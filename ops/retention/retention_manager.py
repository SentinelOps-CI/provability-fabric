#!/usr/bin/env python3
"""
Data Retention Manager for Provability-Fabric.

This script implements OPT-20 data retention and storage cost optimization:
- 7-day hot storage in PostgreSQL
- Weekly roll-ups to object store as Parquet
- BigQuery external table creation
- Safety-case bundle deduplication
- Compression and cost optimization

Usage:
    python retention_manager.py --config <config_file> --action <action>
    python retention_manager.py --hot-to-warm --dry-run
    python retention_manager.py --warm-to-cold --dry-run
    python retention_manager.py --create-bigquery-tables
"""

import argparse
import json
import logging
import os
import sys
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List
import yaml
import psycopg2
import boto3
from google.cloud import bigquery
import pandas as pd
import pyarrow as pa
import pyarrow.parquet as pq
import io

# Configure logging
logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s"
)
logger = logging.getLogger(__name__)


class DataRetentionManager:
    """Manages data retention and storage optimization."""

    def __init__(self, config_file: Path):
        self.config = self._load_config(config_file)
        self.pg_conn = None
        self.s3_client = None
        self.bq_client = None

    def _load_config(self, config_file: Path) -> Dict:
        """Load configuration from YAML file."""
        try:
            with open(config_file, "r") as f:
                config = yaml.safe_load(f)
            logger.info(f"Loaded configuration from {config_file}")
            return config
        except Exception as e:
            logger.error(f"Failed to load configuration: {e}")
            sys.exit(1)

    def connect_postgres(self) -> None:
        """Connect to PostgreSQL database."""
        try:
            db_config = self.config["hot_storage"]
            self.pg_conn = psycopg2.connect(
                host=os.getenv("PG_HOST", "localhost"),
                database=db_config["database"],
                user=os.getenv("PG_USER", "postgres"),
                password=os.getenv("PG_PASSWORD", ""),
                port=os.getenv("PG_PORT", "5432"),
            )
            logger.info("Connected to PostgreSQL")
        except Exception as e:
            logger.error(f"Failed to connect to PostgreSQL: {e}")
            raise

    def connect_s3(self) -> None:
        """Connect to S3 for warm storage."""
        try:
            warm_config = self.config["warm_storage"]
            self.s3_client = boto3.client(
                "s3",
                region_name=warm_config["region"],
                aws_access_key_id=os.getenv("AWS_ACCESS_KEY_ID"),
                aws_secret_access_key=os.getenv("AWS_SECRET_ACCESS_KEY"),
            )
            logger.info("Connected to S3")
        except Exception as e:
            logger.error(f"Failed to connect to S3: {e}")
            raise

    def connect_bigquery(self) -> None:
        """Connect to BigQuery for cold storage."""
        try:
            cold_config = self.config["cold_storage"]
            self.bq_client = bigquery.Client(project=cold_config["project"])
            logger.info("Connected to BigQuery")
        except Exception as e:
            logger.error(f"Failed to connect to BigQuery: {e}")
            raise

    def cleanup_hot_storage(self, dry_run: bool = False) -> Dict:
        """Clean up expired data from hot storage."""
        if not self.pg_conn:
            self.connect_postgres()

        cleanup_results = {
            "tables_processed": [],
            "records_deleted": 0,
            "storage_freed_bytes": 0,
            "errors": [],
        }

        hot_config = self.config["hot_storage"]
        retention_days = hot_config["retention_days"]
        cutoff_date = datetime.now() - timedelta(days=retention_days)

        for table_config in hot_config["tables"]:
            table_name = table_config["name"]
            try:
                # Get table size before cleanup
                with self.pg_conn.cursor() as cursor:
                    cursor.execute("SELECT pg_total_relation_size(%s)", (table_name,))
                    size_before = cursor.fetchone()[0]

                # Delete expired records
                if not dry_run:
                    with self.pg_conn.cursor() as cursor:
                        cursor.execute(
                            f"DELETE FROM {table_name} WHERE created_at < %s",
                            (cutoff_date,),
                        )
                        records_deleted = cursor.rowcount
                        self.pg_conn.commit()
                else:
                    # Dry run - just count records
                    with self.pg_conn.cursor() as cursor:
                        cursor.execute(
                            f"SELECT COUNT(*) FROM {table_name} "
                            f"WHERE created_at < %s",
                            (cutoff_date,),
                        )
                        records_deleted = cursor.fetchone()[0]

                # Get table size after cleanup
                if not dry_run:
                    with self.pg_conn.cursor() as cursor:
                        cursor.execute(
                            "SELECT pg_total_relation_size(%s)", (table_name,)
                        )
                        size_after = cursor.fetchone()[0]
                    storage_freed = size_before - size_after
                else:
                    storage_freed = 0

                cleanup_results["tables_processed"].append(
                    {
                        "table": table_name,
                        "records_deleted": records_deleted,
                        "storage_freed_bytes": storage_freed,
                        "cutoff_date": cutoff_date.isoformat(),
                    }
                )

                cleanup_results["records_deleted"] += records_deleted
                cleanup_results["storage_freed_bytes"] += storage_freed

                logger.info(
                    f"Cleanup {table_name}: {records_deleted} records, "
                    f"{storage_freed} bytes freed"
                )

            except Exception as e:
                error_msg = f"Failed to cleanup {table_name}: {e}"
                logger.error(error_msg)
                cleanup_results["errors"].append(error_msg)

        return cleanup_results

    def rollup_to_warm_storage(self, dry_run: bool = False) -> Dict:
        """Roll up hot storage data to warm storage (Parquet)."""
        if not self.pg_conn:
            self.connect_postgres()
        if not self.s3_client:
            self.connect_s3()

        rollup_results = {
            "tables_processed": [],
            "files_created": 0,
            "total_size_bytes": 0,
            "errors": [],
        }

        warm_config = self.config["warm_storage"]
        bucket = warm_config["bucket"]

        # Get data from last 7 days
        start_date = datetime.now() - timedelta(days=7)

        for table_config in self.config["hot_storage"]["tables"]:
            table_name = table_config["name"]
            try:
                # Query data for rollup
                with self.pg_conn.cursor() as cursor:
                    cursor.execute(
                        f"""
                        SELECT * FROM {table_name} 
                        WHERE created_at >= %s
                        ORDER BY created_at
                        """,
                        (start_date,),
                    )

                    # Convert to pandas DataFrame
                    columns = [desc[0] for desc in cursor.description]
                    data = cursor.fetchall()
                    df = pd.DataFrame(data, columns=columns)

                if df.empty:
                    logger.info(f"No data to rollup for {table_name}")
                    continue

                # Apply deduplication if enabled
                if table_config.get("deduplication", False):
                    df = self._deduplicate_data(df, table_name)

                # Apply compression
                compression_config = self.config["compression"]["tables"].get(
                    table_name, self.config["compression"]
                )

                # Convert to Parquet
                parquet_buffer = self._dataframe_to_parquet(df, compression_config)

                # Generate S3 key
                date_str = start_date.strftime("%Y-%m-%d")
                s3_key = f"{table_name}/{date_str}/{table_name}_{date_str}.parquet"

                if not dry_run:
                    # Upload to S3
                    self.s3_client.put_object(
                        Bucket=bucket,
                        Key=s3_key,
                        Body=parquet_buffer.getvalue(),
                        ContentType="application/octet-stream",
                    )

                    # Get file size
                    file_size = len(parquet_buffer.getvalue())
                else:
                    file_size = len(parquet_buffer.getvalue())

                rollup_results["tables_processed"].append(
                    {
                        "table": table_name,
                        "records": len(df),
                        "file_size_bytes": file_size,
                        "s3_key": s3_key,
                        "compression_ratio": self._calculate_compression_ratio(
                            df, file_size
                        ),
                    }
                )

                rollup_results["files_created"] += 1
                rollup_results["total_size_bytes"] += file_size

                logger.info(
                    f"Rollup {table_name}: {len(df)} records, "
                    f"{file_size} bytes, {s3_key}"
                )

            except Exception as e:
                error_msg = f"Failed to rollup {table_name}: {e}"
                logger.error(error_msg)
                rollup_results["errors"].append(error_msg)

        return rollup_results

    def _deduplicate_data(self, df: pd.DataFrame, table_name: str) -> pd.DataFrame:
        """Deduplicate data based on configuration."""
        dedup_config = self.config["deduplication"]

        for algorithm in dedup_config["algorithms"]:
            if algorithm["name"] == "plan_hash":
                # Deduplicate by plan_hash, policy_hash, tenant_id
                fields = algorithm["fields"]
                if all(field in df.columns for field in fields):
                    df = df.drop_duplicates(subset=fields, keep="first")
                    logger.info(f"Deduplicated {table_name} by {fields}")

            elif algorithm["name"] == "content_hash":
                # Deduplicate by content_hash, metadata_hash
                fields = algorithm["fields"]
                if all(field in df.columns for field in fields):
                    df = df.drop_duplicates(subset=fields, keep="first")
                    logger.info(f"Deduplicated {table_name} by {fields}")

        return df

    def _dataframe_to_parquet(
        self, df: pd.DataFrame, compression_config: Dict
    ) -> io.BytesIO:
        """Convert DataFrame to compressed Parquet format."""
        import io

        # Create Parquet table
        table = pa.Table.from_pandas(df)

        # Write to buffer with compression
        buffer = io.BytesIO()

        if compression_config["algorithm"] == "zstd":
            compression = "zstd"
            compression_level = compression_config.get("level", 6)
        else:
            compression = "snappy"
            compression_level = None

        pq.write_table(
            table, buffer, compression=compression, compression_level=compression_level
        )

        buffer.seek(0)
        return buffer

    def _calculate_compression_ratio(
        self, df: pd.DataFrame, compressed_size: int
    ) -> float:
        """Calculate compression ratio."""
        # Estimate uncompressed size (rough approximation)
        uncompressed_size = len(df) * len(df.columns) * 8  # Assume 8 bytes per field

        if uncompressed_size > 0:
            return compressed_size / uncompressed_size
        return 1.0

    def create_bigquery_tables(self) -> Dict:
        """Create BigQuery external tables for cold storage."""
        if not self.bq_client:
            self.connect_bigquery()

        cold_config = self.config["cold_storage"]

        results = {"tables_created": [], "errors": []}

        for table_config in cold_config["external_tables"]:
            try:
                # Create external table
                table_id = f"{cold_config['project']}.{cold_config['dataset']}.{table_config['name']}"

                external_config = bigquery.ExternalConfig(table_config["format"])
                external_config.source_uris = table_config["source_uris"]

                if table_config.get("compression"):
                    external_config.compression = table_config["compression"]

                # Create table schema (this would need to be defined based on your data)
                schema = self._get_table_schema(table_config["name"])

                table = bigquery.Table(table_id, schema=schema)
                table.external_data_configuration = external_config

                # Create the table
                table = self.bq_client.create_table(table, exists_ok=True)

                results["tables_created"].append(
                    {
                        "table": table_config["name"],
                        "table_id": table_id,
                        "source_uris": table_config["source_uris"],
                    }
                )

                logger.info(f"Created BigQuery table: {table_id}")

            except Exception as e:
                error_msg = (
                    f"Failed to create BigQuery table {table_config['name']}: {e}"
                )
                logger.error(error_msg)
                results["errors"].append(error_msg)

        return results

    def _get_table_schema(self, table_name: str) -> List[bigquery.SchemaField]:
        """Get BigQuery schema for a table."""
        # This would need to be customized based on your actual data schema
        # For now, providing a generic schema

        if "safety_cases" in table_name:
            return [
                bigquery.SchemaField("id", "STRING"),
                bigquery.SchemaField("tenant_id", "STRING"),
                bigquery.SchemaField("plan_hash", "STRING"),
                bigquery.SchemaField("policy_hash", "STRING"),
                bigquery.SchemaField("created_at", "TIMESTAMP"),
                bigquery.SchemaField("content", "STRING"),
                bigquery.SchemaField("metadata", "STRING"),
            ]
        elif "audit_logs" in table_name:
            return [
                bigquery.SchemaField("id", "STRING"),
                bigquery.SchemaField("tenant_id", "STRING"),
                bigquery.SchemaField("timestamp", "TIMESTAMP"),
                bigquery.SchemaField("action", "STRING"),
                bigquery.SchemaField("user_id", "STRING"),
                bigquery.SchemaField("details", "STRING"),
            ]
        elif "metrics" in table_name:
            return [
                bigquery.SchemaField("id", "STRING"),
                bigquery.SchemaField("tenant_id", "STRING"),
                bigquery.SchemaField("timestamp", "TIMESTAMP"),
                bigquery.SchemaField("metric_name", "STRING"),
                bigquery.SchemaField("metric_value", "FLOAT64"),
                bigquery.SchemaField("labels", "STRING"),
            ]
        else:
            # Generic schema
            return [
                bigquery.SchemaField("id", "STRING"),
                bigquery.SchemaField("tenant_id", "STRING"),
                bigquery.SchemaField("created_at", "TIMESTAMP"),
                bigquery.SchemaField("data", "STRING"),
            ]

    def optimize_storage_costs(self) -> Dict:
        """Apply storage cost optimization strategies."""
        if not self.s3_client:
            self.connect_s3()

        cost_config = self.config["cost_optimization"]
        bucket = self.config["warm_storage"]["bucket"]

        results = {
            "lifecycle_policies_applied": [],
            "storage_classes_updated": [],
            "errors": [],
        }

        try:
            # Apply lifecycle policies
            lifecycle_config = {"Rules": []}

            for policy in cost_config["lifecycle"]:
                rule = {
                    "ID": policy["name"],
                    "Status": "Enabled",
                    "Filter": {},
                    "Transitions": [],
                }

                if policy["action"] == "move_to_warm":
                    rule["Transitions"].append(
                        {
                            "Days": policy["days"],
                            "StorageClass": cost_config["storage_classes"]["warm"],
                        }
                    )
                elif policy["action"] == "move_to_cold":
                    rule["Transitions"].append(
                        {
                            "Days": policy["days"],
                            "StorageClass": cost_config["storage_classes"]["cold"],
                        }
                    )

                lifecycle_config["Rules"].append(rule)

            # Apply lifecycle configuration
            self.s3_client.put_bucket_lifecycle_configuration(
                Bucket=bucket, LifecycleConfiguration=lifecycle_config
            )

            results["lifecycle_policies_applied"] = [
                policy["name"] for policy in cost_config["lifecycle"]
            ]

            logger.info("Applied S3 lifecycle policies")

        except Exception as e:
            error_msg = f"Failed to apply lifecycle policies: {e}"
            logger.error(error_msg)
            results["errors"].append(error_msg)

        return results

    def generate_cost_report(self) -> Dict:
        """Generate storage cost analysis report."""
        report = {
            "timestamp": datetime.now().isoformat(),
            "storage_tiers": {},
            "cost_analysis": {},
            "optimization_recommendations": [],
        }

        # Analyze hot storage
        if self.pg_conn:
            try:
                with self.pg_conn.cursor() as cursor:
                    cursor.execute(
                        """
                        SELECT 
                            schemaname,
                            tablename,
                            pg_total_relation_size(schemaname||'.'||tablename) as size_bytes
                        FROM pg_tables 
                        WHERE schemaname = 'public'
                        ORDER BY size_bytes DESC
                    """
                    )

                    hot_storage = {}
                    total_hot_size = 0

                    for row in cursor.fetchall():
                        table_name = row[1]
                        size_bytes = row[2]
                        hot_storage[table_name] = {
                            "size_bytes": size_bytes,
                            "size_mb": round(size_bytes / (1024 * 1024), 2),
                        }
                        total_hot_size += size_bytes

                    report["storage_tiers"]["hot"] = {
                        "total_size_bytes": total_hot_size,
                        "total_size_gb": round(total_hot_size / (1024**3), 2),
                        "tables": hot_storage,
                    }

            except Exception as e:
                logger.error(f"Failed to analyze hot storage: {e}")

        # Analyze warm storage (S3)
        if self.s3_client:
            try:
                bucket = self.config["warm_storage"]["bucket"]
                response = self.s3_client.list_objects_v2(Bucket=bucket)

                warm_storage = {}
                total_warm_size = 0

                for obj in response.get("Contents", []):
                    key = obj["Key"]
                    size = obj["Size"]
                    storage_class = obj.get("StorageClass", "STANDARD")

                    if key not in warm_storage:
                        warm_storage[key] = {
                            "size_bytes": 0,
                            "storage_class": storage_class,
                        }

                    warm_storage[key]["size_bytes"] += size
                    total_warm_size += size

                report["storage_tiers"]["warm"] = {
                    "total_size_bytes": total_warm_size,
                    "total_size_gb": round(total_warm_size / (1024**3), 2),
                    "objects": warm_storage,
                }

            except Exception as e:
                logger.error(f"Failed to analyze warm storage: {e}")

        # Cost analysis
        report["cost_analysis"] = {
            "estimated_monthly_cost": self._estimate_monthly_cost(report),
            "cost_breakdown": self._breakdown_costs(report),
            "savings_potential": self._calculate_savings_potential(report),
        }

        # Optimization recommendations
        report["optimization_recommendations"] = self._generate_recommendations(report)

        return report

    def _estimate_monthly_cost(self, report: Dict) -> float:
        """Estimate monthly storage costs."""
        total_cost = 0

        # Hot storage (PostgreSQL) - rough estimate
        if "hot" in report["storage_tiers"]:
            hot_size_gb = report["storage_tiers"]["hot"]["total_size_gb"]
            # Assume $0.10 per GB per month for PostgreSQL
            total_cost += hot_size_gb * 0.10

        # Warm storage (S3)
        if "warm" in report["storage_tiers"]:
            warm_size_gb = report["storage_tiers"]["warm"]["total_size_gb"]
            # S3 Standard-IA: $0.0125 per GB per month
            total_cost += warm_size_gb * 0.0125

        return round(total_cost, 2)

    def _breakdown_costs(self, report: Dict) -> Dict:
        """Break down costs by storage tier."""
        breakdown = {}

        if "hot" in report["storage_tiers"]:
            hot_size_gb = report["storage_tiers"]["hot"]["total_size_gb"]
            breakdown["hot_storage"] = round(hot_size_gb * 0.10, 2)

        if "warm" in report["storage_tiers"]:
            warm_size_gb = report["storage_tiers"]["warm"]["total_size_gb"]
            breakdown["warm_storage"] = round(warm_size_gb * 0.0125, 2)

        return breakdown

    def _calculate_savings_potential(self, report: Dict) -> Dict:
        """Calculate potential cost savings."""
        savings = {}

        # Moving data from hot to warm storage
        if "hot" in report["storage_tiers"]:
            hot_size_gb = report["storage_tiers"]["hot"]["total_size_gb"]
            # Moving to S3 Standard-IA saves $0.0875 per GB per month
            savings["hot_to_warm"] = round(hot_size_gb * 0.0875, 2)

        # Compression savings
        if "hot" in report["storage_tiers"]:
            hot_size_gb = report["storage_tiers"]["hot"]["total_size_gb"]
            # Assume 60% compression ratio
            compression_savings = hot_size_gb * 0.6 * 0.10
            savings["compression"] = round(compression_savings, 2)

        return savings

    def _generate_recommendations(self, report: Dict) -> List[str]:
        """Generate optimization recommendations."""
        recommendations = []

        # Storage tier optimization
        if "hot" in report["storage_tiers"]:
            hot_size_gb = report["storage_tiers"]["hot"]["total_size_gb"]
            if hot_size_gb > 100:  # If hot storage > 100 GB
                recommendations.append(
                    f"Consider moving {hot_size_gb} GB from hot to warm storage "
                    f"to save ${report['cost_analysis']['savings_potential']['hot_to_warm']}/month"
                )

        # Compression recommendations
        if "hot" in report["storage_tiers"]:
            recommendations.append(
                "Enable zstd compression for hot storage tables to reduce size by 60-80%"
            )

        # Deduplication recommendations
        recommendations.append(
            "Enable deduplication for safety-case bundles using plan_hash and policy_hash"
        )

        # Lifecycle policy recommendations
        recommendations.append(
            "Implement S3 lifecycle policies to automatically move data to cheaper storage tiers"
        )

        return recommendations


def main():
    parser = argparse.ArgumentParser(description="Data Retention Manager")
    parser.add_argument("--config", required=True, help="Configuration file path")
    parser.add_argument(
        "--action",
        choices=[
            "cleanup-hot",
            "rollup-warm",
            "create-bigquery",
            "optimize-costs",
            "cost-report",
            "all",
        ],
        help="Action to perform",
    )
    parser.add_argument("--dry-run", action="store_true", help="Dry run mode")
    parser.add_argument("--output", help="Output file for results")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")

    args = parser.parse_args()

    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    config_file = Path(args.config)
    if not config_file.exists():
        logger.error(f"Configuration file not found: {config_file}")
        sys.exit(1)

    manager = DataRetentionManager(config_file)
    results = {}

    try:
        if args.action in ["cleanup-hot", "all"]:
            logger.info("Cleaning up hot storage...")
            results["hot_cleanup"] = manager.cleanup_hot_storage(args.dry_run)

        if args.action in ["rollup-warm", "all"]:
            logger.info("Rolling up to warm storage...")
            results["warm_rollup"] = manager.rollup_to_warm_storage(args.dry_run)

        if args.action in ["create-bigquery", "all"]:
            logger.info("Creating BigQuery tables...")
            results["bigquery_tables"] = manager.create_bigquery_tables()

        if args.action in ["optimize-costs", "all"]:
            logger.info("Optimizing storage costs...")
            results["cost_optimization"] = manager.optimize_storage_costs()

        if args.action in ["cost-report", "all"]:
            logger.info("Generating cost report...")
            results["cost_report"] = manager.generate_cost_report()

        # Output results
        if args.output:
            with open(args.output, "w") as f:
                json.dump(results, f, indent=2, default=str)
            logger.info(f"Results saved to {args.output}")
        else:
            print(json.dumps(results, indent=2, default=str))

    except Exception as e:
        logger.error(f"Operation failed: {e}")
        sys.exit(1)
    finally:
        if manager.pg_conn:
            manager.pg_conn.close()


if __name__ == "__main__":
    main()
