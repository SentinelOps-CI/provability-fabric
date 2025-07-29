# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

terraform {
  required_version = ">= 1.0"
  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 5.0"
    }
  }
}

# Provider configuration for primary region (us-west-2)
provider "aws" {
  region = "us-west-2"
  alias  = "primary"
}

# Provider configuration for secondary region (us-east-1)
provider "aws" {
  region = "us-east-1"
  alias  = "secondary"
}

# VPC for primary region
resource "aws_vpc" "primary" {
  provider = aws.primary
  cidr_block = "10.0.0.0/16"
  
  tags = {
    Name = "provability-fabric-primary-vpc"
    Environment = "production"
  }
}

# VPC for secondary region
resource "aws_vpc" "secondary" {
  provider = aws.secondary
  cidr_block = "10.1.0.0/16"
  
  tags = {
    Name = "provability-fabric-secondary-vpc"
    Environment = "production"
  }
}

# Subnets for primary region
resource "aws_subnet" "primary_private" {
  provider = aws.primary
  count = 2
  vpc_id = aws_vpc.primary.id
  cidr_block = "10.0.${count.index + 1}.0/24"
  availability_zone = data.aws_availability_zones.primary.names[count.index]
  
  tags = {
    Name = "provability-fabric-primary-private-${count.index + 1}"
  }
}

# Subnets for secondary region
resource "aws_subnet" "secondary_private" {
  provider = aws.secondary
  count = 2
  vpc_id = aws_vpc.secondary.id
  cidr_block = "10.1.${count.index + 1}.0/24"
  availability_zone = data.aws_availability_zones.secondary.names[count.index]
  
  tags = {
    Name = "provability-fabric-secondary-private-${count.index + 1}"
  }
}

# Data sources for availability zones
data "aws_availability_zones" "primary" {
  provider = aws.primary
  state = "available"
}

data "aws_availability_zones" "secondary" {
  provider = aws.secondary
  state = "available"
}

# Security group for RDS
resource "aws_security_group" "rds_primary" {
  provider = aws.primary
  name_prefix = "provability-fabric-rds-primary"
  vpc_id = aws_vpc.primary.id
  
  ingress {
    from_port = 5432
    to_port = 5432
    protocol = "tcp"
    cidr_blocks = ["10.0.0.0/16"]
  }
  
  egress {
    from_port = 0
    to_port = 0
    protocol = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
  
  tags = {
    Name = "provability-fabric-rds-primary-sg"
  }
}

resource "aws_security_group" "rds_secondary" {
  provider = aws.secondary
  name_prefix = "provability-fabric-rds-secondary"
  vpc_id = aws_vpc.secondary.id
  
  ingress {
    from_port = 5432
    to_port = 5432
    protocol = "tcp"
    cidr_blocks = ["10.1.0.0/16"]
  }
  
  egress {
    from_port = 0
    to_port = 0
    protocol = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
  
  tags = {
    Name = "provability-fabric-rds-secondary-sg"
  }
}

# Subnet groups for RDS
resource "aws_db_subnet_group" "primary" {
  provider = aws.primary
  name = "provability-fabric-primary-subnet-group"
  subnet_ids = aws_subnet.primary_private[*].id
  
  tags = {
    Name = "provability-fabric-primary-subnet-group"
  }
}

resource "aws_db_subnet_group" "secondary" {
  provider = aws.secondary
  name = "provability-fabric-secondary-subnet-group"
  subnet_ids = aws_subnet.secondary_private[*].id
  
  tags = {
    Name = "provability-fabric-secondary-subnet-group"
  }
}

# Parameter group for PostgreSQL
resource "aws_db_parameter_group" "primary" {
  provider = aws.primary
  family = "postgres15"
  name = "provability-fabric-primary-params"
  
  parameter {
    name = "rds.force_ssl"
    value = "1"
  }
  
  parameter {
    name = "log_statement"
    value = "all"
  }
  
  parameter {
    name = "log_min_duration_statement"
    value = "1000"
  }
}

# Primary RDS instance in us-west-2
resource "aws_db_instance" "primary" {
  provider = aws.primary
  identifier = "provability-fabric-primary"
  engine = "postgres"
  engine_version = "15.4"
  instance_class = "db.t3.micro"
  allocated_storage = 20
  max_allocated_storage = 100
  storage_type = "gp2"
  storage_encrypted = true
  
  db_name = "provability_fabric"
  username = "pf_admin"
  password = var.db_password
  
  vpc_security_group_ids = [aws_security_group.rds_primary.id]
  db_subnet_group_name = aws_db_subnet_group.primary.name
  parameter_group_name = aws_db_parameter_group.primary.name
  
  backup_retention_period = 7
  backup_window = "03:00-04:00"
  maintenance_window = "sun:04:00-sun:05:00"
  
  deletion_protection = true
  skip_final_snapshot = false
  final_snapshot_identifier = "provability-fabric-primary-final"
  
  tags = {
    Name = "provability-fabric-primary"
    Environment = "production"
  }
}

# Read replica in us-east-1
resource "aws_db_instance" "secondary" {
  provider = aws.secondary
  identifier = "provability-fabric-secondary"
  engine = "postgres"
  engine_version = "15.4"
  instance_class = "db.t3.micro"
  allocated_storage = 20
  max_allocated_storage = 100
  storage_type = "gp2"
  storage_encrypted = true
  
  replicate_source_db = aws_db_instance.primary.arn
  
  vpc_security_group_ids = [aws_security_group.rds_secondary.id]
  db_subnet_group_name = aws_db_subnet_group.secondary.name
  
  backup_retention_period = 7
  backup_window = "03:00-04:00"
  maintenance_window = "sun:04:00-sun:05:00"
  
  deletion_protection = true
  skip_final_snapshot = false
  final_snapshot_identifier = "provability-fabric-secondary-final"
  
  tags = {
    Name = "provability-fabric-secondary"
    Environment = "production"
  }
}

# S3 bucket for database dumps in primary region
resource "aws_s3_bucket" "dumps_primary" {
  provider = aws.primary
  bucket = "provability-fabric-dumps-${random_string.bucket_suffix.result}"
  
  tags = {
    Name = "provability-fabric-dumps-primary"
    Environment = "production"
  }
}

# S3 bucket for database dumps in secondary region
resource "aws_s3_bucket" "dumps_secondary" {
  provider = aws.secondary
  bucket = "provability-fabric-dumps-${random_string.bucket_suffix.result}-secondary"
  
  tags = {
    Name = "provability-fabric-dumps-secondary"
    Environment = "production"
  }
}

# Random string for unique bucket names
resource "random_string" "bucket_suffix" {
  length = 8
  special = false
  upper = false
}

# S3 bucket versioning
resource "aws_s3_bucket_versioning" "dumps_primary" {
  provider = aws.primary
  bucket = aws_s3_bucket.dumps_primary.id
  versioning_configuration {
    status = "Enabled"
  }
}

resource "aws_s3_bucket_versioning" "dumps_secondary" {
  provider = aws.secondary
  bucket = aws_s3_bucket.dumps_secondary.id
  versioning_configuration {
    status = "Enabled"
  }
}

# S3 bucket encryption
resource "aws_s3_bucket_server_side_encryption_configuration" "dumps_primary" {
  provider = aws.primary
  bucket = aws_s3_bucket.dumps_primary.id
  
  rule {
    apply_server_side_encryption_by_default {
      sse_algorithm = "AES256"
    }
  }
}

resource "aws_s3_bucket_server_side_encryption_configuration" "dumps_secondary" {
  provider = aws.secondary
  bucket = aws_s3_bucket.dumps_secondary.id
  
  rule {
    apply_server_side_encryption_by_default {
      sse_algorithm = "AES256"
    }
  }
}

# S3 replication configuration
resource "aws_s3_bucket_replication_configuration" "dumps_primary" {
  provider = aws.primary
  bucket = aws_s3_bucket.dumps_primary.id
  role = aws_iam_role.replication.arn
  
  rule {
    id = "cross-region-replication"
    status = "Enabled"
    
    destination {
      bucket = aws_s3_bucket.dumps_secondary.arn
      storage_class = "STANDARD"
    }
  }
}

# IAM role for S3 replication
resource "aws_iam_role" "replication" {
  provider = aws.primary
  name = "provability-fabric-s3-replication-role"
  
  assume_role_policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Action = "sts:AssumeRole"
        Effect = "Allow"
        Principal = {
          Service = "s3.amazonaws.com"
        }
      }
    ]
  })
}

# IAM policy for S3 replication
resource "aws_iam_policy" "replication" {
  provider = aws.primary
  name = "provability-fabric-s3-replication-policy"
  
  policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Effect = "Allow"
        Action = [
          "s3:GetReplicationConfiguration",
          "s3:ListBucket"
        ]
        Resource = aws_s3_bucket.dumps_primary.arn
      },
      {
        Effect = "Allow"
        Action = [
          "s3:GetObjectVersion",
          "s3:GetObjectVersionAcl"
        ]
        Resource = "${aws_s3_bucket.dumps_primary.arn}/*"
      },
      {
        Effect = "Allow"
        Action = [
          "s3:ReplicateObject",
          "s3:ReplicateDelete"
        ]
        Resource = "${aws_s3_bucket.dumps_secondary.arn}/*"
      }
    ]
  })
}

# Attach policy to role
resource "aws_iam_role_policy_attachment" "replication" {
  provider = aws.primary
  role = aws_iam_role.replication.name
  policy_arn = aws_iam_policy.replication.arn
}

# Route 53 hosted zone
resource "aws_route53_zone" "main" {
  name = "provability-fabric.org"
  
  tags = {
    Name = "provability-fabric-zone"
    Environment = "production"
  }
}

# Health check for primary region
resource "aws_route53_health_check" "primary" {
  fqdn = aws_db_instance.primary.endpoint
  port = 5432
  type = "TCP"
  request_interval = 30
  failure_threshold = 3
  
  tags = {
    Name = "provability-fabric-primary-health-check"
  }
}

# Health check for secondary region
resource "aws_route53_health_check" "secondary" {
  fqdn = aws_db_instance.secondary.endpoint
  port = 5432
  type = "TCP"
  request_interval = 30
  failure_threshold = 3
  
  tags = {
    Name = "provability-fabric-secondary-health-check"
  }
}

# Route 53 fail-over records
resource "aws_route53_record" "primary" {
  zone_id = aws_route53_zone.main.zone_id
  name = "db.${aws_route53_zone.main.name}"
  type = "CNAME"
  ttl = 60
  records = [aws_db_instance.primary.endpoint]
  
  failover_routing_policy {
    type = "PRIMARY"
  }
  
  health_check_id = aws_route53_health_check.primary.id
  set_identifier = "primary"
}

resource "aws_route53_record" "secondary" {
  zone_id = aws_route53_zone.main.zone_id
  name = "db.${aws_route53_zone.main.name}"
  type = "CNAME"
  ttl = 60
  records = [aws_db_instance.secondary.endpoint]
  
  failover_routing_policy {
    type = "SECONDARY"
  }
  
  health_check_id = aws_route53_health_check.secondary.id
  set_identifier = "secondary"
}

# Variables
variable "db_password" {
  description = "Password for the database admin user"
  type = string
  sensitive = true
}

# Outputs
output "primary_db_endpoint" {
  description = "Primary database endpoint"
  value = aws_db_instance.primary.endpoint
}

output "secondary_db_endpoint" {
  description = "Secondary database endpoint"
  value = aws_db_instance.secondary.endpoint
}

output "dns_name" {
  description = "DNS name for database access"
  value = "db.${aws_route53_zone.main.name}"
}

output "primary_s3_bucket" {
  description = "Primary S3 bucket for dumps"
  value = aws_s3_bucket.dumps_primary.bucket
}

output "secondary_s3_bucket" {
  description = "Secondary S3 bucket for dumps"
  value = aws_s3_bucket.dumps_secondary.bucket
}