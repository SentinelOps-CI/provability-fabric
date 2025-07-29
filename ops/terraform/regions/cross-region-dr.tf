# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

# Cross-Region Disaster Recovery Configuration
# Provides zero-downtime upgrades and automatic failover

terraform {
  required_version = ">= 1.0"
  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 5.0"
    }
  }
}

# Primary Region (us-west-2)
provider "aws" {
  region = "us-west-2"
  alias  = "primary"
}

# Secondary Region (us-east-1) 
provider "aws" {
  region = "us-east-1"
  alias  = "secondary"
}

# VPC Configuration for Primary Region
resource "aws_vpc" "primary" {
  provider = aws.primary
  
  cidr_block           = "10.0.0.0/16"
  enable_dns_hostnames = true
  enable_dns_support   = true

  tags = {
    Name = "provability-fabric-primary"
    Environment = "production"
  }
}

# VPC Configuration for Secondary Region
resource "aws_vpc" "secondary" {
  provider = aws.secondary
  
  cidr_block           = "10.1.0.0/16"
  enable_dns_hostnames = true
  enable_dns_support   = true

  tags = {
    Name = "provability-fabric-secondary"
    Environment = "production"
  }
}

# RDS Primary Instance (us-west-2)
resource "aws_db_instance" "primary" {
  provider = aws.primary
  
  identifier = "provability-fabric-primary"
  
  engine         = "postgres"
  engine_version = "15.4"
  instance_class = "db.t3.micro"
  
  allocated_storage     = 20
  max_allocated_storage = 100
  storage_type         = "gp2"
  storage_encrypted    = true
  
  db_name  = "provability_fabric"
  username = "pf_admin"
  password = var.db_password
  
  vpc_security_group_ids = [aws_security_group.rds_primary.id]
  db_subnet_group_name   = aws_db_subnet_group.primary.name
  
  backup_retention_period = 7
  backup_window          = "03:00-04:00"
  maintenance_window     = "sun:04:00-sun:05:00"
  
  deletion_protection = true
  
  tags = {
    Name = "provability-fabric-primary-db"
    Environment = "production"
  }
}

# RDS Read Replica (us-east-1)
resource "aws_db_instance" "secondary" {
  provider = aws.secondary
  
  identifier = "provability-fabric-secondary"
  
  replicate_source_db = aws_db_instance.primary.arn
  
  engine         = "postgres"
  engine_version = "15.4"
  instance_class = "db.t3.micro"
  
  allocated_storage     = 20
  max_allocated_storage = 100
  storage_type         = "gp2"
  storage_encrypted    = true
  
  vpc_security_group_ids = [aws_security_group.rds_secondary.id]
  db_subnet_group_name   = aws_db_subnet_group.secondary.name
  
  backup_retention_period = 0  # Replicas don't need backups
  skip_final_snapshot    = true
  
  deletion_protection = false
  
  tags = {
    Name = "provability-fabric-secondary-db"
    Environment = "production"
  }
}

# Application Load Balancer - Primary
resource "aws_lb" "primary" {
  provider = aws.primary
  
  name               = "provability-fabric-primary-alb"
  internal           = false
  load_balancer_type = "application"
  security_groups    = [aws_security_group.alb_primary.id]
  subnets            = aws_subnet.public_primary[*].id

  enable_deletion_protection = true

  tags = {
    Name = "provability-fabric-primary-alb"
    Environment = "production"
  }
}

# Application Load Balancer - Secondary
resource "aws_lb" "secondary" {
  provider = aws.secondary
  
  name               = "provability-fabric-secondary-alb"
  internal           = false
  load_balancer_type = "application"
  security_groups    = [aws_security_group.alb_secondary.id]
  subnets            = aws_subnet.public_secondary[*].id

  enable_deletion_protection = true

  tags = {
    Name = "provability-fabric-secondary-alb"
    Environment = "production"
  }
}

# Route 53 Health Check - Primary
resource "aws_route53_health_check" "primary" {
  fqdn              = aws_lb.primary.dns_name
  port              = 80
  type              = "HTTP"
  resource_path     = "/health"
  failure_threshold = "3"
  request_interval  = "30"

  tags = {
    Name = "provability-fabric-primary-health"
  }
}

# Route 53 Health Check - Secondary
resource "aws_route53_health_check" "secondary" {
  fqdn              = aws_lb.secondary.dns_name
  port              = 80
  type              = "HTTP"
  resource_path     = "/health"
  failure_threshold = "3"
  request_interval  = "30"

  tags = {
    Name = "provability-fabric-secondary-health"
  }
}

# Route 53 Failover Records
resource "aws_route53_record" "primary" {
  zone_id = var.route53_zone_id
  name    = "api.provability-fabric.org"
  type    = "A"

  alias {
    name                   = aws_lb.primary.dns_name
    zone_id                = aws_lb.primary.zone_id
    evaluate_target_health = true
  }

  set_identifier = "primary"
  health_check_id = aws_route53_health_check.primary.id
  failover_routing_policy {
    type = "PRIMARY"
  }
}

resource "aws_route53_record" "secondary" {
  zone_id = var.route53_zone_id
  name    = "api.provability-fabric.org"
  type    = "A"

  alias {
    name                   = aws_lb.secondary.dns_name
    zone_id                = aws_lb.secondary.zone_id
    evaluate_target_health = true
  }

  set_identifier = "secondary"
  health_check_id = aws_route53_health_check.secondary.id
  failover_routing_policy {
    type = "SECONDARY"
  }
}

# S3 Bucket for Artifacts - Primary
resource "aws_s3_bucket" "artifacts_primary" {
  provider = aws.primary
  
  bucket = "provability-fabric-artifacts-us-west-2"

  tags = {
    Name = "provability-fabric-artifacts-primary"
    Environment = "production"
  }
}

# S3 Bucket for Artifacts - Secondary
resource "aws_s3_bucket" "artifacts_secondary" {
  provider = aws.secondary
  
  bucket = "provability-fabric-artifacts-us-east-1"

  tags = {
    Name = "provability-fabric-artifacts-secondary"
    Environment = "production"
  }
}

# S3 Cross-Region Replication
resource "aws_s3_bucket_replication_configuration" "primary" {
  provider = aws.primary
  
  depends_on = [aws_s3_bucket_versioning.primary]
  
  role   = aws_iam_role.replication.arn
  bucket = aws_s3_bucket.artifacts_primary.id

  rule {
    id     = "cross-region-replication"
    status = "Enabled"

    destination {
      bucket        = aws_s3_bucket.artifacts_secondary.arn
      storage_class = "STANDARD"
    }
  }
}

# S3 Versioning for Replication
resource "aws_s3_bucket_versioning" "primary" {
  provider = aws.primary
  
  bucket = aws_s3_bucket.artifacts_primary.id
  versioning_configuration {
    status = "Enabled"
  }
}

resource "aws_s3_bucket_versioning" "secondary" {
  provider = aws.secondary
  
  bucket = aws_s3_bucket.artifacts_secondary.id
  versioning_configuration {
    status = "Enabled"
  }
}

# IAM Role for S3 Replication
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

# IAM Policy for S3 Replication
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
        Resource = aws_s3_bucket.artifacts_primary.arn
      },
      {
        Effect = "Allow"
        Action = [
          "s3:GetObjectVersion",
          "s3:GetObjectVersionAcl"
        ]
        Resource = "${aws_s3_bucket.artifacts_primary.arn}/*"
      },
      {
        Effect = "Allow"
        Action = [
          "s3:ReplicateObject",
          "s3:ReplicateDelete"
        ]
        Resource = "${aws_s3_bucket.artifacts_secondary.arn}/*"
      }
    ]
  })
}

resource "aws_iam_role_policy_attachment" "replication" {
  provider = aws.primary
  
  role       = aws_iam_role.replication.name
  policy_arn = aws_iam_policy.replication.arn
}

# Variables
variable "db_password" {
  description = "Database password"
  type        = string
  sensitive   = true
}

variable "route53_zone_id" {
  description = "Route 53 hosted zone ID"
  type        = string
}

# Outputs
output "primary_db_endpoint" {
  description = "Primary RDS endpoint"
  value       = aws_db_instance.primary.endpoint
}

output "secondary_db_endpoint" {
  description = "Secondary RDS endpoint"
  value       = aws_db_instance.secondary.endpoint
}

output "primary_alb_dns" {
  description = "Primary ALB DNS name"
  value       = aws_lb.primary.dns_name
}

output "secondary_alb_dns" {
  description = "Secondary ALB DNS name"
  value       = aws_lb.secondary.dns_name
}

output "api_domain" {
  description = "API domain with failover"
  value       = "api.provability-fabric.org"
}