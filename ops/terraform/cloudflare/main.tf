# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

terraform {
  required_version = ">= 1.0"
  required_providers {
    cloudflare = {
      source  = "cloudflare/cloudflare"
      version = "~> 4.0"
    }
  }
}

# Provider configuration
provider "cloudflare" {
  api_token = var.cloudflare_api_token
}

# Cloudflare Workers for edge caching
resource "cloudflare_worker_script" "edge_api" {
  name    = "provability-fabric-edge-api"
  content = file("${path.module}/worker.js")
  
  # Deploy to multiple regions
  compatibility_date = "2024-01-27"
  compatibility_flags = ["nodejs_compat"]
}

# Worker routes for different regions
resource "cloudflare_worker_route" "us_west" {
  zone_id     = data.cloudflare_zone.provability_fabric.id
  pattern     = "api.us-west.provability-fabric.org/*"
  script_name = cloudflare_worker_script.edge_api.name
}

resource "cloudflare_worker_route" "us_east" {
  zone_id     = data.cloudflare_zone.provability_fabric.id
  pattern     = "api.us-east.provability-fabric.org/*"
  script_name = cloudflare_worker_script.edge_api.name
}

resource "cloudflare_worker_route" "eu_west" {
  zone_id     = data.cloudflare_zone.provability_fabric.id
  pattern     = "api.eu-west.provability-fabric.org/*"
  script_name = cloudflare_worker_script.edge_api.name
}

# Cloudflare KV namespace for caching
resource "cloudflare_workers_kv_namespace" "cache" {
  title = "provability-fabric-cache"
}

# KV bindings for the worker
resource "cloudflare_worker_script" "edge_api_with_kv" {
  name    = "provability-fabric-edge-api-kv"
  content = file("${path.module}/worker.js")
  
  compatibility_date = "2024-01-27"
  compatibility_flags = ["nodejs_compat"]
  
  kv_namespace_binding {
    name         = "CACHE"
    namespace_id = cloudflare_workers_kv_namespace.cache.id
  }
}

# Environment variables for the worker
resource "cloudflare_worker_script" "edge_api_with_env" {
  name    = "provability-fabric-edge-api-env"
  content = file("${path.module}/worker.js")
  
  compatibility_date = "2024-01-27"
  compatibility_flags = ["nodejs_compat"]
  
  kv_namespace_binding {
    name         = "CACHE"
    namespace_id = cloudflare_workers_kv_namespace.cache.id
  }
  
  secret {
    name  = "LEDGER_URL"
    value = var.ledger_url
  }
  
  secret {
    name  = "CACHE_TTL"
    value = "300" # 5 seconds
  }
}

# Data source for the zone
data "cloudflare_zone" "provability_fabric" {
  name = "provability-fabric.org"
}

# Variables
variable "cloudflare_api_token" {
  description = "Cloudflare API token"
  type        = string
  sensitive   = true
}

variable "ledger_url" {
  description = "URL of the ledger service"
  type        = string
  default     = "https://ledger.provability-fabric.org"
}

# Outputs
output "worker_urls" {
  description = "URLs for the edge API workers"
  value = {
    us_west = "https://api.us-west.provability-fabric.org"
    us_east = "https://api.us-east.provability-fabric.org"
    eu_west = "https://api.eu-west.provability-fabric.org"
  }
}

output "kv_namespace_id" {
  description = "ID of the KV namespace for caching"
  value       = cloudflare_workers_kv_namespace.cache.id
}