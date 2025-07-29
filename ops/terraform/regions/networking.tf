# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

# Networking Configuration for Cross-Region DR
# Subnets, Security Groups, and Network ACLs

# Primary Region Subnets
resource "aws_subnet" "public_primary" {
  provider = aws.primary
  count    = 3
  
  vpc_id            = aws_vpc.primary.id
  cidr_block        = "10.0.${count.index + 1}.0/24"
  availability_zone = data.aws_availability_zones.primary.names[count.index]
  
  map_public_ip_on_launch = true
  
  tags = {
    Name = "provability-fabric-public-primary-${count.index + 1}"
    Environment = "production"
  }
}

resource "aws_subnet" "private_primary" {
  provider = aws.primary
  count    = 3
  
  vpc_id            = aws_vpc.primary.id
  cidr_block        = "10.0.${count.index + 10}.0/24"
  availability_zone = data.aws_availability_zones.primary.names[count.index]
  
  tags = {
    Name = "provability-fabric-private-primary-${count.index + 1}"
    Environment = "production"
  }
}

# Secondary Region Subnets
resource "aws_subnet" "public_secondary" {
  provider = aws.secondary
  count    = 3
  
  vpc_id            = aws_vpc.secondary.id
  cidr_block        = "10.1.${count.index + 1}.0/24"
  availability_zone = data.aws_availability_zones.secondary.names[count.index]
  
  map_public_ip_on_launch = true
  
  tags = {
    Name = "provability-fabric-public-secondary-${count.index + 1}"
    Environment = "production"
  }
}

resource "aws_subnet" "private_secondary" {
  provider = aws.secondary
  count    = 3
  
  vpc_id            = aws_vpc.secondary.id
  cidr_block        = "10.1.${count.index + 10}.0/24"
  availability_zone = data.aws_availability_zones.secondary.names[count.index]
  
  tags = {
    Name = "provability-fabric-private-secondary-${count.index + 1}"
    Environment = "production"
  }
}

# Internet Gateways
resource "aws_internet_gateway" "primary" {
  provider = aws.primary
  
  vpc_id = aws_vpc.primary.id
  
  tags = {
    Name = "provability-fabric-primary-igw"
    Environment = "production"
  }
}

resource "aws_internet_gateway" "secondary" {
  provider = aws.secondary
  
  vpc_id = aws_vpc.secondary.id
  
  tags = {
    Name = "provability-fabric-secondary-igw"
    Environment = "production"
  }
}

# NAT Gateways for Private Subnets
resource "aws_eip" "nat_primary" {
  provider = aws.primary
  domain   = "vpc"
  
  tags = {
    Name = "provability-fabric-primary-nat-eip"
    Environment = "production"
  }
}

resource "aws_eip" "nat_secondary" {
  provider = aws.secondary
  domain   = "vpc"
  
  tags = {
    Name = "provability-fabric-secondary-nat-eip"
    Environment = "production"
  }
}

resource "aws_nat_gateway" "primary" {
  provider = aws.primary
  
  allocation_id = aws_eip.nat_primary.id
  subnet_id     = aws_subnet.public_primary[0].id
  
  tags = {
    Name = "provability-fabric-primary-nat"
    Environment = "production"
  }
}

resource "aws_nat_gateway" "secondary" {
  provider = aws.secondary
  
  allocation_id = aws_eip.nat_secondary.id
  subnet_id     = aws_subnet.public_secondary[0].id
  
  tags = {
    Name = "provability-fabric-secondary-nat"
    Environment = "production"
  }
}

# Route Tables
resource "aws_route_table" "public_primary" {
  provider = aws.primary
  
  vpc_id = aws_vpc.primary.id
  
  route {
    cidr_block = "0.0.0.0/0"
    gateway_id = aws_internet_gateway.primary.id
  }
  
  tags = {
    Name = "provability-fabric-public-primary-rt"
    Environment = "production"
  }
}

resource "aws_route_table" "private_primary" {
  provider = aws.primary
  
  vpc_id = aws_vpc.primary.id
  
  route {
    cidr_block     = "0.0.0.0/0"
    nat_gateway_id = aws_nat_gateway.primary.id
  }
  
  tags = {
    Name = "provability-fabric-private-primary-rt"
    Environment = "production"
  }
}

resource "aws_route_table" "public_secondary" {
  provider = aws.secondary
  
  vpc_id = aws_vpc.secondary.id
  
  route {
    cidr_block = "0.0.0.0/0"
    gateway_id = aws_internet_gateway.secondary.id
  }
  
  tags = {
    Name = "provability-fabric-public-secondary-rt"
    Environment = "production"
  }
}

resource "aws_route_table" "private_secondary" {
  provider = aws.secondary
  
  vpc_id = aws_vpc.secondary.id
  
  route {
    cidr_block     = "0.0.0.0/0"
    nat_gateway_id = aws_nat_gateway.secondary.id
  }
  
  tags = {
    Name = "provability-fabric-private-secondary-rt"
    Environment = "production"
  }
}

# Route Table Associations
resource "aws_route_table_association" "public_primary" {
  provider = aws.primary
  count    = 3
  
  subnet_id      = aws_subnet.public_primary[count.index].id
  route_table_id = aws_route_table.public_primary.id
}

resource "aws_route_table_association" "private_primary" {
  provider = aws.primary
  count    = 3
  
  subnet_id      = aws_subnet.private_primary[count.index].id
  route_table_id = aws_route_table.private_primary.id
}

resource "aws_route_table_association" "public_secondary" {
  provider = aws.secondary
  count    = 3
  
  subnet_id      = aws_subnet.public_secondary[count.index].id
  route_table_id = aws_route_table.public_secondary.id
}

resource "aws_route_table_association" "private_secondary" {
  provider = aws.secondary
  count    = 3
  
  subnet_id      = aws_subnet.private_secondary[count.index].id
  route_table_id = aws_route_table.private_secondary.id
}

# Security Groups
resource "aws_security_group" "alb_primary" {
  provider = aws.primary
  
  name        = "provability-fabric-alb-primary"
  description = "Security group for primary ALB"
  vpc_id      = aws_vpc.primary.id
  
  ingress {
    description = "HTTP"
    from_port   = 80
    to_port     = 80
    protocol    = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }
  
  ingress {
    description = "HTTPS"
    from_port   = 443
    to_port     = 443
    protocol    = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }
  
  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
  
  tags = {
    Name = "provability-fabric-alb-primary-sg"
    Environment = "production"
  }
}

resource "aws_security_group" "alb_secondary" {
  provider = aws.secondary
  
  name        = "provability-fabric-alb-secondary"
  description = "Security group for secondary ALB"
  vpc_id      = aws_vpc.secondary.id
  
  ingress {
    description = "HTTP"
    from_port   = 80
    to_port     = 80
    protocol    = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }
  
  ingress {
    description = "HTTPS"
    from_port   = 443
    to_port     = 443
    protocol    = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }
  
  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
  
  tags = {
    Name = "provability-fabric-alb-secondary-sg"
    Environment = "production"
  }
}

resource "aws_security_group" "rds_primary" {
  provider = aws.primary
  
  name        = "provability-fabric-rds-primary"
  description = "Security group for primary RDS"
  vpc_id      = aws_vpc.primary.id
  
  ingress {
    description     = "PostgreSQL from ALB"
    from_port       = 5432
    to_port         = 5432
    protocol        = "tcp"
    security_groups = [aws_security_group.alb_primary.id]
  }
  
  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
  
  tags = {
    Name = "provability-fabric-rds-primary-sg"
    Environment = "production"
  }
}

resource "aws_security_group" "rds_secondary" {
  provider = aws.secondary
  
  name        = "provability-fabric-rds-secondary"
  description = "Security group for secondary RDS"
  vpc_id      = aws_vpc.secondary.id
  
  ingress {
    description     = "PostgreSQL from ALB"
    from_port       = 5432
    to_port         = 5432
    protocol        = "tcp"
    security_groups = [aws_security_group.alb_secondary.id]
  }
  
  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
  
  tags = {
    Name = "provability-fabric-rds-secondary-sg"
    Environment = "production"
  }
}

# DB Subnet Groups
resource "aws_db_subnet_group" "primary" {
  provider = aws.primary
  
  name       = "provability-fabric-primary"
  subnet_ids = aws_subnet.private_primary[*].id
  
  tags = {
    Name = "provability-fabric-primary-db-subnet-group"
    Environment = "production"
  }
}

resource "aws_db_subnet_group" "secondary" {
  provider = aws.secondary
  
  name       = "provability-fabric-secondary"
  subnet_ids = aws_subnet.private_secondary[*].id
  
  tags = {
    Name = "provability-fabric-secondary-db-subnet-group"
    Environment = "production"
  }
}

# Data Sources
data "aws_availability_zones" "primary" {
  provider = aws.primary
  state    = "available"
}

data "aws_availability_zones" "secondary" {
  provider = aws.secondary
  state    = "available"
}