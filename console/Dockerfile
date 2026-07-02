# syntax=docker/dockerfile:1.7
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

FROM node:20-alpine AS builder

WORKDIR /app
COPY package*.json ./
RUN --mount=type=cache,target=/root/.npm npm install --no-audit --no-fund

COPY . .
RUN DISABLE_ESLINT_PLUGIN=true npm run build

FROM nginx:alpine
COPY --from=builder /app/build /usr/share/nginx/html
COPY nginx.conf /etc/nginx/nginx.conf

EXPOSE 3000

# Use default nginx user; port 3000 is >1024 so non-root would work, but
# some nginx modules expect ownership. Keep default user to avoid breaking.

CMD ["nginx", "-g", "daemon off;"]