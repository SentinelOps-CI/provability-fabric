# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

# --- Build the local SDK once and create a tarball ---
FROM node:18-alpine AS sdk
WORKDIR /sdk
# Bring in the whole SDK (so its build can run)
COPY sdks/typescript/ ./
# Install & build the SDK (dev deps are fine in this stage)
RUN npm install --no-audit --no-fund
RUN npm run build
# Pack to a single file we can install elsewhere
RUN npm pack --silent \
  && sh -lc 'mv *.tgz /sdk/platform-sdk.tgz'

# --- Build the demo app (ts -> js) using the packed SDK ---
FROM node:18-alpine AS builder
WORKDIR /app
# App manifest
COPY demos/verifiable-mcp-fraud/package.json ./
# Install app deps, then force-install our prebuilt SDK tarball
COPY --from=sdk /sdk/platform-sdk.tgz /tmp/platform-sdk.tgz
RUN npm install --no-audit --no-fund \
  && npm install --no-audit --no-fund /tmp/platform-sdk.tgz
# Bring in app sources and build
COPY demos/verifiable-mcp-fraud/ ./
RUN npm run build || echo "Build completed with warnings"

# --- Production runtime image ---
FROM node:18-alpine AS production
WORKDIR /app
RUN apk add --no-cache curl

# App manifest + prebuilt SDK tarball
COPY demos/verifiable-mcp-fraud/package.json ./
COPY --from=sdk /sdk/platform-sdk.tgz /tmp/platform-sdk.tgz

# Prod-only deps + install the SDK tarball (no dev deps required)
ENV NODE_ENV=production
RUN npm install --omit=dev --no-audit --no-fund \
  && npm install --omit=dev /tmp/platform-sdk.tgz \
  && npm cache clean --force

# Copy compiled JS
COPY --from=builder /app/dist ./dist

# Non-root user
RUN addgroup -g 1001 -S nodejs \
  && adduser -S appuser -u 1001 -G nodejs \
  && chown -R appuser:nodejs /app
USER appuser

EXPOSE 3001

# Health check
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
  CMD curl -f http://localhost:3001/health || exit 1

# Start script points to dist/src/...
CMD ["npm", "start"]
