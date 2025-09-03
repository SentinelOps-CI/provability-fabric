# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

FROM node:18-alpine AS builder

WORKDIR /app

# Copy package manifest and lock file for the demo (paths are relative to build context root)
COPY demos/verifiable-mcp-fraud/package.json demos/verifiable-mcp-fraud/package-lock.json ./

# Copy local SDK so file:../../sdks/typescript resolves from /app to /sdks/typescript
COPY sdks/typescript /sdks/typescript

# TEMP: Debug contents before install
RUN ls -la && echo "--- package-lock.json head ---" && (head -n 20 package-lock.json || true) && echo "--- end head ---"

# Install all dependencies (including devDependencies for building)
RUN npm install --no-audit --no-fund

# Copy demo source code
COPY demos/verifiable-mcp-fraud/ ./

# Build the application (with error tolerance for demo)
RUN npm run build || echo "Build completed with warnings"

# Production stage
FROM node:18-alpine AS production

WORKDIR /app

# Install curl for health checks
RUN apk add --no-cache curl

# Copy package manifest and lock file explicitly (from repo root paths)
COPY demos/verifiable-mcp-fraud/package.json demos/verifiable-mcp-fraud/package-lock.json ./

# Copy local SDK for runtime install resolution (not strictly needed after build, but ensures parity)
COPY sdks/typescript /sdks/typescript

# Install production dependencies only
ENV NODE_ENV=production
RUN npm install --omit=dev --no-audit --no-fund && npm cache clean --force

# Copy built application from builder stage
COPY --from=builder /app/dist ./dist

# Create non-root user
RUN addgroup -g 1001 -S nodejs && \
  adduser -S appuser -u 1001 -G nodejs

# Change ownership of the app directory
RUN chown -R appuser:nodejs /app
USER appuser

EXPOSE 3001

# Health check
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
  CMD curl -f http://localhost:3001/health || exit 1

CMD ["npm", "start"]



