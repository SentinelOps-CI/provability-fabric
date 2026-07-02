/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

import type { AuthenticatedRequest } from '../auth.js';
import type { McpContext, McpJwtUser } from '../mcp/types.js';

export interface McpAuthenticatedRequest extends AuthenticatedRequest {
  user?: AuthenticatedRequest['user'] & McpJwtUser;
  sessionId?: string;
  mcpContext?: McpContext;
}
