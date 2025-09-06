export type Compatibility = {
  /** Required fabric compatibility */
  'fabric-version': string;
  /** Optional adapter/spec tags used by marketplace filters/search */
  adapters?: string[];
  specs?: string[];
  /** Future-safe: allow extra keys as string or string[] */
  [key: string]: string | string[] | undefined;
};

export interface File {
  path: string;
  hash: string;
  size?: number;
}

export interface Package {
  id: string;
  name: string;
  version: string;
  type: 'adapter' | 'spec' | 'proofpack' | string;
  compatibility: Compatibility;
  description: string;
  author: string;
  license: string;
  repository?: string;
  homepage?: string;
  keywords?: string[];
  files?: File[];
  metadata?: Record<string, any>;
  created: string;
  updated: string;
  downloads: number;
  rating: number;
}

export interface InstallRequest {
  tenantId: string;
  packageId: string;
  version: string;
}

export interface InstallResponse {
  installId: string;
  status: 'pending' | 'completed' | 'failed';
  message: string;
  timestamp?: string;
}

export interface SearchResponse {
  query: string;
  results: Package[];
  total: number;
}

export interface PackageListResponse {
  packages: Package[];
  total: number;
}

/** Auth user shape for UI; token is optional for local/dev flows */
export interface User {
  id: string;
  name: string;
  email?: string;
  token?: string;
  [key: string]: unknown;
}