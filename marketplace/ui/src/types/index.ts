export interface Package {
  id: string;
  name: string;
  version: string;
  type: 'adapter' | 'spec' | 'proofpack';
  compatibility: {
    'fabric-version': string;
    adapters?: string[];
    specs?: string[];
  };
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

export interface File {
  path: string;
  hash: string;
  size?: number;
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