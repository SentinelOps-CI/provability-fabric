import axios from 'axios';
import { Package, InstallRequest, InstallResponse, SearchResponse, PackageListResponse } from '../types';

const API_BASE_URL = process.env.REACT_APP_API_URL || 'http://localhost:8080';

const api = axios.create({
  baseURL: API_BASE_URL,
  headers: {
    'Content-Type': 'application/json',
  },
});

// Add auth token to requests
api.interceptors.request.use((config) => {
  const token = localStorage.getItem('auth_token');
  if (token) {
    config.headers.Authorization = `Bearer ${token}`;
  }
  return config;
});

export const marketplaceAPI = {
  // Get all packages with optional filtering
  getPackages: async (type?: string, author?: string): Promise<PackageListResponse> => {
    const params = new URLSearchParams();
    if (type) params.append('type', type);
    if (author) params.append('author', author);
    
    const response = await api.get(`/packages?${params.toString()}`);
    return response.data;
  },

  // Get a specific package
  getPackage: async (id: string): Promise<Package> => {
    const response = await api.get(`/packages/${id}`);
    return response.data;
  },

  // Search packages
  searchPackages: async (query: string): Promise<SearchResponse> => {
    const response = await api.get(`/search?q=${encodeURIComponent(query)}`);
    return response.data;
  },

  // Install a package
  installPackage: async (request: InstallRequest): Promise<InstallResponse> => {
    const response = await api.post('/install', request);
    return response.data;
  },

  // Get installation status
  getInstallStatus: async (installId: string): Promise<InstallResponse> => {
    const response = await api.get(`/install/${installId}`);
    return response.data;
  },

  // Create a new package
  createPackage: async (pkg: Omit<Package, 'id' | 'created' | 'updated' | 'downloads' | 'rating'>): Promise<Package> => {
    const response = await api.post('/packages', pkg);
    return response.data;
  },

  // Update a package
  updatePackage: async (id: string, pkg: Partial<Package>): Promise<Package> => {
    const response = await api.put(`/packages/${id}`, pkg);
    return response.data;
  },

  // Delete a package
  deletePackage: async (id: string): Promise<void> => {
    await api.delete(`/packages/${id}`);
  },

  // Get package versions
  getPackageVersions: async (id: string): Promise<Package[]> => {
    const response = await api.get(`/packages/${id}/versions`);
    return response.data.versions;
  },

  // Health check
  healthCheck: async (): Promise<{ status: string; timestamp: string; version: string }> => {
    const response = await api.get('/health');
    return response.data;
  },
};

export default marketplaceAPI;