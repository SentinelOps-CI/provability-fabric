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

// Add response interceptor for better error handling
api.interceptors.response.use(
  (response) => {
    console.log('API Response:', response.config.url, response.status, response.data);
    return response;
  },
  (error) => {
    console.error('API Error:', error.config?.url, error.response?.status, error.response?.data);
    return Promise.reject(error);
  }
);

export const marketplaceAPI = {
  // Get all packages with optional filtering
  getPackages: async (type?: string, author?: string): Promise<PackageListResponse> => {
    try {
      const params = new URLSearchParams();
      if (type) params.append('type', type);
      if (author) params.append('author', author);
      
      console.log('Fetching packages from:', `${API_BASE_URL}/packages?${params.toString()}`);
      const response = await api.get(`/packages?${params.toString()}`);
      console.log('Packages response:', response.data);
      return response.data;
    } catch (error) {
      console.error('Error fetching packages:', error);
      // Return empty response on error
      return { packages: [], total: 0 };
    }
  },

  // Get a specific package
  getPackage: async (id: string): Promise<Package> => {
    try {
      const response = await api.get(`/packages/${id}`);
      return response.data;
    } catch (error) {
      console.error('Error fetching package:', error);
      throw error;
    }
  },

  // Search packages
  searchPackages: async (query: string): Promise<SearchResponse> => {
    try {
      const response = await api.get(`/search?q=${encodeURIComponent(query)}`);
      return response.data;
    } catch (error) {
      console.error('Error searching packages:', error);
      return { query, results: [], total: 0 };
    }
  },

  // Download package
  downloadPackage: async (id: string): Promise<void> => {
    try {
      const response = await api.get(`/packages/${id}/download`, {
        responseType: 'blob'
      });
      
      // Create a download link
      const url = window.URL.createObjectURL(new Blob([response.data]));
      const link = document.createElement('a');
      link.href = url;
      link.setAttribute('download', `${id}.json`);
      document.body.appendChild(link);
      link.click();
      link.remove();
      window.URL.revokeObjectURL(url);
    } catch (error) {
      console.error('Error downloading package:', error);
      throw error;
    }
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