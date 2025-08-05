import React, { useState, useEffect } from 'react';
import { Link } from 'react-router-dom';
import { 
  CubeIcon, 
  ChartBarIcon, 
  Cog6ToothIcon, 
  CurrencyDollarIcon,
  ShieldCheckIcon,
  DocumentTextIcon
} from '@heroicons/react/24/outline';
import { marketplaceAPI } from '../services/api';
import { Package } from '../types';

export const Dashboard: React.FC = () => {
  const [packages, setPackages] = useState<Package[]>([]);
  const [loading, setLoading] = useState(true);
  const [ledgerData, setLedgerData] = useState<any>(null);
  const [stats, setStats] = useState({
    totalPackages: 0,
    totalDownloads: 0,
    averageRating: 0,
    activeTenants: 0,
    totalCapsules: 0,
    totalQuotes: 0
  });

  useEffect(() => {
    loadDashboardData();
  }, []);

  const loadDashboardData = async () => {
    try {
      setLoading(true);
      
      // Load marketplace packages
      const packagesResponse = await marketplaceAPI.getPackages();
      setPackages(packagesResponse.packages || []);
      
      // Load ledger data
      try {
        const ledgerResponse = await fetch('http://localhost:8080/tenant/dev-tenant/capsules');
        if (ledgerResponse.ok) {
          const ledgerData = await ledgerResponse.json();
          setLedgerData(ledgerData);
        } else {
          console.warn('Ledger API not available, using mock data');
          setLedgerData({ capsules: [] });
        }
      } catch (ledgerError) {
        console.warn('Ledger API error, using mock data:', ledgerError);
        setLedgerData({ capsules: [] });
      }
      
      // Calculate stats
      const totalDownloads = (packagesResponse.packages || []).reduce((sum, pkg) => sum + pkg.downloads, 0);
      const averageRating = (packagesResponse.packages || []).length > 0 
        ? (packagesResponse.packages || []).reduce((sum, pkg) => sum + pkg.rating, 0) / (packagesResponse.packages || []).length
        : 0;
      
      setStats({
        totalPackages: (packagesResponse.packages || []).length,
        totalDownloads,
        averageRating: Math.round(averageRating * 10) / 10,
        activeTenants: 1, // Mock data
        totalCapsules: ledgerData?.capsules?.length || 0,
        totalQuotes: 0 // Mock data
      });
      
    } catch (error) {
      console.error('Error loading dashboard data:', error);
      // Set default values on error
      setPackages([]);
      setStats({
        totalPackages: 0,
        totalDownloads: 0,
        averageRating: 0,
        activeTenants: 0,
        totalCapsules: 0,
        totalQuotes: 0
      });
    } finally {
      setLoading(false);
    }
  };

  if (loading) {
    return (
      <div className="flex justify-center items-center h-64">
        <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-primary-600"></div>
      </div>
    );
  }

  return (
    <div className="space-y-8">
      {/* Header */}
      <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
        <div className="flex justify-between items-start">
          <div>
            <h1 className="text-3xl font-bold text-gray-900 mb-2">
              Provability-Fabric Dashboard
            </h1>
            <p className="text-gray-600">
              AI Agent Verification Platform - Marketplace & Ledger Integration
            </p>
          </div>
          <button
            onClick={loadDashboardData}
            disabled={loading}
            className="bg-primary-600 text-white px-4 py-2 rounded-lg text-sm font-medium hover:bg-primary-700 disabled:opacity-50 disabled:cursor-not-allowed"
          >
            {loading ? 'Refreshing...' : 'Refresh Data'}
          </button>
        </div>
      </div>

      {/* Debug Info (Development Only) */}
      {process.env.NODE_ENV === 'development' && (
        <div className="bg-yellow-50 border border-yellow-200 rounded-lg p-4">
          <h3 className="text-lg font-semibold text-yellow-800 mb-2">Debug Information</h3>
          <div className="text-sm text-yellow-700 space-y-1">
            <p>API Base URL: {process.env.REACT_APP_API_URL || 'http://localhost:8080'}</p>
            <p>Packages Loaded: {packages.length}</p>
            <p>Ledger Data: {ledgerData ? 'Available' : 'Not Available'}</p>
            <p>Last Updated: {new Date().toLocaleTimeString()}</p>
          </div>
        </div>
      )}

      {/* Stats Grid */}
      <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6">
        <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
          <div className="flex items-center">
            <CubeIcon className="h-8 w-8 text-blue-600" />
            <div className="ml-4">
              <p className="text-sm font-medium text-gray-600">Total Packages</p>
              <p className="text-2xl font-bold text-gray-900">{stats.totalPackages}</p>
            </div>
          </div>
        </div>

        <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
          <div className="flex items-center">
            <ChartBarIcon className="h-8 w-8 text-green-600" />
            <div className="ml-4">
              <p className="text-sm font-medium text-gray-600">Total Downloads</p>
              <p className="text-2xl font-bold text-gray-900">{stats.totalDownloads.toLocaleString()}</p>
            </div>
          </div>
        </div>

        <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
          <div className="flex items-center">
            <ShieldCheckIcon className="h-8 w-8 text-purple-600" />
            <div className="ml-4">
              <p className="text-sm font-medium text-gray-600">Average Rating</p>
              <p className="text-2xl font-bold text-gray-900">{stats.averageRating}/5.0</p>
            </div>
          </div>
        </div>

        <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
          <div className="flex items-center">
            <Cog6ToothIcon className="h-8 w-8 text-orange-600" />
            <div className="ml-4">
              <p className="text-sm font-medium text-gray-600">Active Tenants</p>
              <p className="text-2xl font-bold text-gray-900">{stats.activeTenants}</p>
            </div>
          </div>
        </div>

        <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
          <div className="flex items-center">
            <DocumentTextIcon className="h-8 w-8 text-indigo-600" />
            <div className="ml-4">
              <p className="text-sm font-medium text-gray-600">Total Capsules</p>
              <p className="text-2xl font-bold text-gray-900">{stats.totalCapsules}</p>
            </div>
          </div>
        </div>

        <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
          <div className="flex items-center">
            <CurrencyDollarIcon className="h-8 w-8 text-yellow-600" />
            <div className="ml-4">
              <p className="text-sm font-medium text-gray-600">Premium Quotes</p>
              <p className="text-2xl font-bold text-gray-900">{stats.totalQuotes}</p>
            </div>
          </div>
        </div>
      </div>

      {/* Recent Packages */}
      <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
        <div className="flex items-center justify-between mb-6">
          <h2 className="text-xl font-semibold text-gray-900">Recent Packages</h2>
          <Link 
            to="/packages" 
            className="text-primary-600 hover:text-primary-700 font-medium"
          >
            View All →
          </Link>
        </div>
        
        <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
          {packages.slice(0, 3).map((pkg) => (
            <div key={pkg.id} className="border border-gray-200 rounded-lg p-4 hover:shadow-md transition-shadow">
              <div className="flex items-start justify-between mb-2">
                <h3 className="font-semibold text-gray-900">
                  <Link to={`/package/${pkg.id}`} className="hover:text-primary-600">
                    {pkg.name}
                  </Link>
                </h3>
                <span className={`px-2 py-1 rounded-full text-xs font-medium ${
                  pkg.type === 'adapter' ? 'bg-blue-100 text-blue-800' :
                  pkg.type === 'spec' ? 'bg-green-100 text-green-800' :
                  'bg-purple-100 text-purple-800'
                }`}>
                  {pkg.type}
                </span>
              </div>
              <p className="text-sm text-gray-600 mb-2 line-clamp-2">{pkg.description}</p>
              <div className="flex items-center justify-between text-sm text-gray-500">
                <span>{pkg.author}</span>
                <span>{pkg.downloads} downloads</span>
              </div>
            </div>
          ))}
        </div>
      </div>

      {/* Ledger Data */}
      {ledgerData && (
        <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
          <h2 className="text-xl font-semibold text-gray-900 mb-6">Recent Capsules</h2>
          
          {ledgerData.capsules && ledgerData.capsules.length > 0 ? (
            <div className="space-y-4">
              {ledgerData.capsules.map((capsule: any) => (
                <div key={capsule.id} className="border border-gray-200 rounded-lg p-4">
                  <div className="flex items-center justify-between">
                    <div>
                      <h3 className="font-semibold text-gray-900">Capsule {capsule.hash}</h3>
                      <p className="text-sm text-gray-600">Risk Score: {capsule.riskScore}</p>
                      <p className="text-sm text-gray-500">Created: {new Date(capsule.createdAt).toLocaleDateString()}</p>
                    </div>
                    <div className="text-right">
                      <span className="inline-flex items-center px-2.5 py-0.5 rounded-full text-xs font-medium bg-green-100 text-green-800">
                        Active
                      </span>
                    </div>
                  </div>
                </div>
              ))}
            </div>
          ) : (
            <p className="text-gray-500 text-center py-8">No capsules found</p>
          )}
        </div>
      )}

      {/* Quick Actions */}
      <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
        <h2 className="text-xl font-semibold text-gray-900 mb-6">Quick Actions</h2>
        
        <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-4 gap-4">
          <Link 
            to="/packages" 
            className="flex items-center p-4 border border-gray-200 rounded-lg hover:shadow-md transition-shadow"
          >
            <CubeIcon className="h-6 w-6 text-blue-600 mr-3" />
            <span className="font-medium text-gray-900">Browse Packages</span>
          </Link>
          
          <Link 
            to="/search" 
            className="flex items-center p-4 border border-gray-200 rounded-lg hover:shadow-md transition-shadow"
          >
            <ChartBarIcon className="h-6 w-6 text-green-600 mr-3" />
            <span className="font-medium text-gray-900">Search</span>
          </Link>
          
          <button 
            onClick={() => {
              // Try to connect to GraphQL API, show alert if not available
              fetch('http://localhost:4000/graphql', {
                method: 'POST',
                headers: {
                  'Content-Type': 'application/json',
                },
                body: JSON.stringify({ query: '{ __typename }' })
              })
              .then(response => {
                if (response.ok) {
                  window.open('http://localhost:4000/graphql', '_blank');
                } else {
                  alert('GraphQL API is not available. The ledger service needs to be started.');
                }
              })
              .catch(() => {
                alert('GraphQL API is not available. The ledger service needs to be started.');
              });
            }}
            className="flex items-center p-4 border border-gray-200 rounded-lg hover:shadow-md transition-shadow"
          >
            <Cog6ToothIcon className="h-6 w-6 text-orange-600 mr-3" />
            <span className="font-medium text-gray-900">GraphQL API</span>
          </button>
          
          <button 
            onClick={() => {
              // Try to connect to health endpoint, show alert if not available
              fetch('http://localhost:8080/health')
              .then(response => {
                if (response.ok) {
                  window.open('http://localhost:8080/health', '_blank');
                } else {
                  alert('Health Check endpoint is not available.');
                }
              })
              .catch(() => {
                alert('Health Check endpoint is not available.');
              });
            }}
            className="flex items-center p-4 border border-gray-200 rounded-lg hover:shadow-md transition-shadow"
          >
            <ShieldCheckIcon className="h-6 w-6 text-purple-600 mr-3" />
            <span className="font-medium text-gray-900">Health Check</span>
          </button>
        </div>
      </div>
    </div>
  );
}; 