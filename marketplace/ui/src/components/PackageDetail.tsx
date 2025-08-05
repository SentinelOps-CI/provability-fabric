import React, { useState, useEffect } from 'react';
import { useParams, Link } from 'react-router-dom';
import { 
  StarIcon, 
  ArrowDownTrayIcon, 
  CalendarIcon, 
  UserIcon, 
  CodeBracketIcon,
  GlobeAltIcon,
  TagIcon,
  CloudArrowDownIcon
} from '@heroicons/react/24/outline';
import { marketplaceAPI } from '../services/api';
import { Package } from '../types';
import semver from 'semver';

export const PackageDetail: React.FC = () => {
  const { id } = useParams<{ id: string }>();
  const [pkg, setPkg] = useState<Package | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [installing, setInstalling] = useState(false);
  const [downloading, setDownloading] = useState(false);

  useEffect(() => {
    if (id) {
      loadPackage();
    }
  }, [id]);

  const loadPackage = async () => {
    try {
      setLoading(true);
      const packageData = await marketplaceAPI.getPackage(id!);
      setPkg(packageData);
      setError(null);
    } catch (err) {
      setError('Failed to load package details');
      console.error('Error loading package:', err);
    } finally {
      setLoading(false);
    }
  };

  const handleInstall = async () => {
    if (!pkg) return;

    try {
      setInstalling(true);
      
      // Check compatibility
      const fabricVersion = '1.0.0'; // This would come from the current Fabric version
      if (!semver.satisfies(fabricVersion, pkg.compatibility['fabric-version'])) {
        alert(`Incompatible: Package requires Fabric ${pkg.compatibility['fabric-version']}, but you're running ${fabricVersion}`);
        return;
      }

      const response = await marketplaceAPI.installPackage({
        tenantId: 'demo-tenant', // This would come from auth context
        packageId: pkg.id,
        version: pkg.version,
      });

      alert(`Installation initiated: ${response.message}`);
    } catch (err) {
      alert('Installation failed. Please try again.');
      console.error('Installation error:', err);
    } finally {
      setInstalling(false);
    }
  };

  const handleDownload = async () => {
    if (!pkg) return;

    try {
      setDownloading(true);
      await marketplaceAPI.downloadPackage(pkg.id);
    } catch (err) {
      alert('Download failed. Please try again.');
      console.error('Download error:', err);
    } finally {
      setDownloading(false);
    }
  };

  const getTypeColor = (type: string) => {
    switch (type) {
      case 'adapter':
        return 'bg-blue-100 text-blue-800';
      case 'spec':
        return 'bg-green-100 text-green-800';
      case 'proofpack':
        return 'bg-purple-100 text-purple-800';
      default:
        return 'bg-gray-100 text-gray-800';
    }
  };

  const formatDate = (dateString: string) => {
    return new Date(dateString).toLocaleDateString();
  };

  if (loading) {
    return (
      <div className="flex justify-center items-center h-64">
        <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-primary-600"></div>
      </div>
    );
  }

  if (error || !pkg) {
    return (
      <div className="text-center py-8">
        <p className="text-red-600">{error || 'Package not found'}</p>
        <Link
          to="/"
          className="mt-4 inline-block bg-primary-600 text-white px-4 py-2 rounded-lg hover:bg-primary-700"
        >
          Back to Packages
        </Link>
      </div>
    );
  }

  return (
    <div className="max-w-4xl mx-auto">
      {/* Header */}
      <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6 mb-6">
        <div className="flex items-start justify-between mb-4">
          <div className="flex-1">
            <div className="flex items-center space-x-3 mb-2">
              <h1 className="text-3xl font-bold text-gray-900">{pkg.name}</h1>
              <span className={`px-3 py-1 rounded-full text-sm font-medium ${getTypeColor(pkg.type)}`}>
                {pkg.type}
              </span>
            </div>
            <p className="text-lg text-gray-600">{pkg.description}</p>
          </div>
          <div className="flex space-x-3">
            <button
              onClick={handleDownload}
              disabled={downloading}
              className="bg-green-600 text-white px-4 py-3 rounded-lg font-medium hover:bg-green-700 disabled:opacity-50 disabled:cursor-not-allowed"
            >
              {downloading ? 'Downloading...' : 'Download'}
            </button>
            <button
              onClick={handleInstall}
              disabled={installing}
              className="bg-primary-600 text-white px-6 py-3 rounded-lg font-medium hover:bg-primary-700 disabled:opacity-50 disabled:cursor-not-allowed"
            >
              {installing ? 'Installing...' : 'Install Package'}
            </button>
          </div>
        </div>

        {/* Metadata */}
        <div className="grid grid-cols-1 md:grid-cols-3 gap-4 text-sm text-gray-500">
          <div className="flex items-center">
            <UserIcon className="h-4 w-4 mr-2" />
            {pkg.author}
          </div>
          <div className="flex items-center">
                            <ArrowDownTrayIcon className="h-4 w-4 mr-2" />
            {pkg.downloads} downloads
          </div>
          <div className="flex items-center">
            <CalendarIcon className="h-4 w-4 mr-2" />
            Updated {formatDate(pkg.updated)}
          </div>
        </div>
      </div>

      <div className="grid grid-cols-1 lg:grid-cols-3 gap-6">
        {/* Main Content */}
        <div className="lg:col-span-2 space-y-6">
          {/* Version Info */}
          <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
            <h2 className="text-xl font-semibold text-gray-900 mb-4">Version Information</h2>
            <div className="space-y-3">
              <div className="flex justify-between">
                <span className="text-gray-600">Version:</span>
                <span className="font-medium">{pkg.version}</span>
              </div>
              <div className="flex justify-between">
                <span className="text-gray-600">License:</span>
                <span className="font-medium">{pkg.license}</span>
              </div>
              <div className="flex justify-between">
                <span className="text-gray-600">Created:</span>
                <span className="font-medium">{formatDate(pkg.created)}</span>
              </div>
            </div>
          </div>

          {/* Compatibility */}
          <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
            <h2 className="text-xl font-semibold text-gray-900 mb-4">Compatibility</h2>
            <div className="space-y-3">
              <div className="flex justify-between">
                <span className="text-gray-600">Fabric Version:</span>
                <span className="font-medium">≥ {pkg.compatibility['fabric-version']}</span>
              </div>
              {pkg.compatibility.adapters && pkg.compatibility.adapters.length > 0 && (
                <div>
                  <span className="text-gray-600">Required Adapters:</span>
                  <div className="mt-1">
                    {pkg.compatibility.adapters.map((adapter, index) => (
                      <span key={index} className="inline-block bg-gray-100 text-gray-700 px-2 py-1 rounded text-sm mr-2 mb-1">
                        {adapter}
                      </span>
                    ))}
                  </div>
                </div>
              )}
              {pkg.compatibility.specs && pkg.compatibility.specs.length > 0 && (
                <div>
                  <span className="text-gray-600">Required Specs:</span>
                  <div className="mt-1">
                    {pkg.compatibility.specs.map((spec, index) => (
                      <span key={index} className="inline-block bg-gray-100 text-gray-700 px-2 py-1 rounded text-sm mr-2 mb-1">
                        {spec}
                      </span>
                    ))}
                  </div>
                </div>
              )}
            </div>
          </div>

          {/* Keywords */}
          {pkg.keywords && pkg.keywords.length > 0 && (
            <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
              <h2 className="text-xl font-semibold text-gray-900 mb-4">Keywords</h2>
              <div className="flex flex-wrap gap-2">
                {pkg.keywords.map((keyword, index) => (
                  <span key={index} className="bg-primary-100 text-primary-800 px-3 py-1 rounded-full text-sm">
                    {keyword}
                  </span>
                ))}
              </div>
            </div>
          )}

          {/* Files */}
          {pkg.files && pkg.files.length > 0 && (
            <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
              <h2 className="text-xl font-semibold text-gray-900 mb-4">Files</h2>
              <div className="space-y-2">
                {pkg.files.map((file, index) => (
                  <div key={index} className="flex justify-between items-center py-2 border-b border-gray-100 last:border-b-0">
                    <span className="text-sm text-gray-600">{file.path}</span>
                    <span className="text-xs text-gray-500">{file.hash.substring(0, 8)}...</span>
                  </div>
                ))}
              </div>
            </div>
          )}
        </div>

        {/* Sidebar */}
        <div className="space-y-6">
          {/* Rating */}
          <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
            <h3 className="text-lg font-semibold text-gray-900 mb-4">Rating</h3>
            <div className="flex items-center mb-2">
              <div className="flex items-center">
                {[...Array(5)].map((_, i) => (
                  <StarIcon
                    key={i}
                    className={`h-5 w-5 ${
                      i < Math.floor(pkg.rating) ? 'text-yellow-400' : 'text-gray-300'
                    }`}
                  />
                ))}
              </div>
              <span className="ml-2 text-lg font-semibold">{pkg.rating.toFixed(1)}</span>
            </div>
            <p className="text-sm text-gray-500">Based on community feedback</p>
          </div>

          {/* Links */}
          <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
            <h3 className="text-lg font-semibold text-gray-900 mb-4">Links</h3>
            <div className="space-y-3">
              {pkg.repository && (
                <a
                  href={pkg.repository}
                  target="_blank"
                  rel="noopener noreferrer"
                  className="flex items-center text-primary-600 hover:text-primary-700"
                >
                  <CodeBracketIcon className="h-4 w-4 mr-2" />
                  Source Code
                </a>
              )}
              {pkg.homepage && (
                <a
                  href={pkg.homepage}
                  target="_blank"
                  rel="noopener noreferrer"
                  className="flex items-center text-primary-600 hover:text-primary-700"
                >
                  <GlobeAltIcon className="h-4 w-4 mr-2" />
                  Homepage
                </a>
              )}
            </div>
          </div>

          {/* Metadata */}
          {pkg.metadata && (
            <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
              <h3 className="text-lg font-semibold text-gray-900 mb-4">Metadata</h3>
              <div className="space-y-2 text-sm">
                {Object.entries(pkg.metadata).map(([key, value]) => (
                  <div key={key} className="flex justify-between">
                    <span className="text-gray-600 capitalize">{key}:</span>
                    <span className="font-medium">{String(value)}</span>
                  </div>
                ))}
              </div>
            </div>
          )}
        </div>
      </div>
    </div>
  );
};