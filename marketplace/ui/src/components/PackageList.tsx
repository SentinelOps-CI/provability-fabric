import React, { useState, useEffect } from 'react';
import { Link } from 'react-router-dom';
import { StarIcon, DownloadIcon, CalendarIcon, UserIcon } from '@heroicons/react/24/outline';
import { StarIcon as StarIconSolid } from '@heroicons/react/24/solid';
import { marketplaceAPI } from '../services/api';
import { Package } from '../types';
import semver from 'semver';

export const PackageList: React.FC = () => {
  const [packages, setPackages] = useState<Package[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [selectedType, setSelectedType] = useState<string>('');
  const [selectedAuthor, setSelectedAuthor] = useState<string>('');
  const [installing, setInstalling] = useState<string | null>(null);

  useEffect(() => {
    loadPackages();
  }, [selectedType, selectedAuthor]);

  const loadPackages = async () => {
    try {
      setLoading(true);
      const response = await marketplaceAPI.getPackages(selectedType || undefined, selectedAuthor || undefined);
      setPackages(response.packages);
      setError(null);
    } catch (err) {
      setError('Failed to load packages');
      console.error('Error loading packages:', err);
    } finally {
      setLoading(false);
    }
  };

  const handleInstall = async (pkg: Package) => {
    try {
      setInstalling(pkg.id);
      
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
      setInstalling(null);
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

  if (error) {
    return (
      <div className="text-center py-8">
        <p className="text-red-600">{error}</p>
        <button
          onClick={loadPackages}
          className="mt-4 bg-primary-600 text-white px-4 py-2 rounded-lg hover:bg-primary-700"
        >
          Retry
        </button>
      </div>
    );
  }

  return (
    <div>
      {/* Filters */}
      <div className="mb-8 bg-white p-6 rounded-lg shadow-sm border border-gray-200">
        <h2 className="text-lg font-semibold text-gray-900 mb-4">Filters</h2>
        <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
          <div>
            <label className="block text-sm font-medium text-gray-700 mb-2">
              Package Type
            </label>
            <select
              value={selectedType}
              onChange={(e) => setSelectedType(e.target.value)}
              className="w-full border border-gray-300 rounded-lg px-3 py-2 focus:ring-2 focus:ring-primary-500 focus:border-primary-500"
            >
              <option value="">All Types</option>
              <option value="adapter">Adapters</option>
              <option value="spec">Specifications</option>
              <option value="proofpack">Proof Packs</option>
            </select>
          </div>
          <div>
            <label className="block text-sm font-medium text-gray-700 mb-2">
              Author
            </label>
            <input
              type="text"
              value={selectedAuthor}
              onChange={(e) => setSelectedAuthor(e.target.value)}
              placeholder="Filter by author..."
              className="w-full border border-gray-300 rounded-lg px-3 py-2 focus:ring-2 focus:ring-primary-500 focus:border-primary-500"
            />
          </div>
        </div>
      </div>

      {/* Package Grid */}
      <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6">
        {packages.map((pkg) => (
          <div key={pkg.id} className="bg-white rounded-lg shadow-sm border border-gray-200 hover:shadow-md transition-shadow">
            <div className="p-6">
              {/* Header */}
              <div className="flex items-start justify-between mb-4">
                <div className="flex-1">
                  <h3 className="text-lg font-semibold text-gray-900 mb-1">
                    <Link to={`/package/${pkg.id}`} className="hover:text-primary-600">
                      {pkg.name}
                    </Link>
                  </h3>
                  <p className="text-sm text-gray-500">v{pkg.version}</p>
                </div>
                <span className={`px-2 py-1 rounded-full text-xs font-medium ${getTypeColor(pkg.type)}`}>
                  {pkg.type}
                </span>
              </div>

              {/* Description */}
              <p className="text-gray-600 text-sm mb-4 line-clamp-2">
                {pkg.description}
              </p>

              {/* Metadata */}
              <div className="space-y-2 mb-4">
                <div className="flex items-center text-sm text-gray-500">
                  <UserIcon className="h-4 w-4 mr-2" />
                  {pkg.author}
                </div>
                <div className="flex items-center text-sm text-gray-500">
                  <DownloadIcon className="h-4 w-4 mr-2" />
                  {pkg.downloads} downloads
                </div>
                <div className="flex items-center text-sm text-gray-500">
                  <CalendarIcon className="h-4 w-4 mr-2" />
                  Updated {formatDate(pkg.updated)}
                </div>
              </div>

              {/* Rating */}
              <div className="flex items-center mb-4">
                <div className="flex items-center">
                  {[...Array(5)].map((_, i) => (
                    <StarIcon
                      key={i}
                      className={`h-4 w-4 ${
                        i < Math.floor(pkg.rating) ? 'text-yellow-400' : 'text-gray-300'
                      }`}
                    />
                  ))}
                </div>
                <span className="ml-2 text-sm text-gray-500">{pkg.rating.toFixed(1)}</span>
              </div>

              {/* Compatibility */}
              <div className="mb-4">
                <span className="text-xs text-gray-500">
                  Requires Fabric ≥ {pkg.compatibility['fabric-version']}
                </span>
              </div>

              {/* Actions */}
              <div className="flex space-x-2">
                <Link
                  to={`/package/${pkg.id}`}
                  className="flex-1 bg-gray-100 text-gray-700 px-4 py-2 rounded-lg text-sm font-medium hover:bg-gray-200 text-center"
                >
                  Details
                </Link>
                <button
                  onClick={() => handleInstall(pkg)}
                  disabled={installing === pkg.id}
                  className="flex-1 bg-primary-600 text-white px-4 py-2 rounded-lg text-sm font-medium hover:bg-primary-700 disabled:opacity-50 disabled:cursor-not-allowed"
                >
                  {installing === pkg.id ? 'Installing...' : 'Install'}
                </button>
              </div>
            </div>
          </div>
        ))}
      </div>

      {packages.length === 0 && !loading && (
        <div className="text-center py-12">
          <p className="text-gray-500">No packages found matching your criteria.</p>
        </div>
      )}
    </div>
  );
};