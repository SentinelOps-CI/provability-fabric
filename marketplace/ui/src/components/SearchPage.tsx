import React, { useState, useEffect, useCallback } from 'react';
import { useSearchParams, Link } from 'react-router-dom';
import { ChartBarIcon, ClockIcon, StarIcon } from '@heroicons/react/24/outline';
import { marketplaceAPI } from '../services/api';
import type { Package } from '../types';
import { AdvancedSearch, SearchFilters } from './AdvancedSearch';
import { searchEngine } from '../utils/searchEngine';
import { useWebSocket } from '../hooks/useWebSocket';

export const SearchPage: React.FC = () => {
  const [searchParams, setSearchParams] = useSearchParams();
  const [allPackages, setAllPackages] = useState<Package[]>([]);
  const [results, setResults] = useState<Package[]>([]);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [searchMetrics, setSearchMetrics] = useState({ executionTime: 0, total: 0 });

  // WebSocket for real-time updates
  const { isConnected } = useWebSocket({
    onMessage: (message) => {
      if (message.type === 'new_package') {
        setAllPackages(prev => {
          const updated = [message.package as Package, ...prev];
          searchEngine.updatePackages(updated);
          return updated;
        });
      }
    }
  });

  // Load packages on component mount
  useEffect(() => {
    const loadPackages = async () => {
      try {
        setLoading(true);
        const response = await marketplaceAPI.getPackages();
        setAllPackages(response.packages as Package[]);
        searchEngine.updatePackages(response.packages as Package[]);
      } catch (err) {
        setError('Failed to load packages');
        console.error('Load packages error:', err);
      } finally {
        setLoading(false);
      }
    };

    loadPackages();
  }, []);

  const performAdvancedSearch = useCallback((filters: SearchFilters) => {
    if (allPackages.length === 0) return;

    try {
      setLoading(true);
      setError(null);

      const searchResult = searchEngine.search(filters);
      setResults(searchResult.packages as unknown as Package[]);
      setSearchMetrics({
        executionTime: searchResult.executionTime,
        total: searchResult.total
      });
    } catch (err) {
      setError('Search failed');
      console.error('Search error:', err);
    } finally {
      setLoading(false);
    }
  }, [allPackages]);

  // Handle URL search params
  useEffect(() => {
    const searchQuery = searchParams.get('q');
    if (searchQuery && allPackages.length > 0) {
      performAdvancedSearch({
        query: searchQuery,
        type: '',
        author: '',
        minRating: 0,
        compatibility: '',
        sortBy: 'relevance',
        sortOrder: 'desc'
      });
    }
  }, [searchParams, allPackages, performAdvancedSearch]);

  const clearFilters = () => {
    setResults(allPackages);
    setSearchParams({});
    setSearchMetrics({ executionTime: 0, total: allPackages.length });
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

  return (
    <div className="max-w-6xl mx-auto">
      {/* Header */}
      <div className="mb-8">
        <h1 className="text-3xl font-bold text-gray-900 mb-2">Package Search</h1>
        <div className="flex items-center space-x-4 text-sm text-gray-600">
          <span>{allPackages.length} packages available</span>
          {isConnected && (
            <span className="flex items-center text-green-600">
              <span className="w-2 h-2 bg-green-500 rounded-full mr-2"></span>
              Live updates enabled
            </span>
          )}
          {searchMetrics.executionTime > 0 && (
            <span>Search completed in {searchMetrics.executionTime.toFixed(2)}ms</span>
          )}
        </div>
      </div>

      {/* Advanced Search Component */}
      <AdvancedSearch
        onSearch={performAdvancedSearch}
        onClearFilters={clearFilters}
        isLoading={loading}
        resultsCount={results.length}
      />

      {/* Results */}
      {loading && (
        <div className="flex justify-center items-center h-64">
          <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-primary-600"></div>
        </div>
      )}

      {error && (
        <div className="text-center py-8">
          <p className="text-red-600">{error}</p>
          <button
            onClick={() =>
              performAdvancedSearch({
                query: searchParams.get('q') ?? '',
                type: '',
                author: '',
                minRating: 0,
                compatibility: '',
                sortBy: 'relevance',
                sortOrder: 'desc'
              })
            }
            className="mt-4 bg-primary-600 text-white px-4 py-2 rounded-lg hover:bg-primary-700"
          >
            Retry
          </button>
        </div>
      )}

      {!loading && !error && results.length > 0 && (
        <div className="mt-8">
          <div className="grid grid-cols-1 lg:grid-cols-2 xl:grid-cols-3 gap-6">
            {results.map((pkg) => (
              <div
                key={pkg.id}
                className="bg-white rounded-lg shadow-sm border border-gray-200 p-6 hover:shadow-md transition-all hover:border-indigo-300"
              >
                <div className="flex flex-col h-full">
                  {/* Package Header */}
                  <div className="flex items-start justify-between mb-3">
                    <div className="flex items-center space-x-2">
                      <span className={`px-2 py-1 rounded-full text-xs font-medium ${getTypeColor(pkg.type)}`}>
                        {pkg.type}
                      </span>
                      <span className="text-sm text-gray-500">v{pkg.version}</span>
                    </div>
                    <div className="flex items-center text-yellow-500">
                      <StarIcon className="h-4 w-4 mr-1" />
                      <span className="text-sm font-medium">{pkg.rating.toFixed(1)}</span>
                    </div>
                  </div>

                  {/* Package Title */}
                  <h3 className="text-lg font-semibold text-gray-900 mb-2 hover:text-indigo-600">
                    <Link to={`/package/${pkg.id}`}>{pkg.name}</Link>
                  </h3>

                  {/* Description */}
                  <p className="text-gray-600 text-sm mb-4 flex-1 line-clamp-3">{pkg.description}</p>

                  {/* Metadata */}
                  <div className="space-y-2">
                    <div className="flex items-center justify-between text-sm text-gray-500">
                      <span className="flex items-center">
                        <ChartBarIcon className="h-4 w-4 mr-1" />
                        {pkg.downloads.toLocaleString()} downloads
                      </span>
                      <span className="flex items-center">
                        <ClockIcon className="h-4 w-4 mr-1" />
                        {formatDate(pkg.updated)}
                      </span>
                    </div>
                    <div className="flex items-center justify-between">
                      <span className="text-sm text-gray-600 font-medium">by {pkg.author}</span>
                      <Link
                        to={`/package/${pkg.id}`}
                        className="bg-indigo-600 text-white px-3 py-1 rounded-md text-sm font-medium hover:bg-indigo-700 transition-colors"
                      >
                        View Details
                      </Link>
                    </div>
                  </div>
                </div>
              </div>
            ))}
          </div>
        </div>
      )}

      {!loading && !error && results.length === 0 && allPackages.length > 0 && (
        <div className="text-center py-12">
          <p className="text-gray-500">No packages match your search criteria</p>
          <p className="text-sm text-gray-400 mt-2">Try adjusting your filters or search terms</p>
          <button onClick={clearFilters} className="mt-4 inline-block bg-indigo-600 text-white px-4 py-2 rounded-lg hover:bg-indigo-700">
            Clear Filters
          </button>
        </div>
      )}

      {!loading && !error && allPackages.length === 0 && (
        <div className="text-center py-12">
          <p className="text-gray-500">Loading packages...</p>
        </div>
      )}
    </div>
  );
};