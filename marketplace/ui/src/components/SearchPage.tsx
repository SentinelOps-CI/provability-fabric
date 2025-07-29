import React, { useState, useEffect } from 'react';
import { useSearchParams, Link } from 'react-router-dom';
import { MagnifyingGlassIcon } from '@heroicons/react/24/outline';
import { marketplaceAPI } from '../services/api';
import { Package } from '../types';

export const SearchPage: React.FC = () => {
  const [searchParams, setSearchParams] = useSearchParams();
  const [query, setQuery] = useState(searchParams.get('q') || '');
  const [results, setResults] = useState<Package[]>([]);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    const searchQuery = searchParams.get('q');
    if (searchQuery) {
      setQuery(searchQuery);
      performSearch(searchQuery);
    }
  }, [searchParams]);

  const performSearch = async (searchQuery: string) => {
    if (!searchQuery.trim()) return;

    try {
      setLoading(true);
      setError(null);
      const response = await marketplaceAPI.searchPackages(searchQuery);
      setResults(response.results);
    } catch (err) {
      setError('Failed to perform search');
      console.error('Search error:', err);
    } finally {
      setLoading(false);
    }
  };

  const handleSearch = (e: React.FormEvent) => {
    e.preventDefault();
    if (query.trim()) {
      setSearchParams({ q: query.trim() });
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

  return (
    <div className="max-w-4xl mx-auto">
      {/* Search Form */}
      <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6 mb-8">
        <h1 className="text-2xl font-bold text-gray-900 mb-4">Search Packages</h1>
        <form onSubmit={handleSearch} className="flex gap-4">
          <div className="flex-1 relative">
            <input
              type="text"
              value={query}
              onChange={(e) => setQuery(e.target.value)}
              placeholder="Search for packages, authors, keywords..."
              className="w-full pl-10 pr-4 py-3 border border-gray-300 rounded-lg focus:ring-2 focus:ring-primary-500 focus:border-primary-500"
            />
            <MagnifyingGlassIcon className="absolute left-3 top-3.5 h-5 w-5 text-gray-400" />
          </div>
          <button
            type="submit"
            className="bg-primary-600 text-white px-6 py-3 rounded-lg font-medium hover:bg-primary-700"
          >
            Search
          </button>
        </form>
      </div>

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
            onClick={() => performSearch(query)}
            className="mt-4 bg-primary-600 text-white px-4 py-2 rounded-lg hover:bg-primary-700"
          >
            Retry
          </button>
        </div>
      )}

      {!loading && !error && results.length > 0 && (
        <div>
          <div className="mb-6">
            <h2 className="text-lg font-semibold text-gray-900">
              Found {results.length} package{results.length !== 1 ? 's' : ''} for "{query}"
            </h2>
          </div>

          <div className="space-y-4">
            {results.map((pkg) => (
              <div key={pkg.id} className="bg-white rounded-lg shadow-sm border border-gray-200 p-6 hover:shadow-md transition-shadow">
                <div className="flex items-start justify-between">
                  <div className="flex-1">
                    <div className="flex items-center space-x-3 mb-2">
                      <h3 className="text-xl font-semibold text-gray-900">
                        <Link to={`/package/${pkg.id}`} className="hover:text-primary-600">
                          {pkg.name}
                        </Link>
                      </h3>
                      <span className={`px-2 py-1 rounded-full text-xs font-medium ${getTypeColor(pkg.type)}`}>
                        {pkg.type}
                      </span>
                      <span className="text-sm text-gray-500">v{pkg.version}</span>
                    </div>
                    <p className="text-gray-600 mb-3">{pkg.description}</p>
                    <div className="flex items-center space-x-6 text-sm text-gray-500">
                      <span>by {pkg.author}</span>
                      <span>{pkg.downloads} downloads</span>
                      <span>Updated {formatDate(pkg.updated)}</span>
                      <span>★ {pkg.rating.toFixed(1)}</span>
                    </div>
                  </div>
                  <Link
                    to={`/package/${pkg.id}`}
                    className="bg-primary-600 text-white px-4 py-2 rounded-lg text-sm font-medium hover:bg-primary-700"
                  >
                    View Details
                  </Link>
                </div>
              </div>
            ))}
          </div>
        </div>
      )}

      {!loading && !error && results.length === 0 && query && (
        <div className="text-center py-12">
          <p className="text-gray-500">No packages found for "{query}"</p>
          <p className="text-sm text-gray-400 mt-2">Try different keywords or browse all packages</p>
          <Link
            to="/"
            className="mt-4 inline-block bg-primary-600 text-white px-4 py-2 rounded-lg hover:bg-primary-700"
          >
            Browse All Packages
          </Link>
        </div>
      )}

      {!loading && !error && !query && (
        <div className="text-center py-12">
          <p className="text-gray-500">Enter a search query to find packages</p>
        </div>
      )}
    </div>
  );
};