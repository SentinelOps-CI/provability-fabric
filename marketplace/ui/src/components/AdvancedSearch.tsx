import React, { useState, useEffect, useMemo } from 'react';
import { MagnifyingGlassIcon, FunnelIcon, XMarkIcon } from '@heroicons/react/24/outline';
import { useDebounce } from '../hooks/useDebounce';

export interface SearchFilters {
  query: string;
  type: string;
  author: string;
  minRating: number;
  compatibility: string;
  sortBy: 'relevance' | 'downloads' | 'rating' | 'updated' | 'name';
  sortOrder: 'asc' | 'desc';
}

export interface Package {
  id: string;
  name: string;
  version: string;
  description: string;
  author: string;
  type: string;
  downloads: number;
  rating: number;
  updated: string;
  created: string;
  compatibility: { [key: string]: string };
}

interface AdvancedSearchProps {
  onSearch: (filters: SearchFilters) => void;
  onClearFilters: () => void;
  isLoading?: boolean;
  resultsCount?: number;
}

export const AdvancedSearch: React.FC<AdvancedSearchProps> = ({
  onSearch,
  onClearFilters,
  isLoading = false,
  resultsCount = 0
}) => {
  const [filters, setFilters] = useState<SearchFilters>({
    query: '',
    type: '',
    author: '',
    minRating: 0,
    compatibility: '',
    sortBy: 'relevance',
    sortOrder: 'desc'
  });

  const [showAdvanced, setShowAdvanced] = useState(false);
  const [searchHistory, setSearchHistory] = useState<string[]>([]);

  // Debounce search query for performance
  const debouncedQuery = useDebounce(filters.query, 300);

  // Available filter options
  const packageTypes = [
    { value: '', label: 'All Types' },
    { value: 'adapter', label: 'Adapters' },
    { value: 'spec', label: 'Specifications' },
    { value: 'proofpack', label: 'Proof Packs' },
    { value: 'tool', label: 'Tools' }
  ];

  const sortOptions = [
    { value: 'relevance', label: 'Relevance' },
    { value: 'downloads', label: 'Downloads' },
    { value: 'rating', label: 'Rating' },
    { value: 'updated', label: 'Last Updated' },
    { value: 'name', label: 'Name' }
  ];

  // Load search history from localStorage
  useEffect(() => {
    const history = localStorage.getItem('searchHistory');
    if (history) {
      setSearchHistory(JSON.parse(history));
    }
  }, []);

  // Trigger search when debounced query or filters change
  useEffect(() => {
    const updatedFilters = { ...filters, query: debouncedQuery };
    onSearch(updatedFilters);
    
    // Save to search history if query is not empty
    if (debouncedQuery.trim() && !searchHistory.includes(debouncedQuery.trim())) {
      const newHistory = [debouncedQuery.trim(), ...searchHistory.slice(0, 9)]; // Keep last 10 searches
      setSearchHistory(newHistory);
      localStorage.setItem('searchHistory', JSON.stringify(newHistory));
    }
  }, [debouncedQuery, filters.type, filters.author, filters.minRating, filters.compatibility, filters.sortBy, filters.sortOrder]);

  const updateFilter = (key: keyof SearchFilters, value: any) => {
    setFilters(prev => ({ ...prev, [key]: value }));
  };

  const clearAllFilters = () => {
    setFilters({
      query: '',
      type: '',
      author: '',
      minRating: 0,
      compatibility: '',
      sortBy: 'relevance',
      sortOrder: 'desc'
    });
    onClearFilters();
  };

  const hasActiveFilters = useMemo(() => {
    return filters.type || filters.author || filters.minRating > 0 || filters.compatibility;
  }, [filters]);

  const clearSearchHistory = () => {
    setSearchHistory([]);
    localStorage.removeItem('searchHistory');
  };

  return (
    <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
      {/* Main Search Bar */}
      <div className="relative">
        <div className="relative">
          <MagnifyingGlassIcon className="absolute left-3 top-1/2 transform -translate-y-1/2 h-5 w-5 text-gray-400" />
          <input
            type="text"
            placeholder="Search packages, descriptions, authors..."
            value={filters.query}
            onChange={(e) => updateFilter('query', e.target.value)}
            className="w-full pl-10 pr-20 py-3 border border-gray-300 rounded-lg focus:ring-2 focus:ring-indigo-500 focus:border-indigo-500 text-sm"
          />
          <div className="absolute right-2 top-1/2 transform -translate-y-1/2 flex items-center space-x-2">
            <button
              onClick={() => setShowAdvanced(!showAdvanced)}
              className={`p-2 rounded-md transition-colors ${
                showAdvanced || hasActiveFilters
                  ? 'bg-indigo-100 text-indigo-600'
                  : 'bg-gray-100 text-gray-600 hover:bg-gray-200'
              }`}
              title="Advanced filters"
            >
              <FunnelIcon className="h-4 w-4" />
            </button>
          </div>
        </div>

        {/* Search History Dropdown */}
        {filters.query === '' && searchHistory.length > 0 && (
          <div className="absolute top-full left-0 right-0 mt-1 bg-white border border-gray-200 rounded-md shadow-lg z-10">
            <div className="p-2 border-b border-gray-100 flex justify-between items-center">
              <span className="text-xs font-medium text-gray-600">Recent Searches</span>
              <button
                onClick={clearSearchHistory}
                className="text-xs text-gray-400 hover:text-gray-600"
              >
                Clear
              </button>
            </div>
            {searchHistory.map((query, index) => (
              <button
                key={index}
                onClick={() => updateFilter('query', query)}
                className="w-full text-left px-3 py-2 text-sm text-gray-700 hover:bg-gray-50 flex items-center"
              >
                <MagnifyingGlassIcon className="h-4 w-4 text-gray-400 mr-2" />
                {query}
              </button>
            ))}
          </div>
        )}
      </div>

      {/* Advanced Filters */}
      {showAdvanced && (
        <div className="mt-4 pt-4 border-t border-gray-200">
          <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-4 gap-4">
            {/* Package Type Filter */}
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Package Type
              </label>
              <select
                value={filters.type}
                onChange={(e) => updateFilter('type', e.target.value)}
                className="w-full px-3 py-2 border border-gray-300 rounded-md focus:ring-indigo-500 focus:border-indigo-500 text-sm"
              >
                {packageTypes.map(type => (
                  <option key={type.value} value={type.value}>
                    {type.label}
                  </option>
                ))}
              </select>
            </div>

            {/* Author Filter */}
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Author
              </label>
              <input
                type="text"
                placeholder="Filter by author..."
                value={filters.author}
                onChange={(e) => updateFilter('author', e.target.value)}
                className="w-full px-3 py-2 border border-gray-300 rounded-md focus:ring-indigo-500 focus:border-indigo-500 text-sm"
              />
            </div>

            {/* Minimum Rating Filter */}
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Minimum Rating
              </label>
              <select
                value={filters.minRating}
                onChange={(e) => updateFilter('minRating', Number(e.target.value))}
                className="w-full px-3 py-2 border border-gray-300 rounded-md focus:ring-indigo-500 focus:border-indigo-500 text-sm"
              >
                <option value={0}>Any Rating</option>
                <option value={4.5}>4.5+ Stars</option>
                <option value={4.0}>4.0+ Stars</option>
                <option value={3.5}>3.5+ Stars</option>
                <option value={3.0}>3.0+ Stars</option>
              </select>
            </div>

            {/* Compatibility Filter */}
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Compatibility
              </label>
              <input
                type="text"
                placeholder="e.g., fabric-version"
                value={filters.compatibility}
                onChange={(e) => updateFilter('compatibility', e.target.value)}
                className="w-full px-3 py-2 border border-gray-300 rounded-md focus:ring-indigo-500 focus:border-indigo-500 text-sm"
              />
            </div>
          </div>

          {/* Sort Options */}
          <div className="mt-4 flex flex-wrap items-center gap-4">
            <div className="flex items-center space-x-2">
              <label className="text-sm font-medium text-gray-700">Sort by:</label>
              <select
                value={filters.sortBy}
                onChange={(e) => updateFilter('sortBy', e.target.value)}
                className="px-3 py-1 border border-gray-300 rounded-md focus:ring-indigo-500 focus:border-indigo-500 text-sm"
              >
                {sortOptions.map(option => (
                  <option key={option.value} value={option.value}>
                    {option.label}
                  </option>
                ))}
              </select>
            </div>

            <div className="flex items-center space-x-2">
              <label className="text-sm font-medium text-gray-700">Order:</label>
              <select
                value={filters.sortOrder}
                onChange={(e) => updateFilter('sortOrder', e.target.value)}
                className="px-3 py-1 border border-gray-300 rounded-md focus:ring-indigo-500 focus:border-indigo-500 text-sm"
              >
                <option value="desc">Descending</option>
                <option value="asc">Ascending</option>
              </select>
            </div>

            {hasActiveFilters && (
              <button
                onClick={clearAllFilters}
                className="flex items-center space-x-1 px-3 py-1 text-sm text-gray-600 hover:text-gray-800 border border-gray-300 rounded-md hover:bg-gray-50"
              >
                <XMarkIcon className="h-4 w-4" />
                <span>Clear Filters</span>
              </button>
            )}
          </div>
        </div>
      )}

      {/* Results Summary */}
      <div className="mt-4 flex justify-between items-center text-sm text-gray-600">
        <div>
          {isLoading ? (
            <span>Searching...</span>
          ) : (
            <span>
              {resultsCount} {resultsCount === 1 ? 'result' : 'results'}
              {filters.query && ` for "${filters.query}"`}
            </span>
          )}
        </div>
        
        {hasActiveFilters && (
          <div className="flex items-center space-x-2">
            <span className="text-xs">Active filters:</span>
            <div className="flex space-x-1">
              {filters.type && (
                <span className="inline-flex items-center px-2 py-1 rounded-full text-xs bg-blue-100 text-blue-800">
                  Type: {packageTypes.find(t => t.value === filters.type)?.label}
                </span>
              )}
              {filters.author && (
                <span className="inline-flex items-center px-2 py-1 rounded-full text-xs bg-green-100 text-green-800">
                  Author: {filters.author}
                </span>
              )}
              {filters.minRating > 0 && (
                <span className="inline-flex items-center px-2 py-1 rounded-full text-xs bg-yellow-100 text-yellow-800">
                  Rating: {filters.minRating}+
                </span>
              )}
            </div>
          </div>
        )}
      </div>
    </div>
  );
};

export default AdvancedSearch;
