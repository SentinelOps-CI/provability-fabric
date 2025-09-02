import { Package, SearchFilters } from '../components/AdvancedSearch';

export interface SearchResult {
  packages: Package[];
  total: number;
  query: string;
  executionTime: number;
}

/**
 * Advanced search engine for marketplace packages
 * Implements fuzzy search, filtering, and relevance scoring
 */
export class SearchEngine {
  private packages: Package[] = [];

  constructor(packages: Package[] = []) {
    this.packages = packages;
  }

  /**
   * Update the package database
   */
  updatePackages(packages: Package[]): void {
    this.packages = packages;
  }

  /**
   * Perform advanced search with filters and sorting
   */
  search(filters: SearchFilters): SearchResult {
    const startTime = performance.now();
    let results = [...this.packages];

    // Apply text search with fuzzy matching
    if (filters.query.trim()) {
      results = this.performTextSearch(results, filters.query);
    }

    // Apply filters
    results = this.applyFilters(results, filters);

    // Sort results
    results = this.sortResults(results, filters);

    const executionTime = performance.now() - startTime;

    return {
      packages: results,
      total: results.length,
      query: filters.query,
      executionTime
    };
  }

  /**
   * Perform fuzzy text search across multiple fields
   */
  private performTextSearch(packages: Package[], query: string): Package[] {
    const searchTerms = query.toLowerCase().split(/\s+/).filter(term => term.length > 0);
    
    return packages
      .map(pkg => ({
        package: pkg,
        score: this.calculateRelevanceScore(pkg, searchTerms)
      }))
      .filter(result => result.score > 0)
      .sort((a, b) => b.score - a.score)
      .map(result => result.package);
  }

  /**
   * Calculate relevance score for a package based on search terms
   */
  private calculateRelevanceScore(pkg: Package, searchTerms: string[]): number {
    let score = 0;
    const searchableText = {
      name: pkg.name.toLowerCase(),
      description: pkg.description.toLowerCase(),
      author: pkg.author.toLowerCase(),
      type: pkg.type.toLowerCase()
    };

    for (const term of searchTerms) {
      // Exact matches get highest score
      if (searchableText.name.includes(term)) {
        score += 10;
      }
      if (searchableText.description.includes(term)) {
        score += 5;
      }
      if (searchableText.author.includes(term)) {
        score += 7;
      }
      if (searchableText.type.includes(term)) {
        score += 6;
      }

      // Fuzzy matching for partial matches
      score += this.fuzzyMatch(searchableText.name, term) * 3;
      score += this.fuzzyMatch(searchableText.description, term) * 2;
      score += this.fuzzyMatch(searchableText.author, term) * 2;
    }

    // Boost score based on package popularity
    score += Math.log(pkg.downloads + 1) * 0.1;
    score += pkg.rating * 0.5;

    return score;
  }

  /**
   * Simple fuzzy matching algorithm
   */
  private fuzzyMatch(text: string, pattern: string): number {
    if (pattern.length === 0) return 0;
    if (text.length === 0) return 0;

    let score = 0;
    let textIndex = 0;
    let patternIndex = 0;

    while (textIndex < text.length && patternIndex < pattern.length) {
      if (text[textIndex] === pattern[patternIndex]) {
        score++;
        patternIndex++;
      }
      textIndex++;
    }

    // Return normalized score (0-1)
    return patternIndex === pattern.length ? score / pattern.length : 0;
  }

  /**
   * Apply various filters to the package list
   */
  private applyFilters(packages: Package[], filters: SearchFilters): Package[] {
    return packages.filter(pkg => {
      // Type filter
      if (filters.type && pkg.type !== filters.type) {
        return false;
      }

      // Author filter (case-insensitive partial match)
      if (filters.author && !pkg.author.toLowerCase().includes(filters.author.toLowerCase())) {
        return false;
      }

      // Minimum rating filter
      if (filters.minRating > 0 && pkg.rating < filters.minRating) {
        return false;
      }

      // Compatibility filter
      if (filters.compatibility) {
        const hasCompatibility = Object.keys(pkg.compatibility).some(key =>
          key.toLowerCase().includes(filters.compatibility.toLowerCase()) ||
          pkg.compatibility[key].toLowerCase().includes(filters.compatibility.toLowerCase())
        );
        if (!hasCompatibility) {
          return false;
        }
      }

      return true;
    });
  }

  /**
   * Sort results based on the specified criteria
   */
  private sortResults(packages: Package[], filters: SearchFilters): Package[] {
    const { sortBy, sortOrder } = filters;
    const multiplier = sortOrder === 'asc' ? 1 : -1;

    return packages.sort((a, b) => {
      let comparison = 0;

      switch (sortBy) {
        case 'name':
          comparison = a.name.localeCompare(b.name);
          break;
        case 'downloads':
          comparison = a.downloads - b.downloads;
          break;
        case 'rating':
          comparison = a.rating - b.rating;
          break;
        case 'updated':
          comparison = new Date(a.updated).getTime() - new Date(b.updated).getTime();
          break;
        case 'relevance':
        default:
          // For relevance, maintain the order from text search
          // If no text search was performed, sort by a combination of factors
          if (!filters.query.trim()) {
            comparison = (b.downloads * 0.3 + b.rating * 100) - (a.downloads * 0.3 + a.rating * 100);
          }
          break;
      }

      return comparison * multiplier;
    });
  }

  /**
   * Get search suggestions based on partial query
   */
  getSuggestions(query: string, limit: number = 5): string[] {
    if (!query.trim()) return [];

    const suggestions = new Set<string>();
    const queryLower = query.toLowerCase();

    for (const pkg of this.packages) {
      // Suggest package names
      if (pkg.name.toLowerCase().startsWith(queryLower)) {
        suggestions.add(pkg.name);
      }

      // Suggest authors
      if (pkg.author.toLowerCase().startsWith(queryLower)) {
        suggestions.add(pkg.author);
      }

      // Suggest types
      if (pkg.type.toLowerCase().startsWith(queryLower)) {
        suggestions.add(pkg.type);
      }

      if (suggestions.size >= limit) break;
    }

    return Array.from(suggestions).slice(0, limit);
  }

  /**
   * Get popular search terms
   */
  getPopularTerms(limit: number = 10): string[] {
    const termFrequency = new Map<string, number>();

    for (const pkg of this.packages) {
      // Count words in names and descriptions
      const words = [
        ...pkg.name.toLowerCase().split(/\s+/),
        ...pkg.description.toLowerCase().split(/\s+/),
        pkg.author.toLowerCase(),
        pkg.type.toLowerCase()
      ];

      for (const word of words) {
        if (word.length > 2) { // Ignore very short words
          termFrequency.set(word, (termFrequency.get(word) || 0) + 1);
        }
      }
    }

    return Array.from(termFrequency.entries())
      .sort((a, b) => b[1] - a[1])
      .slice(0, limit)
      .map(([term]) => term);
  }

  /**
   * Get search analytics/metrics
   */
  getSearchMetrics(): {
    totalPackages: number;
    packageTypes: { [key: string]: number };
    authorCount: number;
    averageRating: number;
    totalDownloads: number;
  } {
    const packageTypes: { [key: string]: number } = {};
    const authors = new Set<string>();
    let totalRating = 0;
    let totalDownloads = 0;

    for (const pkg of this.packages) {
      packageTypes[pkg.type] = (packageTypes[pkg.type] || 0) + 1;
      authors.add(pkg.author);
      totalRating += pkg.rating;
      totalDownloads += pkg.downloads;
    }

    return {
      totalPackages: this.packages.length,
      packageTypes,
      authorCount: authors.size,
      averageRating: this.packages.length > 0 ? totalRating / this.packages.length : 0,
      totalDownloads
    };
  }
}

// Create and export a singleton instance
export const searchEngine = new SearchEngine();
export default SearchEngine;
