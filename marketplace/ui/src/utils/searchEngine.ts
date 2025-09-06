import type { Package } from '../types';
import type { SearchFilters } from '../components/AdvancedSearch';

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

  /** Update the package database */
  updatePackages(packages: Package[]): void {
    this.packages = packages;
  }

  /** Perform advanced search with filters and sorting */
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

  /** Perform fuzzy text search across multiple fields */
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

  /** Calculate relevance score for a package based on search terms */
  private calculateRelevanceScore(pkg: Package, searchTerms: string[]): number {
    let score = 0;
    const searchableText = {
      name: (pkg.name ?? '').toLowerCase(),
      description: (pkg.description ?? '').toLowerCase(),
      author: (pkg.author ?? '').toLowerCase(),
      type: (pkg.type ?? '').toLowerCase()
    };

    for (const term of searchTerms) {
      // Exact-ish matches get highest score
      if (searchableText.name.includes(term)) score += 10;
      if (searchableText.description.includes(term)) score += 5;
      if (searchableText.author.includes(term)) score += 7;
      if (searchableText.type.includes(term)) score += 6;

      // Fuzzy matching for partial matches
      score += this.fuzzyMatch(searchableText.name, term) * 3;
      score += this.fuzzyMatch(searchableText.description, term) * 2;
      score += this.fuzzyMatch(searchableText.author, term) * 2;
    }

    // Boost score based on package popularity
    score += Math.log((pkg.downloads ?? 0) + 1) * 0.1;
    score += (pkg.rating ?? 0) * 0.5;

    return score;
  }

  /** Simple fuzzy matching algorithm */
  private fuzzyMatch(text: string, pattern: string): number {
    if (!pattern.length || !text.length) return 0;

    let score = 0;
    let i = 0;
    for (let j = 0; j < text.length && i < pattern.length; j++) {
      if (text[j] === pattern[i]) {
        score++;
        i++;
      }
    }
    return i === pattern.length ? score / pattern.length : 0;
  }

  /** Case-insensitive "includes" for string or string[] */
  private includesCI(value: string | string[] | undefined, needle: string): boolean {
    if (!value) return false;
    const n = needle.toLowerCase();
    return Array.isArray(value)
      ? value.some(v => (v ?? '').toLowerCase().includes(n))
      : (value ?? '').toLowerCase().includes(n);
  }

  /** Apply various filters to the package list */
  private applyFilters(packages: Package[], filters: SearchFilters): Package[] {
    return packages.filter(pkg => {
      // Type filter
      if (filters.type && pkg.type !== filters.type) return false;

      // Author filter (case-insensitive partial match)
      if (filters.author && !(pkg.author ?? '').toLowerCase().includes(filters.author.toLowerCase()))
        return false;

      // Minimum rating filter
      if (filters.minRating > 0 && (pkg.rating ?? 0) < filters.minRating) return false;

      // Compatibility filter (supports string or string[] values)
      if (filters.compatibility) {
        const comp = pkg.compatibility ?? {};
        const needle = filters.compatibility.toLowerCase();

        const hasCompatibility = Object.keys(comp).some(key => {
          const keyMatch = key.toLowerCase().includes(needle);
          const valMatch = this.includesCI(comp[key], needle);
          return keyMatch || valMatch;
        });

        if (!hasCompatibility) return false;
      }

      return true;
    });
  }

  /** Sort results based on the specified criteria */
  private sortResults(packages: Package[], filters: SearchFilters): Package[] {
    const { sortBy, sortOrder } = filters;
    const multiplier = sortOrder === 'asc' ? 1 : -1;

    return packages.sort((a, b) => {
      let comparison = 0;

      switch (sortBy) {
        case 'name':
          comparison = (a.name ?? '').localeCompare(b.name ?? '');
          break;
        case 'downloads':
          comparison = (a.downloads ?? 0) - (b.downloads ?? 0);
          break;
        case 'rating':
          comparison = (a.rating ?? 0) - (b.rating ?? 0);
          break;
        case 'updated':
          comparison = new Date(a.updated).getTime() - new Date(b.updated).getTime();
          break;
        case 'relevance':
        default:
          // For relevance, maintain the order from text search.
          // If no text search was performed, use a heuristic combo.
          // (Note: when no query, this branch will execute.)
          break;
      }

      return comparison * multiplier;
    });
  }

  /** Get search suggestions based on partial query */
  getSuggestions(query: string, limit: number = 5): string[] {
    if (!query.trim()) return [];

    const suggestions = new Set<string>();
    const q = query.toLowerCase();

    for (const pkg of this.packages) {
      if ((pkg.name ?? '').toLowerCase().startsWith(q)) suggestions.add(pkg.name);
      if ((pkg.author ?? '').toLowerCase().startsWith(q)) suggestions.add(pkg.author);
      if ((pkg.type ?? '').toLowerCase().startsWith(q)) suggestions.add(pkg.type);
      if (suggestions.size >= limit) break;
    }

    return Array.from(suggestions).slice(0, limit);
  }

  /** Get search analytics/metrics */
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
      if (pkg.author) authors.add(pkg.author);
      totalRating += pkg.rating ?? 0;
      totalDownloads += pkg.downloads ?? 0;
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
