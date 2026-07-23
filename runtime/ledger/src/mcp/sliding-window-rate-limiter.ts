/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 *
 * In-memory sliding-window rate limiter for MCP proxy.
 *
 * Caveat: this is single-node only. Timestamps live in process memory and are
 * not shared across replicas. Multi-instance deployments need a coordinated
 * store (e.g. Redis) before relying on these limits for global enforcement.
 */

export interface SlidingWindowLimit {
  /** Maximum allowed acquisitions inside the window. */
  requests: number;
  /** Window length in milliseconds. */
  windowMs: number;
}

export type NowFn = () => number;

export class SlidingWindowRateLimiter {
  private readonly windows = new Map<string, number[]>();
  private readonly nowFn: NowFn;

  constructor(nowFn: NowFn = () => Date.now()) {
    this.nowFn = nowFn;
  }

  /**
   * Attempt to acquire a slot for `key` (typically `tenant:method`).
   * Returns true when allowed, false when the sliding window is full.
   */
  tryAcquire(key: string, limit: SlidingWindowLimit): boolean {
    if (limit.requests <= 0 || limit.windowMs <= 0) {
      return false;
    }

    const now = this.nowFn();
    const cutoff = now - limit.windowMs;
    let stamps = this.windows.get(key) ?? [];
    stamps = stamps.filter((t) => t > cutoff);

    if (stamps.length >= limit.requests) {
      this.windows.set(key, stamps);
      return false;
    }

    stamps.push(now);
    this.windows.set(key, stamps);
    return true;
  }

  /** Current in-window count for a key (after pruning). */
  currentCount(key: string, windowMs: number): number {
    const now = this.nowFn();
    const cutoff = now - windowMs;
    const stamps = (this.windows.get(key) ?? []).filter((t) => t > cutoff);
    this.windows.set(key, stamps);
    return stamps.length;
  }

  reset(): void {
    this.windows.clear();
  }
}

export default SlidingWindowRateLimiter;
