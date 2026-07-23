/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

import winston from 'winston';
import { SlidingWindowRateLimiter } from './sliding-window-rate-limiter';
import { JCSValidator } from './jcs-validator';

function silentLogger(): winston.Logger {
  return winston.createLogger({
    silent: true,
    transports: [new winston.transports.Console()],
  });
}

describe('SlidingWindowRateLimiter', () => {
  beforeEach(() => {
    jest.useFakeTimers();
    jest.setSystemTime(new Date('2026-07-22T12:00:00.000Z'));
  });

  afterEach(() => {
    jest.useRealTimers();
  });

  it('denies after N acquisitions in the same window', () => {
    const limiter = new SlidingWindowRateLimiter(() => Date.now());
    const key = 'tenant-a:tools/list';
    const limit = { requests: 3, windowMs: 60_000 };

    expect(limiter.tryAcquire(key, limit)).toBe(true);
    expect(limiter.tryAcquire(key, limit)).toBe(true);
    expect(limiter.tryAcquire(key, limit)).toBe(true);
    expect(limiter.tryAcquire(key, limit)).toBe(false);
    expect(limiter.currentCount(key, limit.windowMs)).toBe(3);
  });

  it('isolates keys by tenant:method', () => {
    const limiter = new SlidingWindowRateLimiter(() => Date.now());
    const limit = { requests: 1, windowMs: 60_000 };

    expect(limiter.tryAcquire('tenant-a:tools/list', limit)).toBe(true);
    expect(limiter.tryAcquire('tenant-a:tools/list', limit)).toBe(false);
    expect(limiter.tryAcquire('tenant-b:tools/list', limit)).toBe(true);
    expect(limiter.tryAcquire('tenant-a:tools/call', limit)).toBe(true);
  });

  it('allows new acquisitions after sliding-window rollover', () => {
    const limiter = new SlidingWindowRateLimiter(() => Date.now());
    const key = 'tenant-a:tools/list';
    const limit = { requests: 2, windowMs: 60_000 };

    expect(limiter.tryAcquire(key, limit)).toBe(true);
    expect(limiter.tryAcquire(key, limit)).toBe(true);
    expect(limiter.tryAcquire(key, limit)).toBe(false);

    jest.advanceTimersByTime(60_001);

    expect(limiter.tryAcquire(key, limit)).toBe(true);
    expect(limiter.tryAcquire(key, limit)).toBe(true);
    expect(limiter.tryAcquire(key, limit)).toBe(false);
  });

  it('prunes only timestamps that fall outside the window', () => {
    const limiter = new SlidingWindowRateLimiter(() => Date.now());
    const key = 'tenant-a:resources/read';
    const limit = { requests: 2, windowMs: 10_000 };

    expect(limiter.tryAcquire(key, limit)).toBe(true);
    jest.advanceTimersByTime(5_000);
    expect(limiter.tryAcquire(key, limit)).toBe(true);
    expect(limiter.tryAcquire(key, limit)).toBe(false);

    jest.advanceTimersByTime(5_001);
    expect(limiter.currentCount(key, limit.windowMs)).toBe(1);
    expect(limiter.tryAcquire(key, limit)).toBe(true);
    expect(limiter.tryAcquire(key, limit)).toBe(false);
  });
});

describe('JCSValidator cache hit rate', () => {
  it('reports zero hit rate before validation', () => {
    const validator = new JCSValidator(silentLogger());
    expect(validator.getStats().cacheHitRate).toBe(0);
    expect(validator.getStats().cacheHits).toBe(0);
    expect(validator.getStats().cacheMisses).toBe(0);
  });

  it('computes hit rate after a warm cache', () => {
    const validator = new JCSValidator(silentLogger());
    const schema = validator.getSchema('tool_call');
    expect(schema).not.toBeNull();

    const input = { name: 'echo', arguments: { text: 'hi' } };
    const first = validator.validateInput(input, schema!);
    const second = validator.validateInput(input, schema!);
    const third = validator.validateInput(input, schema!);

    expect(first.valid).toBe(true);
    expect(second).toEqual(first);
    expect(third).toEqual(first);

    const stats = validator.getStats();
    expect(stats.cacheMisses).toBe(1);
    expect(stats.cacheHits).toBe(2);
    expect(stats.cacheSize).toBe(1);
    expect(stats.cacheHitRate).toBeCloseTo(2 / 3);
  });

  it('retains hit/miss counters after clearCache', () => {
    const validator = new JCSValidator(silentLogger());
    const schema = validator.getSchema('tool_call')!;
    const input = { name: 'echo', arguments: {} };

    validator.validateInput(input, schema);
    validator.validateInput(input, schema);
    validator.clearCache();

    const stats = validator.getStats();
    expect(stats.cacheSize).toBe(0);
    expect(stats.cacheMisses).toBe(1);
    expect(stats.cacheHits).toBe(1);
    expect(stats.cacheHitRate).toBeCloseTo(0.5);
  });
});
