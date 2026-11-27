/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use arc_swap::ArcSwap;
use parking_lot::{Mutex, RwLock};
use std::collections::VecDeque;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc;
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

/// Bounded mutex-protected FIFO (legacy type name).
///
/// Preserve the historical power-of-two slot capacity and one reserved slot.
/// Ownership moves out on pop; unused slots never retain consumed events.
pub struct LockFreeRingBuffer<T> {
    buffer: Mutex<VecDeque<T>>,
    capacity: usize,
}

impl<T: Default + Clone> LockFreeRingBuffer<T> {
    /// Create a ring buffer with power-of-two storage capacity.
    pub fn new(capacity: usize) -> Self {
        let actual_capacity = capacity.next_power_of_two();
        Self {
            buffer: Mutex::new(VecDeque::with_capacity(actual_capacity)),
            capacity: actual_capacity,
        }
    }

    /// Report configured buffer capacity, including the reserved slot.
    pub fn slot_capacity(&self) -> usize {
        self.capacity
    }

    /// Enqueue an item, returning ownership unchanged if the queue is full.
    #[inline(always)]
    pub fn push(&self, item: T) -> Result<(), T> {
        let mut buffer = self.buffer.lock();
        if buffer.len() >= self.capacity - 1 {
            return Err(item);
        }
        buffer.push_back(item);
        Ok(())
    }

    /// Remove the oldest item, transferring ownership to the consumer.
    #[inline(always)]
    pub fn pop(&self) -> Option<T> {
        self.buffer.lock().pop_front()
    }

    /// Exact size at the point of lock acquisition.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.buffer.lock().len()
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.buffer.lock().is_empty()
    }

    #[inline(always)]
    pub fn is_full(&self) -> bool {
        self.buffer.lock().len() >= self.capacity - 1
    }
}

/// Event ingress using a bounded mutex-protected FIFO.
pub struct EventIngress<T> {
    ring_buffer: Arc<LockFreeRingBuffer<T>>,
    worker_handles: Vec<thread::JoinHandle<()>>,
    shutdown_flag: Arc<std::sync::atomic::AtomicBool>,
}

impl<T: Default + Clone + Send + 'static> EventIngress<T> {
    /// Create new event ingress with worker threads
    pub fn new(capacity: usize, worker_count: usize) -> Self {
        let ring_buffer = Arc::new(LockFreeRingBuffer::new(capacity));
        let mut worker_handles = Vec::new();

        // Create a shared shutdown flag instead of cloning the receiver
        let shutdown_flag = Arc::new(std::sync::atomic::AtomicBool::new(false));

        for worker_id in 0..worker_count {
            let ring_buffer = Arc::clone(&ring_buffer);
            let shutdown_flag = Arc::clone(&shutdown_flag);

            let handle = thread::spawn(move || {
                Self::worker_loop_with_flag(worker_id, ring_buffer, shutdown_flag);
            });

            worker_handles.push(handle);
        }

        Self {
            ring_buffer,
            worker_handles,
            shutdown_flag,
        }
    }

    /// Submit event for processing (hot path)
    #[inline(always)]
    pub fn submit_event(&self, event: T) -> Result<(), T> {
        self.ring_buffer.push(event)
    }

    /// Get current queue size
    pub fn queue_size(&self) -> usize {
        self.ring_buffer.len()
    }

    /// Check if queue is full
    pub fn is_full(&self) -> bool {
        self.ring_buffer.is_full()
    }

    /// Shutdown event ingress
    pub fn shutdown(self) -> Result<(), Box<dyn std::error::Error>> {
        // Set shutdown flag
        self.shutdown_flag
            .store(true, std::sync::atomic::Ordering::Relaxed);

        // Wait for all workers to finish
        for handle in self.worker_handles {
            let _ = handle.join();
        }

        Ok(())
    }

    /// Worker loop for processing events with shutdown flag
    fn worker_loop_with_flag(
        worker_id: usize,
        ring_buffer: Arc<LockFreeRingBuffer<T>>,
        shutdown_flag: Arc<std::sync::atomic::AtomicBool>,
    ) {
        let mut processed_count = 0;
        let mut last_yield_time = Instant::now();

        loop {
            // Check for shutdown signal
            if shutdown_flag.load(std::sync::atomic::Ordering::Relaxed) {
                break;
            }

            // Process events from ring buffer
            let mut batch_count = 0;
            while let Some(_event) = ring_buffer.pop() {
                // Process the event here
                // For now, just count it
                batch_count += 1;
                processed_count += 1;

                // Yield periodically to avoid starving other threads
                if batch_count >= 100 || last_yield_time.elapsed() >= Duration::from_micros(50) {
                    thread::yield_now();
                    last_yield_time = Instant::now();
                    batch_count = 0;
                }
            }

            // If no events, yield to avoid busy waiting
            if batch_count == 0 {
                thread::yield_now();
            }
        }

        println!("Worker {} processed {} events", worker_id, processed_count);
    }
}

/// Epoch-based policy management with ArcSwap
pub struct EpochPolicyManager<T> {
    current_policy: ArcSwap<T>,
    epoch: AtomicUsize,
    update_notify: Arc<RwLock<Vec<mpsc::Sender<()>>>>,
}

impl<T: Clone> EpochPolicyManager<T> {
    /// Create new epoch policy manager
    pub fn new(initial_policy: T) -> Self {
        Self {
            current_policy: ArcSwap::new(Arc::new(initial_policy)),
            epoch: AtomicUsize::new(0),
            update_notify: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// Get current policy (lock-free read)
    #[inline(always)]
    pub fn get_policy(&self) -> Arc<T> {
        self.current_policy.load().clone()
    }

    /// Update policy with new epoch (atomic)
    pub fn update_policy(&self, new_policy: T) -> usize {
        let new_epoch = self.epoch.fetch_add(1, Ordering::SeqCst) + 1;
        self.current_policy.store(Arc::new(new_policy));

        // Notify all subscribers
        let notify_list = self.update_notify.read();
        for sender in notify_list.iter() {
            let _ = sender.send(());
        }

        new_epoch
    }

    /// Subscribe to policy updates
    pub fn subscribe(&self) -> mpsc::Receiver<()> {
        let (tx, rx) = mpsc::channel();
        let mut notify_list = self.update_notify.write();
        notify_list.push(tx);
        rx
    }

    /// Get current epoch
    pub fn current_epoch(&self) -> usize {
        self.epoch.load(Ordering::SeqCst)
    }
}

type BucketEntries<K, V> = Vec<(K, V)>;

/// High-performance concurrent hash map with lock-free reads
pub struct LockFreeHashMap<K, V> {
    buckets: Vec<Arc<RwLock<BucketEntries<K, V>>>>,
    bucket_count: usize,
    mask: usize,
}

impl<K: Clone + PartialEq, V: Clone> LockFreeHashMap<K, V> {
    /// Create new lock-free hash map
    pub fn new(capacity: usize) -> Self {
        let bucket_count = capacity.next_power_of_two();
        let buckets = (0..bucket_count)
            .map(|_| Arc::new(RwLock::new(Vec::new())))
            .collect();

        Self {
            buckets,
            bucket_count,
            mask: bucket_count - 1,
        }
    }

    /// Number of hash buckets backing this map.
    pub fn bucket_count(&self) -> usize {
        self.bucket_count
    }

    /// Get value by key (lock-free read)
    #[inline(always)]
    pub fn get(&self, key: &K) -> Option<V> {
        let bucket_index = self.hash_key(key) & self.mask;
        let bucket = &self.buckets[bucket_index];
        let bucket_guard = bucket.read();

        for (k, v) in bucket_guard.iter() {
            if k == key {
                return Some(v.clone());
            }
        }

        None
    }

    /// Insert key-value pair
    pub fn insert(&self, key: K, value: V) {
        let bucket_index = self.hash_key(&key) & self.mask;
        let bucket = &self.buckets[bucket_index];
        let mut bucket_guard = bucket.write();

        // Check if key already exists
        for (k, v) in bucket_guard.iter_mut() {
            if k == &key {
                *v = value;
                return;
            }
        }

        // Add new entry
        bucket_guard.push((key, value));
    }

    /// Remove key-value pair
    pub fn remove(&self, key: &K) -> Option<V> {
        let bucket_index = self.hash_key(key) & self.mask;
        let bucket = &self.buckets[bucket_index];
        let mut bucket_guard = bucket.write();

        for (i, (k, v)) in bucket_guard.iter().enumerate() {
            if k == key {
                let value = v.clone();
                bucket_guard.remove(i);
                return Some(value);
            }
        }

        None
    }

    /// Hash key to bucket index
    #[inline(always)]
    fn hash_key(&self, key: &K) -> usize {
        // Simple hash function - in production would use a proper hash
        std::ptr::addr_of!(key) as usize
    }
}

/// Performance metrics for concurrency operations
#[derive(Debug, Default)]
pub struct ConcurrencyMetrics {
    pub events_processed: AtomicUsize,
    pub events_dropped: AtomicUsize,
    pub average_processing_time: AtomicUsize, // in microseconds
    pub queue_size: AtomicUsize,
    pub policy_updates: AtomicUsize,
}

impl ConcurrencyMetrics {
    /// Record event processing
    pub fn record_event_processed(&self, processing_time: Duration) {
        self.events_processed.fetch_add(1, Ordering::Relaxed);
        let time_us = processing_time.as_micros() as usize;
        self.average_processing_time
            .store(time_us, Ordering::Relaxed);
    }

    /// Record dropped event
    pub fn record_event_dropped(&self) {
        self.events_dropped.fetch_add(1, Ordering::Relaxed);
    }

    /// Record policy update
    pub fn record_policy_update(&self) {
        self.policy_updates.fetch_add(1, Ordering::Relaxed);
    }

    /// Get metrics snapshot
    pub fn snapshot(&self) -> ConcurrencyMetricsSnapshot {
        ConcurrencyMetricsSnapshot {
            events_processed: self.events_processed.load(Ordering::Relaxed),
            events_dropped: self.events_dropped.load(Ordering::Relaxed),
            average_processing_time: self.average_processing_time.load(Ordering::Relaxed),
            queue_size: self.queue_size.load(Ordering::Relaxed),
            policy_updates: self.policy_updates.load(Ordering::Relaxed),
        }
    }
}

/// Snapshot of concurrency metrics
#[derive(Debug, Clone)]
pub struct ConcurrencyMetricsSnapshot {
    pub events_processed: usize,
    pub events_dropped: usize,
    pub average_processing_time: usize,
    pub queue_size: usize,
    pub policy_updates: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;
    use std::time::Duration;

    #[test]
    fn test_lock_free_ring_buffer() {
        let buffer = LockFreeRingBuffer::new(8);

        // Test basic operations
        assert!(buffer.is_empty());
        assert!(!buffer.is_full());

        // Push items
        for i in 0..7 {
            assert!(buffer.push(i).is_ok());
        }

        assert!(!buffer.is_empty());
        assert!(buffer.is_full());

        // Try to push when full
        assert!(buffer.push(99).is_err());

        // Pop items
        for i in 0..7 {
            assert_eq!(buffer.pop(), Some(i));
        }

        assert!(buffer.is_empty());
        assert_eq!(buffer.pop(), None);
    }

    #[test]
    fn test_ring_buffer_exhaustive_bounded_traces() {
        // Compare with an independent sequential list model, including the
        // historical unusable reserved-slot capacities zero and one.
        for capacity in [0usize, 1, 2, 3, 8, 17] {
            for trace in 0u16..1024 {
                let queue = LockFreeRingBuffer::new(capacity);
                let limit = capacity.next_power_of_two() - 1;
                let mut model = Vec::new();
                for step in 0..10 {
                    if trace & (1 << step) != 0 {
                        if model.len() == limit {
                            assert_eq!(queue.push(step), Err(step));
                        } else {
                            model.push(step);
                            assert_eq!(queue.push(step), Ok(()));
                        }
                    } else {
                        let expected = if model.is_empty() { None } else { Some(model.remove(0)) };
                        assert_eq!(queue.pop(), expected);
                    }
                    assert_eq!(queue.len(), model.len());
                    assert_eq!(queue.is_empty(), model.is_empty());
                    assert_eq!(queue.is_full(), model.len() == limit);
                }
            }
        }
    }

    #[test]
    fn test_ring_buffer_transfers_ownership_on_pop() {
        let queue = LockFreeRingBuffer::new(2);
        let value = Arc::new(());
        queue.push(value.clone()).unwrap();
        assert_eq!(Arc::strong_count(&value), 2);
        let returned = queue.pop().unwrap();
        assert!(Arc::ptr_eq(&value, &returned));
        drop(returned);
        assert_eq!(Arc::strong_count(&value), 1);
        queue.push(value.clone()).unwrap();
        let rejected = queue.push(value.clone()).unwrap_err();
        drop(rejected);
        assert_eq!(Arc::strong_count(&value), 2);
        drop(queue);
        assert_eq!(Arc::strong_count(&value), 1);
    }

    #[test]
    fn test_concurrent_ring_buffer() {
        use std::sync::mpsc;

        let buffer = Arc::new(LockFreeRingBuffer::new(1024));
        let (done_tx, done_rx) = mpsc::channel();

        thread::spawn(move || {
            let mut handles = Vec::new();

            // Spawn producer threads
            for thread_id in 0..4 {
                let buffer = Arc::clone(&buffer);
                let handle = thread::spawn(move || {
                    for i in 0..1000 {
                        let value = thread_id * 1000 + i;
                        while buffer.push(value).is_err() {
                            thread::yield_now();
                        }
                    }
                });
                handles.push(handle);
            }

            // Spawn consumer thread
            let buffer_clone = Arc::clone(&buffer);
            let consumer_handle = thread::spawn(move || {
                let mut values = Vec::with_capacity(4000);
                while values.len() < 4000 {
                    if let Some(value) = buffer_clone.pop() {
                        values.push(value);
                    } else {
                        thread::yield_now();
                    }
                }
                values
            });

            for handle in handles {
                handle.join().unwrap();
            }

            let consumed = consumer_handle.join().unwrap();
            let _ = done_tx.send(consumed);
        });

        let consumed = done_rx
            .recv_timeout(Duration::from_secs(10))
            .expect("concurrent ring buffer hung (likely lost items under MPMC race)");
        let mut expected = [0; 4];
        for &value in &consumed {
            let producer = value / 1000;
            assert!(producer < 4);
            assert_eq!(value % 1000, expected[producer]);
            expected[producer] += 1;
        }
        assert_eq!(expected, [1000; 4]);
        let mut sorted = consumed;
        sorted.sort_unstable();
        assert_eq!(sorted, (0..4000).collect::<Vec<_>>());
    }

    #[test]
    fn test_epoch_policy_manager() {
        let manager = EpochPolicyManager::new("initial_policy".to_string());

        // Test initial policy
        let policy = manager.get_policy();
        assert_eq!(*policy, "initial_policy");
        assert_eq!(manager.current_epoch(), 0);

        // Test policy update
        let epoch = manager.update_policy("updated_policy".to_string());
        assert_eq!(epoch, 1);

        let policy = manager.get_policy();
        assert_eq!(*policy, "updated_policy");
        assert_eq!(manager.current_epoch(), 1);
    }

    #[test]
    fn test_lock_free_hash_map() {
        let map = LockFreeHashMap::new(16);

        // Test insert and get
        map.insert("key1".to_string(), "value1".to_string());
        map.insert("key2".to_string(), "value2".to_string());

        assert_eq!(map.get(&"key1".to_string()), Some("value1".to_string()));
        assert_eq!(map.get(&"key2".to_string()), Some("value2".to_string()));
        assert_eq!(map.get(&"key3".to_string()), None);

        // Test update
        map.insert("key1".to_string(), "updated_value1".to_string());
        assert_eq!(
            map.get(&"key1".to_string()),
            Some("updated_value1".to_string())
        );

        // Test remove
        assert_eq!(
            map.remove(&"key1".to_string()),
            Some("updated_value1".to_string())
        );
        assert_eq!(map.get(&"key1".to_string()), None);
    }

    #[test]
    fn test_event_ingress() {
        let ingress = EventIngress::new(100, 2);

        // Submit events
        for i in 0..50 {
            assert!(ingress.submit_event(i).is_ok());
        }

        // Wait a bit for processing
        thread::sleep(Duration::from_millis(100));

        // Shutdown
        ingress.shutdown().unwrap();
    }

    #[test]
    fn test_performance_benchmark() {
        // Capacity must exceed push count: single-threaded push cannot drain while filling.
        let buffer = Arc::new(LockFreeRingBuffer::new(100_000));

        // Benchmark push operations
        let start = Instant::now();
        for i in 0..100_000 {
            assert!(buffer.push(std::hint::black_box(i)).is_ok());
        }
        let push_duration = start.elapsed();

        // Benchmark pop operations
        let start = Instant::now();
        for expected in 0..100_000 {
            assert_eq!(std::hint::black_box(buffer.pop()), Some(expected));
        }
        let pop_duration = start.elapsed();
        assert!(buffer.is_empty());

        // Keep the original threshold in the dedicated optimized CI gate.
        if !cfg!(debug_assertions) {
            assert!(push_duration.as_millis() < 1, "Push too slow: {:?}", push_duration);
            assert!(pop_duration.as_millis() < 1, "Pop too slow: {:?}", pop_duration);
        }

        println!("100k push operations: {:?}", push_duration);
        println!("100k pop operations: {:?}", pop_duration);
    }
}
