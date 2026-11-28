// SPDX-License-Identifier: Apache-2.0
//! Diagnostic only: compare the current bounded FIFO against independently
//! implemented controls and a bounded concurrent candidate under identical release workloads.
//! This is not a concurrent linearizability proof or a replacement for the
//! existing release latency gate.
use crossbeam_queue::ArrayQueue;
use sidecar_watcher::concurrency::LockFreeRingBuffer;
use std::{
    collections::VecDeque,
    hint::black_box,
    sync::{mpsc, Arc, Mutex},
    thread,
    time::{Duration, Instant},
};

const OPERATIONS: usize = 100_000;
const ROUNDS: usize = 31;
const CAPACITY: usize = 131_072;
const LIMIT: usize = CAPACITY - 1;

trait Queue {
    fn push(&mut self, item: usize) -> Result<(), usize>;
    fn pop(&mut self) -> Option<usize>;
}

impl Queue for LockFreeRingBuffer<usize> {
    fn push(&mut self, item: usize) -> Result<(), usize> {
        LockFreeRingBuffer::push(black_box(&*self), item)
    }
    fn pop(&mut self) -> Option<usize> {
        LockFreeRingBuffer::pop(black_box(&*self))
    }
}

struct StdMutexQueue(Mutex<VecDeque<usize>>);
impl Queue for StdMutexQueue {
    fn push(&mut self, item: usize) -> Result<(), usize> {
        // Lock through a shared reference; do not optimize away locking with get_mut.
        let mut queue = black_box(&self.0).lock().expect("fixture lock");
        if queue.len() >= LIMIT {
            Err(item)
        } else {
            queue.push_back(item);
            Ok(())
        }
    }
    fn pop(&mut self) -> Option<usize> {
        black_box(&self.0).lock().expect("fixture lock").pop_front()
    }
}

struct ParkingLotQueue(parking_lot::Mutex<VecDeque<usize>>);
impl Queue for ParkingLotQueue {
    fn push(&mut self, item: usize) -> Result<(), usize> {
        let mut queue = black_box(&self.0).lock();
        if queue.len() >= LIMIT {
            Err(item)
        } else {
            queue.push_back(item);
            Ok(())
        }
    }
    fn pop(&mut self) -> Option<usize> {
        black_box(&self.0).lock().pop_front()
    }
}

// Development-only adapter. Preserve the historical rounded slot count and
// reserved slot by constructing the queue with the usable capacity. ArrayQueue
// rejects zero capacity, so the unusable cases are represented explicitly.
// No concurrent size-snapshot or progress guarantee is inferred from this adapter.
struct ArrayQueueCandidate<T> {
    queue: Option<ArrayQueue<T>>,
}

impl<T> ArrayQueueCandidate<T> {
    fn new(slots: usize) -> Self {
        let limit = slots.next_power_of_two() - 1;
        Self { queue: (limit != 0).then(|| ArrayQueue::new(limit)) }
    }

    fn push_shared(&self, item: T) -> Result<(), T> {
        match &self.queue {
            Some(queue) => queue.push(item),
            None => Err(item),
        }
    }

    fn pop_shared(&self) -> Option<T> {
        self.queue.as_ref().and_then(ArrayQueue::pop)
    }

    fn len_quiescent(&self) -> usize {
        self.queue.as_ref().map_or(0, ArrayQueue::len)
    }
}

impl Queue for ArrayQueueCandidate<usize> {
    fn push(&mut self, item: usize) -> Result<(), usize> {
        black_box(&*self).push_shared(item)
    }

    fn pop(&mut self) -> Option<usize> {
        black_box(&*self).pop_shared()
    }
}

fn validate_candidate() {
    // Independent list model: all 10-operation push/pop schedules at six
    // configured capacities, including zero usable slots and wraparound.
    for slots in [0usize, 1, 2, 3, 8, 17] {
        let limit = slots.next_power_of_two() - 1;
        for trace in 0u16..1024 {
            let queue = ArrayQueueCandidate::new(slots);
            let mut model = Vec::new();
            for step in 0..10 {
                if trace & (1 << step) != 0 {
                    let expected = if model.len() == limit {
                        Err(step)
                    } else {
                        model.push(step);
                        Ok(())
                    };
                    assert_eq!(queue.push_shared(step), expected);
                } else {
                    let expected = if model.is_empty() { None } else { Some(model.remove(0)) };
                    assert_eq!(queue.pop_shared(), expected);
                }
                assert_eq!(queue.len_quiescent(), model.len());
            }
        }
    }

    // Ownership transfer on success, rejection, consumption and queue drop.
    let queue = ArrayQueueCandidate::new(2);
    let value = Arc::new(());
    queue.push_shared(value.clone()).unwrap();
    let rejected = queue.push_shared(value.clone()).unwrap_err();
    assert!(Arc::ptr_eq(&value, &rejected));
    drop(rejected);
    let returned = queue.pop_shared().unwrap();
    assert!(Arc::ptr_eq(&value, &returned));
    drop(returned);
    assert_eq!(Arc::strong_count(&value), 1);
    queue.push_shared(value.clone()).unwrap();
    drop(queue);
    assert_eq!(Arc::strong_count(&value), 1);

    // Concurrent producer order and exactly-once delivery in a bounded workload.
    // A timeout prevents a lost-item regression from hanging the experiment.
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let queue = Arc::new(ArrayQueueCandidate::new(32));
        let mut producers = Vec::new();
        for producer in 0..4usize {
            let queue = Arc::clone(&queue);
            producers.push(thread::spawn(move || {
                for item in 0..1000 {
                    let mut value = producer * 1000 + item;
                    loop {
                        match queue.push_shared(value) {
                            Ok(()) => break,
                            Err(returned) => {
                                value = returned;
                                thread::yield_now();
                            }
                        }
                    }
                }
            }));
        }
        let mut next = [0usize; 4];
        for _ in 0..4000 {
            let value = loop {
                if let Some(value) = queue.pop_shared() {
                    break value;
                }
                thread::yield_now();
            };
            let producer = value / 1000;
            assert!(producer < next.len());
            assert_eq!(value % 1000, next[producer]);
            next[producer] += 1;
        }
        for producer in producers {
            producer.join().unwrap();
        }
        assert_eq!(next, [1000; 4]);
        assert_eq!(queue.pop_shared(), None);
        assert_eq!(queue.len_quiescent(), 0);
        tx.send(()).unwrap();
    });
    rx.recv_timeout(Duration::from_secs(10))
        .expect("candidate concurrent delivery failed or timed out");
    eprintln!("PASS: 6144 bounded traces, ownership checks, 4000 concurrent producer deliveries");
}

// Uncontended sequential lower-overhead control, not a thread-safe candidate.
struct SequentialQueue(VecDeque<usize>);
impl Queue for SequentialQueue {
    fn push(&mut self, item: usize) -> Result<(), usize> {
        if self.0.len() >= LIMIT {
            Err(item)
        } else {
            self.0.push_back(item);
            Ok(())
        }
    }
    fn pop(&mut self) -> Option<usize> {
        self.0.pop_front()
    }
}

fn exercise<Q: Queue>(queue: &mut Q) -> (Duration, Duration) {
    let start = Instant::now();
    for item in 0..OPERATIONS {
        assert_eq!(queue.push(black_box(item)), Ok(()));
    }
    let push = start.elapsed();
    let start = Instant::now();
    for expected in 0..OPERATIONS {
        assert_eq!(black_box(queue.pop()), Some(expected));
    }
    let pop = start.elapsed();
    assert_eq!(queue.pop(), None);
    (push, pop)
}

fn sample<Q: Queue>(mut queue: Q, warm: bool) -> (u128, u128) {
    if warm {
        let _ = exercise(&mut queue);
    }
    let (push, pop) = exercise(&mut queue);
    (push.as_nanos(), pop.as_nanos())
}

fn main() {
    assert!(!cfg!(debug_assertions), "execute this diagnostic in release mode");
    validate_candidate();
    let names = ["production", "std_mutex", "parking_lot_reference", "sequential_control", "crossbeam_arrayqueue"];
    println!("implementation,allocation_state,round,push_ns,pop_ns");
    // Rotate execution order to reduce systematic ordering bias. Every
    // measurement verifies all FIFO results; every cold sample is newly allocated.
    for round in 0..ROUNDS {
        for warm in [false, true] {
            for offset in 0..names.len() {
                let kind = (round + offset + if warm { 1 } else { 0 }) % names.len();
                let (push, pop) = match kind {
                    0 => sample(LockFreeRingBuffer::new(CAPACITY), warm),
                    1 => sample(StdMutexQueue(Mutex::new(VecDeque::with_capacity(CAPACITY))), warm),
                    2 => sample(ParkingLotQueue(parking_lot::Mutex::new(VecDeque::with_capacity(CAPACITY))), warm),
                    3 => sample(SequentialQueue(VecDeque::with_capacity(CAPACITY)), warm),
                    4 => sample(ArrayQueueCandidate::new(CAPACITY), warm),
                    _ => unreachable!(),
                };
                let state = if warm { "warm" } else { "fresh" };
                println!("{},{},{},{},{}", names[kind], state, round, push, pop);
            }
        }
    }
}
