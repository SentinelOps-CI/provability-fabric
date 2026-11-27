// SPDX-License-Identifier: Apache-2.0
//! Diagnostic only: compare the current bounded FIFO against independently
//! implemented single-thread controls under identical release workloads.
//! This is not a concurrent linearizability proof or a replacement for the
//! existing release latency gate.
use sidecar_watcher::concurrency::LockFreeRingBuffer;
use std::{
    collections::VecDeque,
    hint::black_box,
    sync::Mutex,
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
        LockFreeRingBuffer::push(self, item)
    }
    fn pop(&mut self) -> Option<usize> {
        LockFreeRingBuffer::pop(self)
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
    let names = ["production", "std_mutex", "parking_lot_reference", "sequential_control"];
    println!("implementation,allocation_state,round,push_ns,pop_ns");
    // Rotate execution order to reduce systematic ordering bias. Every
    // measurement verifies all FIFO results; every cold sample is newly allocated.
    for round in 0..ROUNDS {
        for warm in [false, true] {
            for offset in 0..names.len() {
                let kind = (round + offset + usize::from(warm)) % names.len();
                let (push, pop) = match kind {
                    0 => sample(LockFreeRingBuffer::new(CAPACITY), warm),
                    1 => sample(StdMutexQueue(Mutex::new(VecDeque::with_capacity(CAPACITY))), warm),
                    2 => sample(ParkingLotQueue(parking_lot::Mutex::new(VecDeque::with_capacity(CAPACITY))), warm),
                    3 => sample(SequentialQueue(VecDeque::with_capacity(CAPACITY)), warm),
                    _ => unreachable!(),
                };
                let state = if warm { "warm" } else { "fresh" };
                println!("{},{},{},{},{}", names[kind], state, round, push, pop);
            }
        }
    }
}
