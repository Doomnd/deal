use std::cell::UnsafeCell;
use std::mem::MaybeUninit;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::{Acquire, Relaxed, Release}};
use crossbeam_utils::sync::Parker;
use std::sync::Arc;
use std::thread;

#[repr(align(64))]
struct Pad([u8; 64]);

pub struct SpscRing<T> {
    buffer: Box<[UnsafeCell<MaybeUninit<T>>]>,
    mask: usize,

    _pad0: Pad,
    head: AtomicUsize, // consumer index
    _pad1: Pad,
    tail: AtomicUsize, // producer index
    _pad2: Pad,

    // Simple park/wake: consumer parks when empty, producer wakes; and vice versa when full
    prod_waiting: AtomicBool,
    cons_waiting: AtomicBool,
    prod_parker: Parker,
    cons_parker: Parker,
}

unsafe impl<T: Send> Send for SpscRing<T> {}
unsafe impl<T: Send> Sync for SpscRing<T> {}

impl<T> SpscRing<T> {
    pub fn with_capacity(capacity: usize) -> Self {
        assert!(capacity.is_power_of_two(), "capacity must be power of two");
        let mut v = Vec::with_capacity(capacity);
        for _ in 0..capacity { v.push(UnsafeCell::new(MaybeUninit::<T>::uninit())); }
        Self {
            buffer: v.into_boxed_slice(),
            mask: capacity - 1,
            _pad0: Pad([0; 64]), head: AtomicUsize::new(0),
            _pad1: Pad([0; 64]), tail: AtomicUsize::new(0),
            _pad2: Pad([0; 64]),
            prod_waiting: AtomicBool::new(false),
            cons_waiting: AtomicBool::new(false),
            prod_parker: Parker::new(),
            cons_parker: Parker::new(),
        }
    }

    #[inline]
    pub fn capacity(&self) -> usize { self.mask + 1 }

    #[inline]
    pub fn len(&self) -> usize {
        let head = self.head.load(Relaxed);
        let tail = self.tail.load(Relaxed);
        tail.wrapping_sub(head)
    }

    #[inline]
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    pub fn push(&self, value: T) -> Result<(), T> {
        let capacity = self.capacity();
        let mut spins = 0u32;
        loop {
            let tail = self.tail.load(Relaxed);
            let head = self.head.load(Acquire);
            if tail.wrapping_sub(head) != capacity {
                let idx = tail & self.mask;
                unsafe { (*self.buffer[idx].get()).write(value); }
                self.tail.store(tail.wrapping_add(1), Release);
                // Wake consumer if needed
                if self.cons_waiting.swap(false, Relaxed) { self.cons_parker.unparker().unpark(); }
                return Ok(());
            }
            // queue full
            if spins < 100 { spins += 1; std::hint::spin_loop(); continue; }
            self.prod_waiting.store(true, Relaxed);
            self.prod_parker.park_timeout(std::time::Duration::from_micros(50));
        }
    }

    pub fn pop(&self) -> Option<T> {
        let mut spins = 0u32;
        loop {
            let head = self.head.load(Relaxed);
            let tail = self.tail.load(Acquire);
            if head != tail {
                let idx = head & self.mask;
                let value = unsafe { (*self.buffer[idx].get()).assume_init_read() };
                self.head.store(head.wrapping_add(1), Release);
                // Wake producer if needed
                if self.prod_waiting.swap(false, Relaxed) { self.prod_parker.unparker().unpark(); }
                return Some(value);
            }
            // empty
            if spins < 100 { spins += 1; std::hint::spin_loop(); continue; }
            self.cons_waiting.store(true, Relaxed);
            self.cons_parker.park_timeout(std::time::Duration::from_micros(50));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn smoke() {
        let q = Arc::new(SpscRing::<usize>::with_capacity(1024));
        let p = q.clone();
        let t_prod = std::thread::spawn(move || {
            for i in 0..100_000usize { while p.push(i).is_err() { std::hint::spin_loop(); } }
        });
        let t_cons = std::thread::spawn(move || {
            let mut next = 0usize;
            while next < 100_000 {
                if let Some(v) = q.pop() { assert_eq!(v, next); next += 1; } else { std::hint::spin_loop(); }
            }
        });
        t_prod.join().unwrap();
        t_cons.join().unwrap();
    }
}


