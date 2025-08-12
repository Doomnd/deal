use std::time::Instant;

fn main() {
    // Simple arithmetic benchmark - same as Deal language
    let iterations = 100_000;
    let start = Instant::now();
    
    for _ in 0..iterations {
        let mut acc = 0;
        acc = acc + 1;
        acc = acc + 2;
        acc = acc + 3;
        acc = acc + 4;
        acc = acc + 5;
        acc = acc + 6;
        acc = acc + 7;
        acc = acc + 8;
        acc = acc + 9;
        acc = acc + 10;
        // Prevent optimization
        if acc != 55 {
            println!("Error: expected 55, got {}", acc);
        }
    }
    
    let dur = start.elapsed();
    println!("Rust: {} iterations in {:?} ({:.2} ops/sec)", 
             iterations, dur, 
             (iterations as f64) / dur.as_secs_f64());
}
