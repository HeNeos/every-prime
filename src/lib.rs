use once_cell::sync::Lazy;
use primal_check::miller_rabin;
use std::sync::Mutex;
use wasm_bindgen::prelude::*;

const SIEVE_LIMIT: usize = 1_000_000;

struct SieveData {
    is_prime: Vec<bool>,
    primes: Vec<u64>,
    prime_pi: Vec<usize>, // prime_pi[n] = number of primes <= n
}

impl SieveData {
    fn new(limit: usize) -> Self {
        let mut is_prime = vec![true; limit + 1];
        let mut primes = Vec::new();
        let mut prime_pi = vec![0; limit + 1];

        is_prime[0] = false;
        if limit > 0 {
            is_prime[1] = false;
        }

        for i in 2..=limit {
            if is_prime[i] {
                primes.push(i as u64);
                let mut j = i as u64 * i as u64;
                while j <= limit as u64 {
                    is_prime[j as usize] = false;
                    j += i as u64;
                }
            }
            // prime_pi[n] = prime_pi[n-1] + 1 if n is prime, else same as previous
            prime_pi[i] = prime_pi[i - 1] + if is_prime[i] { 1 } else { 0 };
        }

        SieveData {
            is_prime,
            primes,
            prime_pi,
        }
    }
}

struct PrimeState {
    sieve: SieveData,
    // For larger primes, store as needed
    large_primes: Vec<u64>,
}

impl PrimeState {
    fn new() -> Self {
        let sieve = SieveData::new(SIEVE_LIMIT);
        PrimeState {
            sieve,
            large_primes: Vec::new(),
        }
    }

    fn is_probably_prime(&self, n: u64) -> bool {
        if n <= SIEVE_LIMIT as u64 {
            self.sieve.is_prime[n as usize]
        } else {
            miller_rabin(n)
        }
    }

    fn get_prime(&mut self, index: usize) -> u64 {
        if index < self.sieve.primes.len() {
            self.sieve.primes[index]
        } else {
            // Estimate nth prime
            let mut candidate = self.estimate_nth_prime(index);
            if candidate % 2 == 0 {
                candidate += 1;
            }
            // Search for the next probable prime
            let mut found = self.large_primes.len() + self.sieve.primes.len();
            while found <= index {
                if self.is_probably_prime(candidate) {
                    self.large_primes.push(candidate);
                    found += 1;
                }
                candidate += 2;
            }
            self.large_primes[index - self.sieve.primes.len()]
        }
    }

    fn estimate_nth_prime(&mut self, n: usize) -> u64 {
        if n < SIEVE_LIMIT {
            self.sieve.primes[n - 1]
        } else {
            let n = n as f64;
            (n * (n.ln() + n.ln().ln())).round() as u64
        }
    }

    fn approximate_prime_index(&self, n: u64) -> usize {
        if n <= SIEVE_LIMIT as u64 {
            self.sieve.prime_pi[n as usize]
        } else {
            // Use PNT for large n
            (n as f64 / (n as f64).ln()).round() as usize
        }
    }

    fn next_prime(&self, n: u64) -> u64 {
        if n < SIEVE_LIMIT as u64 {
            let mut candidate = n + 1;
            while candidate <= SIEVE_LIMIT as u64 {
                if self.sieve.is_prime[candidate as usize] {
                    return candidate;
                }
                candidate += 1;
            }
        }
        // For larger n, use Miller-Rabin
        let mut candidate = if n % 2 == 0 { n + 1 } else { n + 2 };
        while !self.is_probably_prime(candidate) {
            candidate += 2;
        }
        candidate
    }
}

static GENERATOR: Lazy<Mutex<PrimeState>> = Lazy::new(|| Mutex::new(PrimeState::new()));

#[wasm_bindgen]
pub fn get_prime(index: usize) -> u64 {
    let mut generator = GENERATOR.lock().unwrap();
    generator.get_prime(index)
}

#[wasm_bindgen]
pub fn get_prime_index(n: u64) -> usize {
    let generator = GENERATOR.lock().unwrap();
    generator.approximate_prime_index(n)
}

#[wasm_bindgen]
pub fn get_next_prime(n: u64) -> u64 {
    let generator = GENERATOR.lock().unwrap();
    generator.next_prime(n)
}
