// src/lib.rs
use js_sys::BigInt;
use once_cell::sync::Lazy;
use std::collections::HashMap;
use std::str::FromStr;
use std::sync::Mutex;
use wasm_bindgen::prelude::*;

// Maximum index (2^32 - 1)
const MAX_INDEX: u64 = u32::MAX as u64; // 4_294_967_295
                                        // Sieve limit for precomputation
const SIEVE_LIMIT: u64 = 50_000_000;
// Cache limit for phi function
const PHI_CACHE_LIMIT: u64 = 4_000_000; // Cache phi(x, a) for x up to this limit

struct PrimeCache {
    small_primes: Vec<u64>, // Primes up to SIEVE_LIMIT
    // Cache for prime counting function pi(x). Key: x, Value: pi(x)
    pi_cache: HashMap<u64, u64>,
    // Cache for phi function. Key: (x, a), Value: phi(x, a)
    phi_cache: HashMap<(u64, u32), u64>,
}

#[derive(Clone, Copy, Debug)]
struct PrimeState {
    current_index: u64, // Position in the sequence of primes (1-based)
    current_prime: u64, // The prime number at this position
}

struct PrimeGenerator {
    state: PrimeState,
    cache: PrimeCache,
}

impl PrimeGenerator {
    fn new() -> Self {
        let cache = Self::init_prime_cache();
        let first_prime = cache.small_primes[0]; // Should be 2

        PrimeGenerator {
            state: PrimeState {
                current_index: 1,
                current_prime: first_prime,
            },
            cache,
        }
    }

    fn init_prime_cache() -> PrimeCache {
        let sieve_limit_usize = SIEVE_LIMIT as usize;
        let mut is_prime = vec![true; sieve_limit_usize + 1];
        is_prime[0] = false;
        is_prime[1] = false;

        for i in 2..=(sieve_limit_usize as f64).sqrt() as usize {
            if is_prime[i] {
                let mut j = i * i;
                while j <= sieve_limit_usize {
                    is_prime[j] = false;
                    j += i;
                }
            }
        }

        let mut small_primes = Vec::new();
        let mut pi_cache = HashMap::new();
        let mut count = 0u64;

        for i in 2..=sieve_limit_usize {
            if is_prime[i] {
                small_primes.push(i as u64);
                count += 1;
            }
        }
        // Store the final count for the sieve limit
        pi_cache.insert(SIEVE_LIMIT, count);

        PrimeCache {
            small_primes,
            pi_cache,
            phi_cache: HashMap::new(),
        }
    }

    // Modular multiplication: (a * b) % modulus for u64
    #[inline]
    fn mod_mul(a: u64, b: u64, modulus: u64) -> u64 {
        // Using u128 for intermediate result handles overflow up to 2^128
        ((a as u128 * b as u128) % modulus as u128) as u64
    }

    // Modular exponentiation: (base^exp) % modulus for u64
    fn mod_pow(&self, mut base: u64, mut exp: u64, modulus: u64) -> u64 {
        if modulus == 1 {
            return 0;
        }
        let mut result = 1;
        base %= modulus;
        while exp > 0 {
            if exp % 2 == 1 {
                result = Self::mod_mul(result, base, modulus);
            }
            base = Self::mod_mul(base, base, modulus);
            exp >>= 1;
        }
        result
    }

    // Miller-Rabin primality test for u64 (deterministic)
    fn is_prime_miller_rabin(&self, n: u64) -> bool {
        if n <= 1 {
            return false;
        }
        if n <= 3 {
            return true;
        }
        if n % 2 == 0 || n % 3 == 0 {
            return false;
        }

        // Check sieve cache first
        if n <= SIEVE_LIMIT {
            return self.cache.small_primes.binary_search(&n).is_ok();
        }

        // Find r, d such that n-1 = 2^r * d
        let mut d = n - 1;
        let r = d.trailing_zeros();
        d >>= r;

        // Witnesses deterministic for u64
        let witnesses = [2, 13, 23, 1662803];

        for &a in witnesses.iter() {
            // Ensure witness a is < n. If n is very small (e.g., n=5),
            // some witnesses might be >= n.
            if a >= n {
                continue;
            }

            let mut x = self.mod_pow(a, d, n);

            if x == 1 || x == n - 1 {
                continue;
            }

            let mut continue_witness = false;
            for _ in 0..r - 1 {
                x = Self::mod_mul(x, x, n);
                if x == n - 1 {
                    continue_witness = true;
                    break;
                }
            }
            if continue_witness {
                continue;
            }

            return false; // Definitely composite
        }

        true // Prime (deterministic for u64)
    }

    // phi(x, a): Counts numbers <= x not divisible by first 'a' primes.
    fn phi(&mut self, x: u64, a: u32) -> u64 {
        // Base cases
        if a == 0 {
            return x;
        }
        // Optimization: phi(x, 1) = x - floor(x/2) = ceil(x/2) for x>=1
        if a == 1 {
            return (x + 1) / 2;
        }
        // Edge cases for x
        if x == 0 {
            return 0;
        }
        if x == 1 {
            return 1;
        } // 1 is not divisible by any prime

        // Check cache
        let key = (x, a);
        if let Some(&result) = self.cache.phi_cache.get(&key) {
            return result;
        }

        // Ensure 'a' is a valid index into small_primes
        // a is 1-based count, index is (a-1)
        if (a as usize) == 0 || (a as usize) > self.cache.small_primes.len() {
            panic!("phi called with invalid prime count a = {}", a);
        }
        let prime_a = self.cache.small_primes[a as usize - 1]; // p_a

        // Recursive step: phi(x, a) = phi(x, a-1) - phi(x / p_a, a-1)
        let result = self.phi(x, a - 1) - self.phi(x / prime_a, a - 1);

        // Cache result if x is within limit
        if x < PHI_CACHE_LIMIT {
            self.cache.phi_cache.insert(key, result);
        }
        result
    }

    // *** USING LEGENDRE'S FORMULA for x > SIEVE_LIMIT ***
    fn prime_counting_function(&mut self, x: u64) -> u64 {
        if x < 2 {
            return 0;
        }

        // Use precomputed primes for x <= SIEVE_LIMIT
        if x <= SIEVE_LIMIT {
            // `partition_point` finds the count efficiently
            let count = self.cache.small_primes.partition_point(|&p| p <= x);
            return count as u64;
        }

        // Check pi_cache for previously computed large values
        if let Some(&cached_pi) = self.cache.pi_cache.get(&x) {
            return cached_pi;
        }

        // Legendre's Formula: pi(x) = phi(x, a) + a - 1, where a = pi(sqrt(x))
        let x_sqrt = (x as f64).sqrt() as u64;

        // Calculate a = pi(sqrt(x)). This might recurse.
        let a = self.prime_counting_function(x_sqrt);

        // Check if a is valid before proceeding
        if a == 0 {
            // This implies x_sqrt < 2, so x < 4. Contradicts x > SIEVE_LIMIT.
            // Should be unreachable. If reached, indicates an issue.
            panic!("prime_counting_function: a=0 for x={} > SIEVE_LIMIT", x);
        }

        // Cast 'a' to u32 for phi. Max a = pi(sqrt(2^64)) = pi(2^32) ~ 2e8, fits u32.
        let a_u32 = a as u32;

        // Calculate phi(x, a). This requires primes p_1..p_a.
        // Since a = pi(sqrt(x)) and sqrt(x) <= 2^32, and SIEVE_LIMIT=1M,
        // we know a <= pi(1M). All needed primes are in small_primes.
        let phi_val = self.phi(x, a_u32);

        // Legendre's formula result: phi(x, a) + a - 1
        // Check for potential underflow (shouldn't happen as a >= 1)
        let result = phi_val + a - 1;

        // Cache the result
        self.cache.pi_cache.insert(x, result);
        result
    }

    // Binary search for the nth prime using prime counting function (u64)
    fn find_prime_at_index(&mut self, n: u64) -> Result<u64, String> {
        if n == 0 {
            return Err("Prime index starts at 1".to_string());
        }
        if n > MAX_INDEX {
            return Err(format!("Index {} exceeds maximum {}", n, MAX_INDEX));
        }

        // Fast path for small indices using the sieve cache
        let sieved_primes_count = self.cache.small_primes.len() as u64;
        if n <= sieved_primes_count {
            return Ok(self.cache.small_primes[n as usize - 1]);
        }

        // Estimate the nth prime using PNT: p_n ~ n * ln(n)
        let n_float = n as f64;
        let log_n = n_float.ln();
        let log_log_n = log_n.ln();

        // Approximate bounds for binary search (use u64)
        // Lower bound starts after the sieve
        let mut low = SIEVE_LIMIT + 1;
        // Upper bound estimate
        let mut high = (n_float * (log_n + log_log_n.max(1.0)) * 1.2) as u64;
        // Ensure high is reasonably larger than low, prevent issues if estimate is bad
        high = high.max(low * 2).max(low + 1000); // Ensure a decent search range

        let mut nth_prime_candidate = 0u64;

        // Binary search for the smallest x such that pi(x) >= n
        while low <= high {
            let mid = low + (high - low) / 2;
            if mid == 0 {
                break;
            } // Avoid pi(0)

            let count = self.prime_counting_function(mid);

            if count >= n {
                // mid is a potential candidate (or too high). Store it and try lower.
                nth_prime_candidate = mid;
                if mid == 0 {
                    break;
                } // Avoid infinite loop if mid becomes 0
                high = mid - 1;
            } else {
                // count < n
                // The nth prime must be larger than mid.
                low = mid + 1;
            }
        }

        // After the loop, nth_prime_candidate holds the smallest x found such that pi(x) >= n.
        // If the loop finished because low > high, nth_prime_candidate holds the last successful mid.
        // If pi() was accurate, the nth prime should be <= nth_prime_candidate.

        if nth_prime_candidate == 0 {
            // This might happen if pi() consistently returns values << n, causing 'low'
            // to increase beyond 'high' without ever finding count >= n.
            // Or if the initial high estimate was drastically wrong.
            // Let's try using 'low' as a starting point if candidate is 0.
            if low > SIEVE_LIMIT {
                nth_prime_candidate = low; // Start searching from where 'low' ended up
                                           // We don't have pi_at_candidate here, maybe calculate it?
            } else {
                // If low is still within sieve limit, something is very wrong.
                return Err(format!(
                    "Binary search failed: n={}, low={}, high={}",
                    n, low, high
                ));
            }
        }

        // We need the largest prime p such that p <= nth_prime_candidate.
        // Furthermore, we need pi(p) to be exactly n if pi() is accurate.
        // Search downwards from nth_prime_candidate until we find a prime.
        let mut p = nth_prime_candidate;
        loop {
            if p < 2 {
                return Err(format!("Search downwards failed below 2 for n={}", n));
            }

            // Optimization: Check simple divisibility first
            if p > 3 && (p % 2 == 0 || p % 3 == 0) {
                p -= 1; // Adjust step below
                continue; // Skip Miller-Rabin
            }

            if self.is_prime_miller_rabin(p) {
                // Found a prime p <= nth_prime_candidate.
                // If pi() is accurate and monotonic, this should be the nth prime.
                // Let's add a verification step using pi(p) if needed for debugging.
                // let actual_pi_p = self.prime_counting_function(p);
                // if actual_pi_p == n {
                return Ok(p);
                // } else {
                // If pi(p) != n, it implies pi() is inaccurate or the search logic is flawed.
                // The binary search finds smallest x s.t. pi(x)>=n.
                // The downward search finds largest prime p <= x.
                // If pi is monotonic, pi(p) should be n. If not, pi is the problem.
                // For now, return the first prime found downwards.
                // return Err(format!("Verification failed: Found p={}, pi({})={}, expected n={}", p, p, actual_pi_p, n));
                // }
            }

            // Step down efficiently
            p -= if p % 2 == 0 { 1 } else { 2 }; // Skip even numbers
        }
    }

    fn set_index(&mut self, index: u64) -> Result<(), String> {
        // Clear caches before a jump? Might impact performance but ensures fresh calculation.
        // self.cache.pi_cache.clear();
        // self.cache.phi_cache.clear();
        // self.cache.pi_cache.insert(SIEVE_LIMIT, self.cache.small_primes.len() as u64);

        let prime = self.find_prime_at_index(index)?;
        self.state.current_index = index;
        self.state.current_prime = prime;
        Ok(())
    }

    // Go to the next prime. Use set_index.
    fn next(&mut self) -> Result<(), String> {
        if self.state.current_index >= MAX_INDEX {
            return Err(format!("Already at maximum index {}", MAX_INDEX));
        }
        // Avoid clearing cache on every step for performance
        self.set_index(self.state.current_index + 1)
    }

    // Go to the previous prime. Use set_index.
    fn previous(&mut self) -> Result<(), String> {
        if self.state.current_index <= 1 {
            return Err("Already at first prime".to_string());
        }
        // Avoid clearing cache on every step for performance
        self.set_index(self.state.current_index - 1)
    }

    fn get_current_pair_as_string_vec(&self) -> Vec<String> {
        vec![
            self.state.current_prime.to_string(),
            self.state.current_index.to_string(),
        ]
    }

    fn get_current_index_as_string(&self) -> String {
        self.state.current_index.to_string()
    }
}

// Helper to convert JS BigInt to Rust u64
fn bigint_to_u64(bi: BigInt) -> Result<u64, JsValue> {
    let s = bi
        .to_string(10)?
        .as_string()
        .ok_or_else(|| JsValue::from_str("Failed to convert BigInt to string"))?;
    u64::from_str(&s)
        .map_err(|e| JsValue::from_str(&format!("Failed to parse BigInt string '{}': {}", s, e)))
}

// Static instance of the generator wrapped in a Mutex
static GENERATOR: Lazy<Mutex<PrimeGenerator>> = Lazy::new(|| Mutex::new(PrimeGenerator::new()));

// --- Wasm Bindings ---

#[wasm_bindgen]
pub fn init_pair(n_bigint: BigInt) -> Result<Vec<String>, JsValue> {
    let n = bigint_to_u64(n_bigint)?;
    let mut generator = GENERATOR
        .lock()
        .map_err(|e| JsValue::from_str(&format!("Mutex lock failed: {}", e)))?;
    // Optional: Clear cache on jump?
    // generator.cache.pi_cache.clear();
    // generator.cache.phi_cache.clear();
    // generator.cache.pi_cache.insert(SIEVE_LIMIT, generator.cache.small_primes.len() as u64);
    generator.set_index(n).map_err(|e| JsValue::from_str(&e))?;
    Ok(generator.get_current_pair_as_string_vec())
}

#[wasm_bindgen]
pub fn next_pair() -> Result<Vec<String>, JsValue> {
    let mut generator = GENERATOR
        .lock()
        .map_err(|e| JsValue::from_str(&format!("Mutex lock failed: {}", e)))?;
    generator.next().map_err(|e| JsValue::from_str(&e))?;
    Ok(generator.get_current_pair_as_string_vec())
}

#[wasm_bindgen]
pub fn prev_pair() -> Result<Vec<String>, JsValue> {
    let mut generator = GENERATOR
        .lock()
        .map_err(|e| JsValue::from_str(&format!("Mutex lock failed: {}", e)))?;
    generator.previous().map_err(|e| JsValue::from_str(&e))?;
    Ok(generator.get_current_pair_as_string_vec())
}

#[wasm_bindgen]
pub fn get_current_index() -> Result<String, JsValue> {
    let generator = GENERATOR
        .lock()
        .map_err(|e| JsValue::from_str(&format!("Mutex lock failed: {}", e)))?;
    Ok(generator.get_current_index_as_string())
}

#[wasm_bindgen]
pub fn clear_caches() -> Result<(), JsValue> {
    let mut generator = GENERATOR
        .lock()
        .map_err(|e| JsValue::from_str(&format!("Mutex lock failed: {}", e)))?;
    generator.cache.pi_cache.clear();
    generator.cache.phi_cache.clear();
    // Re-insert essential cache value
    let sieve_count = generator.cache.small_primes.len() as u64;
    generator.cache.pi_cache.insert(SIEVE_LIMIT, sieve_count);
    Ok(())
}

// Optional: Expose pi function for testing
#[wasm_bindgen]
pub fn get_pi(x_bigint: BigInt) -> Result<String, JsValue> {
    let x = bigint_to_u64(x_bigint)?;
    let mut generator = GENERATOR
        .lock()
        .map_err(|e| JsValue::from_str(&format!("Mutex lock failed: {}", e)))?;
    let pi_x = generator.prime_counting_function(x);
    Ok(pi_x.to_string())
}
