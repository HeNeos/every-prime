use bitvec::prelude::*;
use js_sys::BigInt;
use once_cell::sync::Lazy;
use rustc_hash::FxHashMap;
use std::str::FromStr;
use std::sync::Mutex;
use wasm_bindgen::prelude::*;

const MAX_INDEX: u64 = u32::MAX as u64;
const SIEVE_LIMIT: u64 = 20_000_000;
const PHI_CACHE_LIMIT: u64 = 4_000_000;
const SEGMENT_SIEVE_THRESHOLD: u64 = 1 << 26;

struct PrimeCache {
    small_primes: Vec<u64>,
    pi_cache: FxHashMap<u64, u64>,
    phi_cache: FxHashMap<(u64, u32), u64>,
    pi_sieve: Vec<u64>,
}

#[derive(Clone, Copy, Debug)]
struct PrimeState {
    current_index: u64,
    current_prime: u64,
}

struct PrimeGenerator {
    state: PrimeState,
    cache: PrimeCache,
}

impl PrimeGenerator {
    fn new() -> Self {
        let cache = Self::init_prime_cache();
        let first_prime = cache.small_primes[0];
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
        let mut is_prime = bitvec![1; sieve_limit_usize + 1];
        is_prime.set(0, false);
        is_prime.set(1, false);

        let limit = (sieve_limit_usize as f64).sqrt() as usize;
        for i in 2..=limit {
            if is_prime[i] {
                let mut j = i * i;
                while j <= sieve_limit_usize {
                    is_prime.set(j, false);
                    j += i;
                }
            }
        }
        let estimated_capacity = (SIEVE_LIMIT as f64 / (SIEVE_LIMIT as f64).ln()) as usize;
        let mut small_primes = Vec::with_capacity(estimated_capacity);
        let mut pi_sieve = vec![0u64; sieve_limit_usize + 1];
        let mut count = 0u64;
        for i in 2..=sieve_limit_usize {
            if is_prime[i] {
                small_primes.push(i as u64);
                count += 1;
            }
            pi_sieve[i] = count;
        }
        PrimeCache {
            small_primes,
            pi_cache: FxHashMap::default(),
            phi_cache: FxHashMap::default(),
            pi_sieve,
        }
    }

    #[inline]
    fn mod_mul(a: u64, b: u64, modulus: u64) -> u64 {
        ((a as u128 * b as u128) % modulus as u128) as u64
    }

    #[inline]
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
        if n <= SIEVE_LIMIT {
            return self.cache.small_primes.binary_search(&n).is_ok();
        }
        for &p in self.cache.small_primes.iter().take(20) {
            if n % p == 0 {
                return false;
            }
        }
        let mut d = n - 1;
        let r = d.trailing_zeros();
        d >>= r;
        let witnesses = [2, 13, 23, 1662803];
        'witness_loop: for &a in &witnesses {
            if a >= n {
                continue;
            }
            let mut x = self.mod_pow(a, d, n);
            if x == 1 || x == n - 1 {
                continue;
            }
            for _ in 0..r - 1 {
                x = Self::mod_mul(x, x, n);
                if x == n - 1 {
                    continue 'witness_loop;
                }
            }
            return false;
        }
        true
    }

    fn phi(&mut self, x: u64, a: u32) -> u64 {
        if a == 0 {
            return x;
        }
        if x == 0 {
            return 0;
        }
        if a == 1 {
            return (x + 1) / 2;
        }
        if x <= PHI_CACHE_LIMIT {
            if let Some(&res) = self.cache.phi_cache.get(&(x, a)) {
                return res;
            }
        }
        let a_usize = a as usize;
        let prime_a = self.cache.small_primes[a_usize - 1];
        let result = self.phi(x, a - 1) - self.phi(x / prime_a, a - 1);
        if x <= PHI_CACHE_LIMIT {
            self.cache.phi_cache.insert((x, a), result);
        }
        result
    }

    fn prime_counting_function(&mut self, x: u64) -> u64 {
        if x < 2 {
            return 0;
        }
        if x <= SIEVE_LIMIT {
            return self.cache.pi_sieve[x as usize];
        }
        if let Some(&cached) = self.cache.pi_cache.get(&x) {
            return cached;
        }
        let x_fourth_root = (x as f64).powf(0.25) as u64;
        let x_third_root = (x as f64).powf(1.0 / 3.0) as u64;
        let x_sqrt = (x as f64).sqrt() as u64;
        let a = self.prime_counting_function(x_fourth_root);
        let b = self.prime_counting_function(x_sqrt);
        let c = self.prime_counting_function(x_third_root);
        let mut sum = self.phi(x, a as u32);
        sum += ((b + a - 2) * (b - a + 1)) / 2;
        for i in a + 1..=b {
            let prime_i = self.cache.small_primes[i as usize - 1];
            let w = x / prime_i;
            sum -= self.prime_counting_function(w);
            if i <= c {
                let sqrt_w = (w as f64).sqrt() as u64;
                let b_i = self.prime_counting_function(sqrt_w);
                for j in i..=b_i {
                    let prime_j = self.cache.small_primes[j as usize - 1];
                    sum -= self.prime_counting_function(w / prime_j) - (j - 1);
                }
            }
        }
        if x % 10000 == 1 || x < 1_000_000_000 {
            self.cache.pi_cache.insert(x, sum);
        }
        sum
    }

    fn get_prime_bounds(&self, n: u64) -> (u64, u64) {
        let n_f64 = n as f64;
        let ln = n_f64.ln();
        let lln = ln.ln();
        let high = (n_f64
            * (ln + lln - 1.0 + (lln - 2.0) / ln
                - (lln * lln - 6.0 * lln + 10.273) / (2.0 * ln * ln))) as u64;
        let mut low = (n_f64
            * (ln + lln - 1.0 + (lln - 2.0) / ln
                - (lln * lln - 6.0 * lln + 11.847) / (2.0 * ln * ln))) as u64;
        low = low.max((ln * n_f64) as u64);
        low = low.max(2);
        let high = if n < 8009824 {
            let mut h = (1.25 * n_f64 * ln) as u64 + 1;
            if n < 15 {
                h += (2.1 * n_f64) as u64;
            }
            h
        } else {
            high
        };
        (low, high)
    }

    fn segmented_sieve_primes(&self, low: u64, high: u64) -> Vec<u64> {
        let size = (high - low + 1) as usize;
        let mut is_prime = vec![true; size];
        for &p in self.cache.small_primes.iter() {
            let p2 = p * p;
            if p2 > high {
                break;
            }
            let mut start = if p2 >= low {
                p2
            } else {
                let rem = low % p;
                if rem == 0 {
                    low
                } else {
                    low + (p - rem)
                }
            };
            if start < p2 {
                start = p2;
            }
            let mut j = start;
            while j <= high {
                is_prime[(j - low) as usize] = false;
                j += p;
            }
        }
        let mut out = Vec::new();
        for (i, &flag) in is_prime.iter().enumerate() {
            if flag {
                let v = low + i as u64;
                if v >= 2 {
                    out.push(v);
                }
            }
        }
        out
    }

    fn find_prime_by_segment(&mut self, n: u64) -> Result<u64, String> {
        let (mut low, high) = self.get_prime_bounds(n);
        low = low.max(2);
        let pi_lowm1 = if low <= 1 {
            0
        } else if low - 1 <= SIEVE_LIMIT {
            self.cache.pi_sieve[(low - 1) as usize]
        } else {
            self.prime_counting_function(low - 1)
        };
        let primes = self.segmented_sieve_primes(low, high);
        let k = n
            .checked_sub(pi_lowm1)
            .ok_or_else(|| format!("underflow computing k = {} - {}", n, pi_lowm1))?;
        if k == 0 || (k as usize) > primes.len() {
            return Err(format!(
                "couldn't find the {}th prime in [{},{}], only got {} primes",
                n,
                low,
                high,
                primes.len()
            ));
        }
        Ok(primes[(k - 1) as usize])
    }

    fn find_prime_at_index(&mut self, n: u64) -> Result<u64, String> {
        if n == 0 {
            return Err("Prime index starts at 1".to_string());
        }
        let sieved = self.cache.small_primes.len() as u64;
        if n <= sieved {
            return Ok(self.cache.small_primes[n as usize - 1]);
        }
        if n > SEGMENT_SIEVE_THRESHOLD {
            return self.find_prime_by_segment(n);
        }
        let (mut low, mut high) = self.get_prime_bounds(n);
        low = low.max(SIEVE_LIMIT + 1);
        let mut flag = 0;
        while low < high {
            let mut mid = low + (high - low) / 2;
            let mut pi_mid = self.prime_counting_function(mid);
            if pi_mid != n && flag < 10 {
                let pi_low = self.prime_counting_function(low);
                let pi_high = self.prime_counting_function(high);
                if pi_high - pi_low > 1 && pi_high != n && pi_low != n {
                    let coefficient =
                        (pi_high as f64 - n as f64) / (pi_high as f64 - pi_low as f64);
                    mid = (coefficient * low as f64 + (1.0 - coefficient) * high as f64) as u64;
                    pi_mid = self.prime_counting_function(mid);
                    flag += 1;
                } else {
                    flag = 10;
                }
            }
            if pi_mid >= n {
                high = mid;
            } else {
                low = mid + 1;
            }
        }
        if self.is_prime_miller_rabin(low) {
            let pi_low = self.prime_counting_function(low);
            if pi_low == n {
                self.cache.pi_cache.insert(low, n);
                return Ok(low);
            }
        }
        let search_range = 100;
        for p in (low - search_range).max(2)..=low + search_range {
            if self.is_prime_miller_rabin(p) {
                let pi_p = self.prime_counting_function(p);
                if pi_p == n {
                    return Ok(p);
                }
            }
        }
        Err(format!("Failed to find exact prime for index {}", n))
    }

    fn set_index(&mut self, index: u64) -> Result<(), String> {
        if self.state.current_index > 0 {
            let jump_factor = if index > self.state.current_index {
                index as f64 / self.state.current_index as f64
            } else {
                self.state.current_index as f64 / index as f64
            };
            if jump_factor > 1000.0 {
                self.cache.pi_cache.clear();
                self.cache.phi_cache.clear();
            }
        }
        let prime = self.find_prime_at_index(index)?;
        self.state.current_index = index;
        self.state.current_prime = prime;
        Ok(())
    }

    fn next(&mut self) -> Result<(), String> {
        if self.state.current_index >= MAX_INDEX {
            return Err(format!("Already at maximum index {}", MAX_INDEX));
        }
        if self.state.current_index < self.cache.small_primes.len() as u64 {
            self.state.current_index += 1;
            self.state.current_prime =
                self.cache.small_primes[self.state.current_index as usize - 1];
            return Ok(());
        }
        let mut candidate = self.state.current_prime + 2;
        for _ in 0..500 {
            if self.is_prime_miller_rabin(candidate) {
                self.state.current_index += 1;
                self.state.current_prime = candidate;
                return Ok(());
            }
            candidate += 2;
        }
        self.set_index(self.state.current_index + 1)
    }

    fn previous(&mut self) -> Result<(), String> {
        if self.state.current_index <= 1 {
            return Err("Already at first prime".to_string());
        }
        if self.state.current_index <= self.cache.small_primes.len() as u64 {
            self.state.current_index -= 1;
            self.state.current_prime =
                self.cache.small_primes[self.state.current_index as usize - 1];
            return Ok(());
        }
        if self.state.current_prime > 3 {
            let mut candidate = self.state.current_prime - 2;
            for _ in 0..500 {
                if candidate == 2 {
                    self.state.current_index -= 1;
                    self.state.current_prime = 2;
                    return Ok(());
                }
                if candidate % 3 == 0 {
                    candidate -= 2;
                    continue;
                }
                if self.is_prime_miller_rabin(candidate) {
                    self.state.current_index -= 1;
                    self.state.current_prime = candidate;
                    return Ok(());
                }
                candidate -= 2;
                if candidate <= 2 {
                    break;
                }
            }
        }
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

fn bigint_to_u64(bi: BigInt) -> Result<u64, JsValue> {
    let s = bi
        .to_string(10)?
        .as_string()
        .ok_or_else(|| JsValue::from_str("Failed to convert BigInt to string"))?;
    u64::from_str(&s)
        .map_err(|e| JsValue::from_str(&format!("Failed to parse BigInt string '{}': {}", s, e)))
}

static GENERATOR: Lazy<Mutex<PrimeGenerator>> = Lazy::new(|| Mutex::new(PrimeGenerator::new()));

#[wasm_bindgen]
pub fn init_pair(n_bigint: BigInt) -> Result<Vec<String>, JsValue> {
    let n = bigint_to_u64(n_bigint)?;
    let mut generator = GENERATOR
        .lock()
        .map_err(|e| JsValue::from_str(&format!("Mutex lock failed: {}", e)))?;
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
    Ok(())
}

#[wasm_bindgen]
pub fn get_pi(x_bigint: BigInt) -> Result<String, JsValue> {
    let x = bigint_to_u64(x_bigint)?;
    let mut generator = GENERATOR
        .lock()
        .map_err(|e| JsValue::from_str(&format!("Mutex lock failed: {}", e)))?;
    let pi_x = generator.prime_counting_function(x);
    Ok(pi_x.to_string())
}
