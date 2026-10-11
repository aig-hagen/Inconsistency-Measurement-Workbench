// ---------------------------------------------------------------------------
// Utilities: errors, deadlines, PRNG, bitsets, combinatorics
// ---------------------------------------------------------------------------

class TimeoutError extends Error {
  constructor(msg) { super(msg || 'Computation timed out'); this.name = 'TimeoutError'; }
}

class LimitError extends Error {
  constructor(msg) { super(msg); this.name = 'LimitError'; }
}

// A global, cooperative deadline. Long-running loops call checkDeadline().
const Deadline = {
  at: Infinity,
  set(ms) { this.at = (ms == null || !isFinite(ms)) ? Infinity : Date.now() + ms; },
  clear() { this.at = Infinity; },
};
let _deadlineCounter = 0;
function checkDeadline() {
  if (Deadline.at !== Infinity && ((++_deadlineCounter & 255) === 0) && Date.now() > Deadline.at)
    throw new TimeoutError();
}
function checkDeadlineNow() {
  if (Deadline.at !== Infinity && Date.now() > Deadline.at) throw new TimeoutError();
}

// Seeded PRNG (mulberry32); returns floats in [0,1).
function makeRng(seed) {
  let a = (seed >>> 0) || 0x9e3779b9;
  const rng = function () {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  rng.int = (lo, hi) => lo + Math.floor(rng() * (hi - lo + 1)); // inclusive
  rng.pick = (arr) => arr[Math.floor(rng() * arr.length)];
  return rng;
}

// Exact-as-possible binomial coefficient as a double.
function binomial(n, k) {
  if (n < 0 || k < 0 || k > n) return 0;
  k = Math.min(k, n - k);
  let r = 1;
  for (let i = 1; i <= k; i++) r = r * (n - k + i) / i;
  return Math.round(r);
}

function factorial(n) {
  let r = 1;
  for (let i = 2; i <= n; i++) r *= i;
  return r;
}

function popcount32(x) {
  x = x - ((x >>> 1) & 0x55555555);
  x = (x & 0x33333333) + ((x >>> 2) & 0x33333333);
  return (((x + (x >>> 4)) & 0x0F0F0F0F) * 0x01010101) >>> 24;
}

// Fixed-size bitset over {0..n-1}.
class BitSet {
  constructor(n, words) {
    this.n = n;
    this.w = words || new Uint32Array((n + 31) >>> 5);
  }
  static of(n, idxs) { const b = new BitSet(n); for (const i of idxs) b.add(i); return b; }
  static full(n) { const b = new BitSet(n); for (let i = 0; i < n; i++) b.add(i); return b; }
  clone() { return new BitSet(this.n, this.w.slice()); }
  has(i) { return (this.w[i >>> 5] & (1 << (i & 31))) !== 0; }
  add(i) { this.w[i >>> 5] |= (1 << (i & 31)); return this; }
  delete(i) { this.w[i >>> 5] &= ~(1 << (i & 31)); return this; }
  isEmpty() { for (let i = 0; i < this.w.length; i++) if (this.w[i]) return false; return true; }
  count() { let c = 0; for (let i = 0; i < this.w.length; i++) c += popcount32(this.w[i]); return c; }
  orInPlace(b) { for (let i = 0; i < this.w.length; i++) this.w[i] |= b.w[i]; return this; }
  andInPlace(b) { for (let i = 0; i < this.w.length; i++) this.w[i] &= b.w[i]; return this; }
  or(b) { return this.clone().orInPlace(b); }
  and(b) { return this.clone().andInPlace(b); }
  andNot(b) { const r = this.clone(); for (let i = 0; i < r.w.length; i++) r.w[i] &= ~b.w[i]; return r; }
  intersects(b) { for (let i = 0; i < this.w.length; i++) if (this.w[i] & b.w[i]) return true; return false; }
  isSubsetOf(b) { for (let i = 0; i < this.w.length; i++) if ((this.w[i] & ~b.w[i]) !== 0) return false; return true; }
  equals(b) { for (let i = 0; i < this.w.length; i++) if (this.w[i] !== b.w[i]) return false; return true; }
  key() { return Array.prototype.join.call(this.w, ','); }
  toArray() { const r = []; for (let i = 0; i < this.n; i++) if (this.has(i)) r.push(i); return r; }
  first() { for (let i = 0; i < this.n; i++) if (this.has(i)) return i; return -1; }
}

function cmpIndexArrays(a, b) {
  if (a.length !== b.length) return a.length - b.length;
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return a[i] - b[i];
  return 0;
}

function sortedUnique(arr) {
  const s = Array.from(new Set(arr));
  s.sort((x, y) => x - y);
  return s;
}

// Compare two measure values with tolerance (handles Infinity / NaN).
function approxEqual(a, b, tol) {
  if (tol == null) tol = 1e-9;
  if (Number.isNaN(a) || Number.isNaN(b)) return Number.isNaN(a) && Number.isNaN(b);
  if (!isFinite(a) || !isFinite(b)) return a === b;
  return Math.abs(a - b) <= tol * Math.max(1, Math.abs(a), Math.abs(b));
}

IM.TimeoutError = TimeoutError;
IM.LimitError = LimitError;
IM.Deadline = Deadline;
IM.checkDeadline = checkDeadline;
IM.makeRng = makeRng;
IM.binomial = binomial;
IM.factorial = factorial;
IM.BitSet = BitSet;
IM.approxEqual = approxEqual;
