/* Inconsistency Measurement core library 1.0.0 (JavaScript port of TweetyProject measures, LGPL-3.0) */
function imCore() {
'use strict';
const IM = {};
// ===== 00-util.js =====
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

// ===== 01-formula.js =====
// ---------------------------------------------------------------------------
// Propositional formulas (port of org.tweetyproject.logics.pl.syntax)
//
// A formula is a plain object {t, name?, k?} with t one of
//   'prop' (name), 'not' (k:[f]), 'and' | 'or' | 'xor' (k:[f1..fn], ordered),
//   'impl' | 'equiv' (k:[a,b]), 'top' (+), 'bot' (-).
// Equality follows TweetyProject: structural and order-sensitive for
// associative connectives (a&&b != b&&a). key(f) is an injective string
// representation used for equality, hashing and deduplication.
// ---------------------------------------------------------------------------

const Prop = (name) => ({ t: 'prop', name });
const Not = (f) => ({ t: 'not', k: [f] });
const And = (list) => ({ t: 'and', k: list.slice() });
const Or = (list) => ({ t: 'or', k: list.slice() });
const Xor = (list) => ({ t: 'xor', k: list.slice() });
const Impl = (a, b) => ({ t: 'impl', k: [a, b] });
const Equiv = (a, b) => ({ t: 'equiv', k: [a, b] });
const TOP = Object.freeze({ t: 'top' });
const BOT = Object.freeze({ t: 'bot' });

const ASSOC = { and: true, or: true, xor: true };
const SYMBOL = { and: '&&', or: '||', xor: '^^', impl: '=>', equiv: '<=>' };
const EMPTY_SYMBOL = { and: '+', or: '-', xor: '-' };

function isAssoc(f) { return ASSOC[f.t] === true; }

// Injective key (proposition names never contain '(', ')' or '|').
function key(f) {
  if (f._key !== undefined) return f._key;
  let s;
  switch (f.t) {
    case 'prop': s = f.name; break;
    case 'top': s = '+'; break;
    case 'bot': s = '-'; break;
    case 'not': s = '!(' + key(f.k[0]) + ')'; break;
    case 'and': s = '&(' + f.k.map(key).join('|') + ')'; break;
    case 'or': s = 'v(' + f.k.map(key).join('|') + ')'; break;
    case 'xor': s = '^(' + f.k.map(key).join('|') + ')'; break;
    case 'impl': s = '>(' + key(f.k[0]) + '|' + key(f.k[1]) + ')'; break;
    case 'equiv': s = '=(' + key(f.k[0]) + '|' + key(f.k[1]) + ')'; break;
    default: throw new Error('Unknown formula type ' + f.t);
  }
  if (!Object.isFrozen(f)) Object.defineProperty(f, '_key', { value: s, enumerable: false });
  return s;
}

function equals(f, g) { return f === g || key(f) === key(g); }

// String representation exactly as TweetyProject's toString() (re-parseable).
function toTweetyString(f) {
  switch (f.t) {
    case 'prop': return f.name;
    case 'top': return '+';
    case 'bot': return '-';
    case 'not': {
      const g = f.k[0];
      const s = toTweetyString(g);
      return (isAssoc(g) || g.t === 'not') ? '!(' + s + ')' : '!' + s;
    }
    case 'and': case 'or': case 'xor': {
      if (f.k.length === 0) return EMPTY_SYMBOL[f.t];
      return f.k.map(g => (isAssoc(g) && g.k.length > 1) ? '(' + toTweetyString(g) + ')' : toTweetyString(g)).join(SYMBOL[f.t]);
    }
    case 'impl': return '(' + toTweetyString(f.k[0]) + '=>' + toTweetyString(f.k[1]) + ')';
    case 'equiv': return '(' + toTweetyString(f.k[0]) + '<=>' + toTweetyString(f.k[1]) + ')';
  }
  throw new Error('Unknown formula type ' + f.t);
}

// Human-friendly representation with spaces and minimal parentheses.
const PREC = { equiv: 1, impl: 2, xor: 3, or: 4, and: 5, not: 6, prop: 7, top: 7, bot: 7 };
function toPretty(f, parentPrec) {
  parentPrec = parentPrec || 0;
  let s, p = PREC[f.t];
  switch (f.t) {
    case 'prop': return f.name;
    case 'top': return '+';
    case 'bot': return '-';
    case 'not': {
      const g = f.k[0];
      s = '!' + (PREC[g.t] >= 6 && g.t !== 'not' ? toPretty(g, 6) : '(' + toPretty(g, 0) + ')');
      return s;
    }
    case 'and': case 'or': case 'xor':
      if (f.k.length === 0) return EMPTY_SYMBOL[f.t];
      if (f.k.length === 1) return toPretty(f.k[0], parentPrec);
      // nested same-type associative formulas get explicit parentheses (Tweety keeps nesting)
      s = f.k.map(g => (g.t === f.t || PREC[g.t] <= p) ? '(' + toPretty(g, 0) + ')' : toPretty(g, p)).join(' ' + SYMBOL[f.t] + ' ');
      break;
    case 'impl': case 'equiv':
      // both sides parenthesised when they are binary connectives (no chaining ambiguity)
      s = f.k.map(g => (PREC[g.t] <= 2) ? '(' + toPretty(g, 0) + ')' : toPretty(g, p)).join(' ' + SYMBOL[f.t] + ' ');
      break;
  }
  return (p <= parentPrec) ? '(' + s + ')' : s;
}

// Sorted array of the atom names occurring in f.
function atoms(f) {
  if (f._atoms !== undefined) return f._atoms;
  const set = new Set();
  (function rec(g) {
    if (g.t === 'prop') set.add(g.name);
    else if (g.k) for (const h of g.k) rec(h);
  })(f);
  const arr = Array.from(set).sort(cmpNames);
  if (!Object.isFrozen(f)) Object.defineProperty(f, '_atoms', { value: arr, enumerable: false });
  return arr;
}

// Natural ordering of atom names (a2 < a10).
function cmpNames(a, b) {
  return a.localeCompare(b, 'en', { numeric: true });
}

function isLiteral(f) { return f.t === 'prop' || (f.t === 'not' && f.k[0].t === 'prop'); }

// Tweety's getLiterals(): set (by key) of literal subformulas; a negation of a
// complex formula contributes the literals of its argument.
function literals(f) {
  const res = new Map();
  (function rec(g) {
    switch (g.t) {
      case 'prop': res.set(key(g), g); break;
      case 'not': if (g.k[0].t === 'prop') res.set(key(g), g); else rec(g.k[0]); break;
      case 'top': case 'bot': break;
      default: for (const h of g.k) rec(h);
    }
  })(f);
  return res;
}

// Tweety's complement(): strips a negation, otherwise negates.
function complement(f) { return f.t === 'not' ? f.k[0] : Not(f); }

function numberOfOccurrences(f, p) {
  if (f.t === 'prop') return f.name === p ? 1 : 0;
  if (!f.k) return 0;
  let n = 0;
  for (const g of f.k) n += numberOfOccurrences(g, p);
  return n;
}

function occurrenceCount(f) {
  if (f.t === 'prop') return 1;
  if (!f.k) return 0;
  let n = 0;
  for (const g of f.k) n += occurrenceCount(g);
  return n;
}

// Replace the i-th (1-based, left to right) occurrence of atom p by g.
// (Intended semantics of Tweety's PlFormula.replace; side-effect free.)
function replace(f, p, g, i) {
  let count = 0;
  return (function rec(h) {
    if (h.t === 'prop') {
      if (h.name === p) { count++; if (count === i) return g; }
      return h;
    }
    if (!h.k) return h;
    return { t: h.t, k: h.k.map(rec) };
  })(f);
}

// Evaluate under an assignment function (name -> boolean).
function evaluate(f, val) {
  switch (f.t) {
    case 'prop': return !!val(f.name);
    case 'top': return true;
    case 'bot': return false;
    case 'not': return !evaluate(f.k[0], val);
    case 'and': for (const g of f.k) if (!evaluate(g, val)) return false; return true;
    case 'or': for (const g of f.k) if (evaluate(g, val)) return true; return false;
    case 'xor': { let r = false; for (const g of f.k) if (evaluate(g, val)) r = !r; return r; }
    case 'impl': return !evaluate(f.k[0], val) || evaluate(f.k[1], val);
    case 'equiv': return evaluate(f.k[0], val) === evaluate(f.k[1], val);
  }
  throw new Error('Unknown formula type ' + f.t);
}

// ----- Truth tables ---------------------------------------------------------
// truthTable(f, idx, n): Uint32Array with 2^n bits; bit w is set iff the world
// w (bit j of w = truth value of atom with index j) satisfies f.
const MAX_TT_ATOMS = 24;
const LOW_PATTERNS = [0xAAAAAAAA, 0xCCCCCCCC, 0xF0F0F0F0, 0xFF00FF00, 0xFFFF0000];

function ttWords(n) { return n <= 5 ? 1 : (1 << (n - 5)); }
function ttMask(n) { return n >= 5 ? 0xFFFFFFFF : ((1 << (1 << n)) - 1) >>> 0; }

function truthTable(f, idx, n) {
  if (n > MAX_TT_ATOMS) throw new LimitError('Too many atoms for truth tables (' + n + ')');
  const W = ttWords(n), mask = ttMask(n);
  const fill = (v) => { const a = new Uint32Array(W); if (v) { a.fill(0xFFFFFFFF); a[W - 1] &= mask; if (W === 1) a[0] = mask; } return a; };
  function rec(g) {
    switch (g.t) {
      case 'top': return fill(true);
      case 'bot': return fill(false);
      case 'prop': {
        const j = idx.get(g.name);
        const a = new Uint32Array(W);
        if (j < 5) { a.fill(LOW_PATTERNS[j]); if (W === 1) a[0] &= mask; }
        else { const step = 1 << (j - 5); for (let i = 0; i < W; i++) if (i & step) a[i] = 0xFFFFFFFF; }
        return a;
      }
      case 'not': { const a = rec(g.k[0]); for (let i = 0; i < W; i++) a[i] = ~a[i]; a[W - 1] &= mask; if (W === 1) a[0] &= mask; return a; }
      case 'and': { if (g.k.length === 0) return fill(true); const a = rec(g.k[0]); for (let j = 1; j < g.k.length; j++) { const b = rec(g.k[j]); for (let i = 0; i < W; i++) a[i] &= b[i]; } return a; }
      case 'or': { if (g.k.length === 0) return fill(false); const a = rec(g.k[0]); for (let j = 1; j < g.k.length; j++) { const b = rec(g.k[j]); for (let i = 0; i < W; i++) a[i] |= b[i]; } return a; }
      case 'xor': { if (g.k.length === 0) return fill(false); const a = rec(g.k[0]); for (let j = 1; j < g.k.length; j++) { const b = rec(g.k[j]); for (let i = 0; i < W; i++) a[i] ^= b[i]; } return a; }
      case 'impl': { const a = rec(g.k[0]), b = rec(g.k[1]); for (let i = 0; i < W; i++) a[i] = ~a[i] | b[i]; a[W - 1] &= mask; if (W === 1) a[0] &= mask; return a; }
      case 'equiv': { const a = rec(g.k[0]), b = rec(g.k[1]); for (let i = 0; i < W; i++) a[i] = ~(a[i] ^ b[i]); a[W - 1] &= mask; if (W === 1) a[0] &= mask; return a; }
    }
    throw new Error('Unknown formula type ' + g.t);
  }
  return rec(f);
}
function ttGet(tt, w) { return (tt[w >>> 5] >>> (w & 31)) & 1; }
function ttCount(tt) { let c = 0; for (let i = 0; i < tt.length; i++) c += popcount32(tt[i]); return c; }
function ttIsZero(tt) { for (let i = 0; i < tt.length; i++) if (tt[i]) return false; return true; }

// Truth table of f over its own atoms; returns {atoms, tt}.
function localTruthTable(f) {
  const at = atoms(f);
  const idx = new Map(at.map((a, i) => [a, i]));
  return { atoms: at, tt: truthTable(f, idx, at.length) };
}

// ----- Normal forms (used for rewriting / display) -------------------------
function toNnf(f) {
  switch (f.t) {
    case 'prop': case 'top': case 'bot': return f;
    case 'and': return And(f.k.map(toNnf));
    case 'or': return Or(f.k.map(toNnf));
    case 'impl': return Or([toNnf(Not(f.k[0])), toNnf(f.k[1])]);
    case 'equiv': return And([Or([toNnf(Not(f.k[0])), toNnf(f.k[1])]), Or([toNnf(Not(f.k[1])), toNnf(f.k[0])])]);
    case 'xor': {
      if (f.k.length === 0) return BOT;
      let acc = f.k[0];
      for (let i = 1; i < f.k.length; i++) acc = Or([And([acc, Not(f.k[i])]), And([Not(acc), f.k[i]])]);
      return toNnf(acc);
    }
    case 'not': {
      const g = f.k[0];
      switch (g.t) {
        case 'prop': return f;
        case 'top': return BOT;
        case 'bot': return TOP;
        case 'not': return toNnf(g.k[0]);
        case 'and': return Or(g.k.map(h => toNnf(Not(h))));
        case 'or': return And(g.k.map(h => toNnf(Not(h))));
        case 'impl': return And([toNnf(g.k[0]), toNnf(Not(g.k[1]))]);
        case 'equiv': return toNnf(Not(toNnf(g)));
        case 'xor': return toNnf(Not(toNnf(g)));
      }
    }
  }
  throw new Error('Unknown formula type ' + f.t);
}

// CNF as an array of clauses (arrays of literal formulas); may blow up.
function cnfClauses(f, limit) {
  limit = limit || 4096;
  function rec(g) {
    switch (g.t) {
      case 'top': return [];
      case 'bot': return [[]];
      case 'prop': return [[g]];
      case 'not': return [[g]]; // nnf: literal
      case 'and': { let r = []; for (const h of g.k) r = r.concat(rec(h)); if (r.length > limit) throw new LimitError('CNF too large'); return r; }
      case 'or': {
        let r = [[]];
        for (const h of g.k) {
          const c = rec(h), nr = [];
          for (const a of r) for (const b of c) nr.push(a.concat(b));
          r = nr;
          if (r.length > limit) throw new LimitError('CNF too large');
        }
        return r;
      }
    }
    throw new Error('Unexpected type in NNF: ' + g.t);
  }
  return rec(toNnf(f));
}

function toCnfFormula(f) {
  const cl = cnfClauses(f);
  const clauses = cl.map(c => c.length === 1 ? c[0] : (c.length === 0 ? BOT : Or(c)));
  if (clauses.length === 0) return TOP;
  return clauses.length === 1 ? clauses[0] : And(clauses);
}

// Swap operands of commutative connectives (syntactic variant).
function commuted(f) {
  switch (f.t) {
    case 'prop': case 'top': case 'bot': return f;
    case 'not': return Not(commuted(f.k[0]));
    case 'and': case 'or': case 'xor': return { t: f.t, k: f.k.map(commuted).reverse() };
    case 'equiv': return Equiv(commuted(f.k[1]), commuted(f.k[0]));
    case 'impl': return Impl(commuted(f.k[0]), commuted(f.k[1]));
  }
  return f;
}

// Prime implicants of f (semantic), as array of sorted literal-key arrays.
// A tautology has the single empty implicant, a contradiction none.
function primeImplicants(f, maxAtoms) {
  const { atoms: at, tt } = localTruthTable(f);
  const m = at.length;
  if (m > (maxAtoms || 12)) throw new LimitError('Too many atoms for prime implicants');
  const N = 1 << m;
  // term = (care mask, value mask); implicant iff all worlds matching satisfy f
  const isImpl = (care, val) => {
    for (let w = 0; w < N; w++) if ((w & care) === val && !ttGet(tt, w)) return false;
    return true;
  };
  const impl = [];
  // enumerate terms by increasing size
  const terms = [];
  for (let care = 0; care < N; care++) {
    for (let val = care; ; val = (val - 1) & care) {
      terms.push([care, val]);
      if (val === 0) break;
    }
  }
  terms.sort((a, b) => popcount32(a[0]) - popcount32(b[0]));
  for (const [care, val] of terms) {
    // skip if subsumed by an already found (smaller) implicant
    let sub = false;
    for (const [c2, v2] of impl) if ((c2 & care) === c2 && (val & c2) === v2) { sub = true; break; }
    if (sub) continue;
    if (isImpl(care, val)) impl.push([care, val]);
  }
  return impl.map(([care, val]) => {
    const lits = [];
    for (let j = 0; j < m; j++) if (care & (1 << j)) lits.push((val & (1 << j)) ? at[j] : '!(' + at[j] + ')');
    return lits.sort();
  });
}

IM.F = { Prop, Not, And, Or, Xor, Impl, Equiv, TOP, BOT };
IM.key = key;
IM.equals = equals;
IM.toTweetyString = toTweetyString;
IM.toPretty = toPretty;
IM.atoms = atoms;
IM.cmpNames = cmpNames;
IM.isLiteral = isLiteral;
IM.literals = literals;
IM.complement = complement;
IM.numberOfOccurrences = numberOfOccurrences;
IM.replace = replace;
IM.evaluate = evaluate;
IM.truthTable = truthTable;
IM.ttGet = ttGet;
IM.ttCount = ttCount;
IM.localTruthTable = localTruthTable;
IM.toNnf = toNnf;
IM.toCnfFormula = toCnfFormula;
IM.cnfClauses = cnfClauses;
IM.commuted = commuted;
IM.primeImplicants = primeImplicants;

// ===== 02-parser.js =====
// ---------------------------------------------------------------------------
// Parser for TweetyProject's propositional syntax (port of PlParser).
//
//   FORMULA ::= PROP | "(" FORMULA ")" | FORMULA "&&" FORMULA | FORMULA "||" FORMULA
//             | FORMULA "^^" FORMULA | FORMULA "=>" FORMULA | FORMULA "<=>" FORMULA
//             | "!" FORMULA | "+" | "-"
//
// Binding strength (weakest first): <=>, =>, ^^, ||, &&, !.  &&, || and ^^ are
// n-ary (flat lists), parenthesised sub-formulas stay nested, as in Tweety.
// The logical symbols ¬ ∧ ∨ ⊕ → ↔ ⊤ ⊥ are accepted as alternatives to
// ! && || ^^ => <=> + -.
// Differences to Tweety's parser: chained => and <=> are right-associative
// (Tweety silently concatenates atom names), "!!a" is accepted, and lines
// starting with '%' or '#' are comments. As in Tweety, blanks inside a name
// are ignored ("a b" is the atom "ab"); proposition names may contain any
// character except | & ! ( ) < > = ^ and whitespace.
// ---------------------------------------------------------------------------

class ParseError extends Error {
  constructor(msg, pos) { super(msg); this.name = 'ParseError'; this.pos = pos; }
}

const SPECIAL = new Set(['|', '&', '!', '(', ')', '<', '>', '=', '^', '¬', '∧', '∨', '⊕', '→', '⇒', '↔', '⇔', '⊤', '⊥']);
// logical symbols accepted as alternatives to TweetyProject's ASCII operators
const SYMBOL_TOKENS = { '¬': '!', '∧': '&&', '∨': '||', '⊕': '^^', '→': '=>', '⇒': '=>', '↔': '<=>', '⇔': '<=>' };

function tokenize(s) {
  const toks = [];
  let i = 0;
  const n = s.length;
  while (i < n) {
    const c = s[i];
    if (c === ' ' || c === '\t') { i++; continue; }
    if (c === '(' || c === ')' || c === '!') { toks.push({ v: c, pos: i }); i++; continue; }
    if (SYMBOL_TOKENS[c]) { toks.push({ v: SYMBOL_TOKENS[c], pos: i }); i++; continue; }
    if (c === '⊤' || c === '⊥') { toks.push({ v: c === '⊤' ? '+' : '-', pos: i, name: true }); i++; continue; }
    if (c === '&' || c === '|' || c === '^') {
      if (s[i + 1] === c) { toks.push({ v: c + c, pos: i }); i += 2; continue; }
      throw new ParseError("Unexpected '" + c + "' (did you mean '" + c + c + "'?)", i);
    }
    if (c === '=') {
      if (s[i + 1] === '>') { toks.push({ v: '=>', pos: i }); i += 2; continue; }
      throw new ParseError("Unexpected '=' (did you mean '=>'?)", i);
    }
    if (c === '<') {
      if (s[i + 1] === '=' && s[i + 2] === '>') { toks.push({ v: '<=>', pos: i }); i += 3; continue; }
      throw new ParseError("Unexpected '<' (did you mean '<=>'?)", i);
    }
    if (c === '>') throw new ParseError("Unexpected '>'", i);
    // a name: maximal run of non-special characters (blanks are skipped)
    let name = '';
    const start = i;
    while (i < n && !SPECIAL.has(s[i])) {
      if (s[i] !== ' ' && s[i] !== '\t') name += s[i];
      i++;
    }
    if (/\s/.test(name)) throw new ParseError('Invalid whitespace in name', start);
    toks.push({ v: name, pos: start, name: true });
  }
  return toks;
}

function parseFormula(text) {
  const toks = tokenize(text);
  let p = 0;
  const peek = () => toks[p] ? toks[p].v : null;
  const posOf = () => toks[p] ? toks[p].pos : text.length;
  function expect(v) {
    if (peek() !== v) throw new ParseError("Expected '" + v + "'" + (peek() === null ? ' but reached end of formula' : " but found '" + peek() + "'"), posOf());
    p++;
  }
  function parseEquiv() {
    const left = parseImpl();
    if (peek() === '<=>') { p++; return Equiv(left, parseEquiv()); }
    return left;
  }
  function parseImpl() {
    const left = parseXor();
    if (peek() === '=>') { p++; return Impl(left, parseImpl()); }
    return left;
  }
  function parseNary(op, type, next) {
    const first = next();
    if (peek() !== op) return first;
    const list = [first];
    while (peek() === op) { p++; list.push(next()); }
    return { t: type, k: list };
  }
  function parseXor() { return parseNary('^^', 'xor', parseOr); }
  function parseOr() { return parseNary('||', 'or', parseAnd); }
  function parseAnd() { return parseNary('&&', 'and', parseUnary); }
  function parseUnary() {
    const v = peek();
    if (v === '!') { p++; return Not(parseUnary()); }
    if (v === '(') {
      p++;
      if (peek() === ')') throw new ParseError('Empty parentheses', posOf());
      const f = parseEquiv();
      expect(')');
      return f;
    }
    if (v === null) throw new ParseError('Unexpected end of formula', posOf());
    const tok = toks[p];
    if (!tok.name) throw new ParseError("Unexpected '" + v + "'", tok.pos);
    p++;
    if (v === '+') return TOP;
    if (v === '-') return BOT;
    return Prop(v);
  }
  if (toks.length === 0) throw new ParseError('Empty formula', 0);
  const f = parseEquiv();
  if (p < toks.length) throw new ParseError("Unexpected '" + peek() + "'", posOf());
  return f;
}

// A knowledge base: a set of formulas (syntactic duplicates are merged, as
// in Tweety's PlBeliefSet) together with source information.
class KnowledgeBase {
  constructor(formulas, texts, lines) {
    this.formulas = formulas;
    this.texts = texts || formulas.map(f => toPretty(f));
    this.lines = lines || formulas.map((_, i) => i + 1);
    const set = new Set();
    for (const f of formulas) for (const a of atoms(f)) set.add(a);
    this.atoms = Array.from(set).sort(cmpNames);
    this.atomIndex = new Map(this.atoms.map((a, i) => [a, i]));
  }
  get size() { return this.formulas.length; }
  key() {
    if (this._key === undefined) this._key = this.formulas.map(key).join('\n');
    return this._key;
  }
  subset(indices) {
    return new KnowledgeBase(indices.map(i => this.formulas[i]), indices.map(i => this.texts[i]), indices.map(i => this.lines[i]));
  }
  static fromFormulas(formulas) {
    const seen = new Set(), fs = [];
    for (const f of formulas) { const k = key(f); if (!seen.has(k)) { seen.add(k); fs.push(f); } }
    return new KnowledgeBase(fs);
  }
  toTweetyString() { return this.formulas.map(toTweetyString).join('\n'); }
}

// Parse a knowledge base given as text, one formula per line.
// Returns {kb, errors:[{line, col, message, text}], duplicates:[{line, firstLine}]}
function parseKB(text) {
  const lines = text.split(/\r\n|\r|\n/);
  const formulas = [], texts = [], lineNos = [], errors = [], duplicates = [];
  const seen = new Map();
  lines.forEach((raw, i) => {
    const t = raw.trim();
    if (t === '' || t[0] === '%' || t[0] === '#') return;
    try {
      const f = parseFormula(t);
      const k = key(f);
      if (seen.has(k)) { duplicates.push({ line: i + 1, firstLine: seen.get(k) }); return; }
      seen.set(k, i + 1);
      formulas.push(f); texts.push(t); lineNos.push(i + 1);
    } catch (e) {
      if (e instanceof ParseError) {
        const lead = raw.length - raw.trimStart().length;
        errors.push({ line: i + 1, col: (e.pos || 0) + lead + 1, message: e.message, text: t });
      } else throw e;
    }
  });
  return { kb: new KnowledgeBase(formulas, texts, lineNos), errors, duplicates };
}

// DIMACS CNF -> knowledge base with one clause per formula.
function parseDimacs(text) {
  const formulas = [];
  let cur = [];
  for (const raw of text.split(/\r\n|\r|\n/)) {
    const line = raw.trim();
    if (line === '' || line[0] === 'c' || line[0] === 'p' || line[0] === '%') continue;
    for (const tok of line.split(/\s+/)) {
      const v = parseInt(tok, 10);
      if (isNaN(v)) throw new ParseError('Invalid DIMACS token ' + tok, 0);
      if (v === 0) { formulas.push(cur.length === 0 ? BOT : (cur.length === 1 ? cur[0] : Or(cur))); cur = []; }
      else { const a = Prop('x' + Math.abs(v)); cur.push(v > 0 ? a : Not(a)); }
    }
  }
  if (cur.length) formulas.push(cur.length === 1 ? cur[0] : Or(cur));
  return KnowledgeBase.fromFormulas(formulas);
}

IM.ParseError = ParseError;
IM.parseFormula = parseFormula;
IM.parseKB = parseKB;
IM.parseDimacs = parseDimacs;
IM.KnowledgeBase = KnowledgeBase;

// ===== 03-sat.js =====
// ---------------------------------------------------------------------------
// CDCL SAT solver in the style of MiniSat 2.2
//   - two watched literals, 1-UIP conflict analysis with recursive clause
//     minimisation, VSIDS (binary heap), phase saving, Luby restarts,
//     activity-based learnt clause deletion,
//   - incremental: clauses/variables can be added between calls,
//   - solving under assumptions with extraction of an unsatisfiable core
//     (subset of the assumptions), as needed for MUS enumeration.
// External interface uses DIMACS literals (+v / -v, v >= 1).
// Internally a literal is 2*(v-1) + (negative ? 1 : 0).
// ---------------------------------------------------------------------------

class SatSolver {
  constructor() {
    this.nVars = 0;
    this.ok = true;
    this.clauses = [];       // original clauses
    this.learnts = [];       // learnt clauses
    this.watches = [];       // per literal: watchers {c: clause, b: blocker literal}
    this.lv = new Int8Array(0);   // per literal: 1 true, -1 false, 0 undef
    this.level = new Int32Array(0);
    this.reason = [];
    this.activity = new Float64Array(0);
    this.polarity = new Uint8Array(0); // saved phase: 1 = negative
    this.decisionVar = new Uint8Array(0);
    this.seen = new Uint8Array(0);
    this.trail = [];
    this.trailLim = [];
    this.qhead = 0;
    this.varInc = 1;
    this.claInc = 1;
    this.varDecay = 0.95;
    this.claDecay = 0.999;
    this.heap = [];
    this.heapIdx = new Int32Array(0);
    this.model = null;        // Int8Array: model[v] (1-based) = 1 true / 0 false
    this.core = null;         // DIMACS assumption literals of the final conflict
    this.conflicts = 0;
    this.decisions = 0;
    this.propagations = 0;
    this.maxLearnts = 0;
    this.cap = 0;
  }

  // ----- variables ---------------------------------------------------------
  _grow(n) {
    if (n <= this.cap) return;
    let cap = Math.max(16, this.cap * 2);
    while (cap < n) cap *= 2;
    const g8 = (a, len) => { const b = new a.constructor(len); b.set(a); return b; };
    this.lv = g8(this.lv, 2 * cap);
    this.level = g8(this.level, cap);
    this.activity = g8(this.activity, cap);
    this.polarity = g8(this.polarity, cap);
    this.decisionVar = g8(this.decisionVar, cap);
    this.seen = g8(this.seen, cap);
    this.heapIdx = g8(this.heapIdx, cap);
    this.cap = cap;
  }
  newVar(preferTrue) {
    const v = this.nVars++;
    this._grow(this.nVars);
    this.watches.push([], []);
    this.reason.push(null);
    this.level[v] = 0;
    this.activity[v] = 0;
    this.polarity[v] = preferTrue ? 0 : 1;
    this.decisionVar[v] = 1;
    this.heapIdx[v] = -1;
    this._heapInsert(v);
    return v + 1;
  }
  ensureVars(n) { while (this.nVars < n) this.newVar(); }
  setPolarity(dimacsVar, preferTrue) { this.polarity[dimacsVar - 1] = preferTrue ? 0 : 1; }

  // ----- heap (max-activity) ----------------------------------------------
  _heapLess(a, b) { return this.activity[a] > this.activity[b]; }
  _heapUp(i) {
    const h = this.heap, x = h[i];
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!this._heapLess(x, h[p])) break;
      h[i] = h[p]; this.heapIdx[h[i]] = i; i = p;
    }
    h[i] = x; this.heapIdx[x] = i;
  }
  _heapDown(i) {
    const h = this.heap, x = h[i], n = h.length;
    for (;;) {
      let c = 2 * i + 1;
      if (c >= n) break;
      if (c + 1 < n && this._heapLess(h[c + 1], h[c])) c++;
      if (!this._heapLess(h[c], x)) break;
      h[i] = h[c]; this.heapIdx[h[i]] = i; i = c;
    }
    h[i] = x; this.heapIdx[x] = i;
  }
  _heapInsert(v) {
    if (this.heapIdx[v] >= 0) return;
    this.heap.push(v);
    this.heapIdx[v] = this.heap.length - 1;
    this._heapUp(this.heap.length - 1);
  }
  _heapPop() {
    const h = this.heap;
    const top = h[0];
    const last = h.pop();
    this.heapIdx[top] = -1;
    if (h.length > 0) { h[0] = last; this.heapIdx[last] = 0; this._heapDown(0); }
    return top;
  }

  // ----- activities ---------------------------------------------------------
  _bumpVar(v) {
    if ((this.activity[v] += this.varInc) > 1e100) {
      for (let i = 0; i < this.nVars; i++) this.activity[i] *= 1e-100;
      this.varInc *= 1e-100;
    }
    if (this.heapIdx[v] >= 0) this._heapUp(this.heapIdx[v]);
  }
  _bumpClause(c) {
    if ((c.act += this.claInc) > 1e20) {
      for (const l of this.learnts) l.act *= 1e-20;
      this.claInc *= 1e-20;
    }
  }

  // ----- clauses ------------------------------------------------------------
  _toLit(d) { return d > 0 ? 2 * (d - 1) : 2 * (-d - 1) + 1; }
  _toDimacs(l) { return (l & 1) ? -((l >> 1) + 1) : (l >> 1) + 1; }

  // Add a clause given as an array of DIMACS literals; returns false if the
  // solver became trivially unsatisfiable.
  addClause(dlits) {
    if (!this.ok) return false;
    if (this.trailLim.length > 0) this._cancelUntil(0);
    let maxv = 0;
    for (const d of dlits) { const v = d < 0 ? -d : d; if (v > maxv) maxv = v; }
    this.ensureVars(maxv);
    const lits = [];
    const set = new Set();
    for (const d of dlits) {
      const l = this._toLit(d);
      if (set.has(l ^ 1)) return true;       // tautology
      if (set.has(l)) continue;
      const val = this.lv[l];
      if (val === 1) return true;            // satisfied at level 0
      if (val === -1) continue;              // false at level 0
      set.add(l); lits.push(l);
    }
    if (lits.length === 0) { this.ok = false; return false; }
    if (lits.length === 1) {
      this._enqueue(lits[0], null);
      if (this._propagate() !== null) { this.ok = false; return false; }
      return true;
    }
    const c = { lits, learnt: false, act: 0, removed: false };
    this.clauses.push(c);
    this._attach(c);
    return true;
  }
  // watchers carry a "blocker" literal of the clause; if it is true the
  // clause need not be inspected during propagation
  _attach(c) {
    this.watches[c.lits[0]].push({ c, b: c.lits[1] });
    this.watches[c.lits[1]].push({ c, b: c.lits[0] });
  }

  // ----- assignment ---------------------------------------------------------
  _decisionLevel() { return this.trailLim.length; }
  _enqueue(l, from) {
    const v = l >> 1;
    this.lv[l] = 1; this.lv[l ^ 1] = -1;
    this.level[v] = this.trailLim.length;
    this.reason[v] = from;
    this.trail.push(l);
  }
  _cancelUntil(lvl) {
    if (this.trailLim.length <= lvl) return;
    const lim = this.trailLim[lvl];
    for (let i = this.trail.length - 1; i >= lim; i--) {
      const l = this.trail[i], v = l >> 1;
      this.lv[l] = 0; this.lv[l ^ 1] = 0;
      this.reason[v] = null;
      this.polarity[v] = l & 1;
      this._heapInsert(v);
    }
    this.trail.length = lim;
    this.trailLim.length = lvl;
    this.qhead = Math.min(this.qhead, lim);
  }

  _propagate() {
    const lv = this.lv;
    let confl = null;
    while (this.qhead < this.trail.length) {
      const p = this.trail[this.qhead++];
      const falseLit = p ^ 1;
      const ws = this.watches[falseLit];
      const n = ws.length;
      let i = 0, j = 0;
      this.propagations++;
      while (i < n) {
        const w = ws[i++];
        if (lv[w.b] === 1) { ws[j++] = w; continue; }   // blocker satisfied: clause untouched
        const c = w.c;
        if (c.removed) continue;
        const lits = c.lits;
        if (lits[0] === falseLit) { lits[0] = lits[1]; lits[1] = falseLit; }
        const first = lits[0];
        if (lv[first] === 1) { w.b = first; ws[j++] = w; continue; }
        let found = false;
        for (let k = 2, len = lits.length; k < len; k++) {
          const lk = lits[k];
          if (lv[lk] !== -1) {
            lits[1] = lk; lits[k] = falseLit;
            w.b = first;
            this.watches[lk].push(w);
            found = true; break;
          }
        }
        if (found) continue;
        ws[j++] = w;
        if (lv[first] === -1) {
          confl = c;
          this.qhead = this.trail.length;
          while (i < n) ws[j++] = ws[i++];
        } else {
          this._enqueue(first, c);
        }
      }
      ws.length = j;
      if (confl !== null) return confl;
    }
    return null;
  }

  // ----- conflict analysis --------------------------------------------------
  _analyze(confl) {
    const seen = this.seen;
    const learnt = [0];
    let pathC = 0, p = -1;
    let index = this.trail.length - 1;
    const dl = this._decisionLevel();
    const toClear = [];
    do {
      if (confl.learnt) this._bumpClause(confl);
      const lits = confl.lits;
      for (let k = (p === -1 ? 0 : 1); k < lits.length; k++) {
        const q = lits[k], v = q >> 1;
        if (!seen[v] && this.level[v] > 0) {
          this._bumpVar(v);
          seen[v] = 1; toClear.push(v);
          if (this.level[v] >= dl) pathC++;
          else learnt.push(q);
        }
      }
      while (!seen[this.trail[index] >> 1]) index--;
      p = this.trail[index];
      index--;
      confl = this.reason[p >> 1];
      seen[p >> 1] = 0;
      pathC--;
    } while (pathC > 0);
    learnt[0] = p ^ 1;

    // recursive minimisation
    let abstractLevels = 0;
    for (let i = 1; i < learnt.length; i++) abstractLevels |= 1 << (this.level[learnt[i] >> 1] & 31);
    let j = 1;
    for (let i = 1; i < learnt.length; i++) {
      const v = learnt[i] >> 1;
      if (this.reason[v] === null || !this._litRedundant(learnt[i], abstractLevels, toClear)) learnt[j++] = learnt[i];
    }
    learnt.length = j;

    // find backtrack level
    let btLevel = 0;
    if (learnt.length > 1) {
      let maxI = 1;
      for (let i = 2; i < learnt.length; i++) if (this.level[learnt[i] >> 1] > this.level[learnt[maxI] >> 1]) maxI = i;
      const tmp = learnt[maxI]; learnt[maxI] = learnt[1]; learnt[1] = tmp;
      btLevel = this.level[learnt[1] >> 1];
    }
    for (const v of toClear) seen[v] = 0;
    return { learnt, btLevel };
  }
  _litRedundant(p, abstractLevels, toClear) {
    const stack = [p];
    const top = toClear.length;
    const seen = this.seen;
    while (stack.length > 0) {
      const q = stack.pop();
      const c = this.reason[q >> 1];
      const lits = c.lits;
      for (let i = 1; i < lits.length; i++) {
        const l = lits[i], v = l >> 1;
        if (!seen[v] && this.level[v] > 0) {
          if (this.reason[v] !== null && (abstractLevels & (1 << (this.level[v] & 31))) !== 0) {
            seen[v] = 1; stack.push(l); toClear.push(v);
          } else {
            for (let k = top; k < toClear.length; k++) seen[toClear[k]] = 0;
            toClear.length = top;
            return false;
          }
        }
      }
    }
    return true;
  }
  // Compute the set of assumptions responsible for literal p being false.
  _analyzeFinal(p) {
    const out = [p];
    if (this._decisionLevel() === 0) return out;
    const seen = this.seen;
    seen[p >> 1] = 1;
    for (let i = this.trail.length - 1; i >= this.trailLim[0]; i--) {
      const x = this.trail[i] >> 1;
      if (seen[x]) {
        const r = this.reason[x];
        if (r === null) { if (this.level[x] > 0) out.push(this.trail[i] ^ 1); }
        else { for (let k = 1; k < r.lits.length; k++) { const v = r.lits[k] >> 1; if (this.level[v] > 0) seen[v] = 1; } }
        seen[x] = 0;
      }
    }
    seen[p >> 1] = 0;
    return out;
  }

  _reduceDB() {
    const ls = this.learnts;
    ls.sort((a, b) => (a.lits.length <= 2 ? 1 : 0) - (b.lits.length <= 2 ? 1 : 0) || a.act - b.act);
    const extraLim = this.claInc / Math.max(1, ls.length);
    const half = ls.length >> 1;
    let j = 0;
    for (let i = 0; i < ls.length; i++) {
      const c = ls[i];
      const locked = this.reason[c.lits[0] >> 1] === c && this.lv[c.lits[0]] === 1;
      if (c.lits.length > 2 && !locked && (i < half || c.act < extraLim)) c.removed = true;
      else ls[j++] = c;
    }
    ls.length = j;
  }

  _pickBranchLit() {
    while (this.heap.length > 0) {
      const v = this._heapPop();
      if (this.lv[2 * v] === 0 && this.decisionVar[v]) return 2 * v + this.polarity[v];
    }
    return -1;
  }

  static luby(y, x) {
    let size = 1, seq = 0;
    while (size < x + 1) { seq++; size = 2 * size + 1; }
    while (size - 1 !== x) { size = (size - 1) >> 1; seq--; x = x % size; }
    return Math.pow(y, seq);
  }

  // returns 1 (SAT), -1 (UNSAT), 0 (restart)
  _search(nofConflicts, assumps) {
    let conflictC = 0;
    for (;;) {
      const confl = this._propagate();
      if (confl !== null) {
        this.conflicts++; conflictC++;
        if ((this.conflicts & 255) === 0) checkDeadlineNow();
        if (this._decisionLevel() === 0) { this.ok = false; return -1; }
        const { learnt, btLevel } = this._analyze(confl);
        this._cancelUntil(btLevel);
        if (learnt.length === 1) {
          this._enqueue(learnt[0], null);
        } else {
          const c = { lits: learnt, learnt: true, act: 0, removed: false };
          this.learnts.push(c);
          this._attach(c);
          this._bumpClause(c);
          this._enqueue(learnt[0], c);
        }
        this.varInc /= this.varDecay;
        this.claInc /= this.claDecay;
      } else {
        if (nofConflicts >= 0 && conflictC >= nofConflicts) { this._cancelUntil(0); return 0; }
        if (this.learnts.length - this.trail.length >= this.maxLearnts) this._reduceDB();
        let next = -1;
        while (this._decisionLevel() < assumps.length) {
          const p = assumps[this._decisionLevel()];
          if (this.lv[p] === 1) {
            this.trailLim.push(this.trail.length);   // dummy decision level
          } else if (this.lv[p] === -1) {
            const conf = this._analyzeFinal(p ^ 1);
            this.core = conf.map(l => this._toDimacs(l ^ 1));
            return -1;
          } else { next = p; break; }
        }
        if (next === -1) {
          this.decisions++;
          next = this._pickBranchLit();
          if (next === -1) return 1;
        }
        this.trailLim.push(this.trail.length);
        this._enqueue(next, null);
      }
    }
  }

  // Solve under the given DIMACS assumption literals. Returns true / false.
  solve(assumptions) {
    this.model = null;
    this.core = null;
    if (!this.ok) { this.core = []; return false; }
    const assumps = [];
    if (assumptions) {
      let maxv = 0;
      for (const d of assumptions) { const v = d < 0 ? -d : d; if (v > maxv) maxv = v; }
      this.ensureVars(maxv);
      for (const d of assumptions) assumps.push(this._toLit(d));
    }
    this.maxLearnts = Math.max(this.clauses.length / 3, 100);
    let status = 0, curr = 0;
    try {
      while (status === 0) {
        const rest = SatSolver.luby(2, curr) * 100;
        status = this._search(rest, assumps);
        curr++;
        this.maxLearnts *= 1.05;
      }
      if (status === 1) {
        const m = new Int8Array(this.nVars + 1);
        for (let v = 0; v < this.nVars; v++) m[v + 1] = this.lv[2 * v] === 1 ? 1 : 0;
        this.model = m;
      } else if (this.core === null) {
        this.core = [];   // unsatisfiable independently of the assumptions
      }
    } finally {
      this._cancelUntil(0);
    }
    return status === 1;
  }

  modelValue(dimacsLit) {
    const v = dimacsLit > 0 ? dimacsLit : -dimacsLit;
    const val = this.model[v] === 1;
    return dimacsLit > 0 ? val : !val;
  }
}

// Convenience: decide satisfiability of a CNF given as array of DIMACS clauses.
function solveCnf(clauses, nVars) {
  const s = new SatSolver();
  s.ensureVars(nVars || 0);
  for (const c of clauses) if (!s.addClause(c)) break;
  const sat = s.solve();
  return { sat, model: s.model };
}

function parseDimacsCnf(text) {
  const clauses = [];
  let nVars = 0, cur = [];
  for (const raw of text.split(/\r?\n/)) {
    const line = raw.trim();
    if (line === '' || line[0] === 'c' || line[0] === '%') continue;
    if (line[0] === 'p') { const parts = line.split(/\s+/); nVars = parseInt(parts[2], 10); continue; }
    for (const tok of line.split(/\s+/)) {
      const v = parseInt(tok, 10);
      if (v === 0) { clauses.push(cur); cur = []; } else { cur.push(v); nVars = Math.max(nVars, Math.abs(v)); }
    }
  }
  if (cur.length) clauses.push(cur);
  return { nVars, clauses };
}

IM.SatSolver = SatSolver;
IM.solveCnf = solveCnf;
IM.parseDimacsCnf = parseDimacsCnf;

// ===== 04-encode.js =====
// ---------------------------------------------------------------------------
// CNF encodings on top of the SAT solver
//   Encoder:    Tseitin transformation with structural hashing (full
//               equivalences, so encoded literals may be used in both
//               polarities)
//   totalizer:  cardinality network (Bailleux & Boufkhad) with outputs
//               out[j] <- (at least j+1 inputs true)
//   minimizeTrueCount: SAT-UNSAT linear search for the minimum number of
//               true literals among a set of inputs
// ---------------------------------------------------------------------------

class Encoder {
  // atomLit: optional function (name) -> DIMACS literal; default allocates one
  // variable per atom name.
  constructor(solver, atomLit) {
    this.s = solver;
    this.atomVars = new Map();
    this.atomLit = atomLit || ((name) => {
      let v = this.atomVars.get(name);
      if (v === undefined) { v = this.s.newVar(); this.atomVars.set(name, v); }
      return v;
    });
    this.cache = new Map();
    this._true = 0;
  }
  trueLit() {
    if (!this._true) { this._true = this.s.newVar(); this.s.addClause([this._true]); }
    return this._true;
  }
  andGate(lits) {
    if (lits.length === 0) return this.trueLit();
    if (lits.length === 1) return lits[0];
    const g = this.s.newVar();
    const big = [g];
    for (const l of lits) { this.s.addClause([-g, l]); big.push(-l); }
    this.s.addClause(big);
    return g;
  }
  orGate(lits) {
    if (lits.length === 0) return -this.trueLit();
    if (lits.length === 1) return lits[0];
    const g = this.s.newVar();
    const big = [-g];
    for (const l of lits) { this.s.addClause([g, -l]); big.push(l); }
    this.s.addClause(big);
    return g;
  }
  xorGate(a, b) {
    const g = this.s.newVar();
    this.s.addClause([-g, a, b]); this.s.addClause([-g, -a, -b]);
    this.s.addClause([g, -a, b]); this.s.addClause([g, a, -b]);
    return g;
  }
  lit(f) {
    if (f.t === 'prop') return this.atomLit(f.name);
    if (f.t === 'top') return this.trueLit();
    if (f.t === 'bot') return -this.trueLit();
    if (f.t === 'not') return -this.lit(f.k[0]);
    const k = key(f);
    const cached = this.cache.get(k);
    if (cached !== undefined) return cached;
    let r;
    switch (f.t) {
      case 'and': r = this.andGate(f.k.map(g => this.lit(g))); break;
      case 'or': r = this.orGate(f.k.map(g => this.lit(g))); break;
      case 'xor': {
        if (f.k.length === 0) { r = -this.trueLit(); break; }
        r = this.lit(f.k[0]);
        for (let i = 1; i < f.k.length; i++) r = this.xorGate(r, this.lit(f.k[i]));
        break;
      }
      case 'impl': r = this.orGate([-this.lit(f.k[0]), this.lit(f.k[1])]); break;
      case 'equiv': r = -this.xorGate(this.lit(f.k[0]), this.lit(f.k[1])); break;
      default: throw new Error('Unknown formula type ' + f.t);
    }
    this.cache.set(k, r);
    return r;
  }
  assert(f) { this.s.addClause([this.lit(f)]); }
}

// Totalizer over DIMACS input literals; returns out[0..n-1] with
// (#true inputs >= j+1) -> out[j].
function totalizer(solver, inputs) {
  function build(lits) {
    if (lits.length === 1) return [lits[0]];
    const mid = lits.length >> 1;
    const a = build(lits.slice(0, mid)), b = build(lits.slice(mid));
    const r = [];
    for (let k = 0; k < a.length + b.length; k++) r.push(solver.newVar());
    for (let i = 0; i <= a.length; i++) {
      for (let j = 0; j <= b.length; j++) {
        if (i + j === 0) continue;
        const cl = [r[i + j - 1]];
        if (i > 0) cl.push(-a[i - 1]);
        if (j > 0) cl.push(-b[j - 1]);
        solver.addClause(cl);
      }
    }
    return r;
  }
  if (inputs.length === 0) return [];
  return build(inputs);
}

function countTrue(solver, lits) {
  let c = 0;
  for (const l of lits) if (solver.modelValue(l)) c++;
  return c;
}

// Minimum number of true literals among `inputs` over all models of the
// solver's clauses (Infinity if unsatisfiable). Adds clauses to the solver.
function minimizeTrueCount(solver, inputs, assumptions) {
  assumptions = assumptions || [];
  if (!solver.solve(assumptions)) return Infinity;
  if (inputs.length === 0) return 0;
  let best = countTrue(solver, inputs);
  if (best === 0) return 0;
  const out = totalizer(solver, inputs);
  while (best > 0) {
    solver.addClause([-out[best - 1]]);
    if (!solver.solve(assumptions)) break;
    best = countTrue(solver, inputs);
  }
  return best;
}

// Does the conjunction of `premises` entail `conclusion`?
function entails(premises, conclusion) {
  const s = new SatSolver();
  const enc = new Encoder(s);
  for (const f of premises) enc.assert(f);
  s.addClause([-enc.lit(conclusion)]);
  return !s.solve();
}

function isSatisfiable(formulas) {
  const s = new SatSolver();
  const enc = new Encoder(s);
  for (const f of formulas) enc.assert(f);
  return s.solve();
}

function equivalent(f, g) { return entails([f], g) && entails([g], f); }

IM.Encoder = Encoder;
IM.totalizer = totalizer;
IM.minimizeTrueCount = minimizeTrueCount;
IM.entails = entails;
IM.isSatisfiable = isSatisfiable;
IM.equivalent = equivalent;

// ===== 05-analysis.js =====
// ---------------------------------------------------------------------------
// Knowledge base analysis: consistency, minimal inconsistent subsets (MUS),
// maximal consistent subsets (MSS) and minimal correction sets (MCS).
//
// TweetyProject uses a naive MUS enumerator and derives MCS as irreducible
// hitting sets of the MUS. Here both are enumerated simultaneously with the
// MARCO algorithm (Liffiton et al.), which yields exactly the same sets.
// Formulas are referred to by their index in the knowledge base.
// ---------------------------------------------------------------------------

class KBAnalysis {
  constructor(kb) {
    this.kb = kb;
    this.n = kb.size;
    this._solver = null;
    this._enum = null;
    this._consistent = undefined;
    this._selfContra = null;
    this.satCalls = 0;
  }

  _init() {
    if (this._solver) return;
    const s = new SatSolver();
    const enc = new Encoder(s);
    this.sel = [];
    this.out = [];
    this.selIndex = new Map();
    this.kb.formulas.forEach((f, i) => {
      const o = enc.lit(f);
      const sv = s.newVar();
      s.addClause([-sv, o]);
      this.sel.push(sv);
      this.out.push(o);
      this.selIndex.set(sv, i);
    });
    this.encoder = enc;
    this._solver = s;
  }

  // Is the subset (array of indices) consistent? If so, the solver model is
  // available via this._solver.model.
  isConsistentSubset(indices) {
    this._init();
    this.satCalls++;
    checkDeadline();
    return this._solver.solve(indices.map(i => this.sel[i]));
  }

  isConsistent() {
    if (this._consistent === undefined) {
      this._consistent = this.isConsistentSubset(this.kb.formulas.map((_, i) => i));
    }
    return this._consistent;
  }

  // indices of formulas that are unsatisfiable on their own
  selfContradictory() {
    if (!this._selfContra) {
      this._selfContra = [];
      for (let i = 0; i < this.n; i++) if (!this.isConsistentSubset([i])) this._selfContra.push(i);
    }
    return this._selfContra;
  }

  _coreIndices() {
    const res = [];
    for (const l of this._solver.core) { const i = this.selIndex.get(l); if (i !== undefined) res.push(i); }
    return sortedUnique(res);
  }

  _satisfiedByModel() {
    const res = [];
    for (let i = 0; i < this.n; i++) if (this._solver.modelValue(this.out[i])) res.push(i);
    return res;
  }

  _grow(seed) {
    const inSet = new Uint8Array(this.n);
    for (const i of this._satisfiedByModel()) inSet[i] = 1;
    for (const i of seed) inSet[i] = 1;
    for (let j = 0; j < this.n; j++) {
      if (inSet[j]) continue;
      const cand = [];
      for (let i = 0; i < this.n; i++) if (inSet[i] || i === j) cand.push(i);
      if (this.isConsistentSubset(cand)) {
        for (const i of this._satisfiedByModel()) inSet[i] = 1;
        inSet[j] = 1;
      }
    }
    const res = [];
    for (let i = 0; i < this.n; i++) if (inSet[i]) res.push(i);
    return res;
  }

  _shrink(core) {
    let cur = core.slice();
    const necessary = new Set();
    for (;;) {
      const cand = cur.find(i => !necessary.has(i));
      if (cand === undefined) break;
      const test = cur.filter(i => i !== cand);
      if (!this.isConsistentSubset(test)) cur = this._coreIndices();
      else necessary.add(cand);
    }
    return cur;
  }

  // Enumerate all MUS and MSS (and MCS = complements of MSS).
  enumerate() {
    if (this._enum) return this._enum;
    this._init();
    const n = this.n;
    const map = new SatSolver();
    for (let i = 0; i < n; i++) map.newVar(true);
    const muses = [], msses = [];
    while (map.solve()) {
      checkDeadline();
      const seed = [];
      for (let i = 0; i < n; i++) if (map.model[i + 1] === 1) seed.push(i);
      if (this.isConsistentSubset(seed)) {
        const mss = this._grow(seed);
        msses.push(mss);
        const inMss = new Uint8Array(n);
        for (const i of mss) inMss[i] = 1;
        const block = [];
        for (let i = 0; i < n; i++) if (!inMss[i]) block.push(i + 1);
        if (!map.addClause(block)) break;
      } else {
        const mus = this._shrink(this._coreIndices());
        muses.push(mus);
        if (!map.addClause(mus.map(i => -(i + 1)))) break;
      }
    }
    muses.sort(cmpIndexArrays);
    msses.sort(cmpIndexArrays);
    const mcses = msses.map(m => {
      const s = new Set(m);
      const r = [];
      for (let i = 0; i < n; i++) if (!s.has(i)) r.push(i);
      return r;
    }).sort(cmpIndexArrays);
    this._consistent = muses.length === 0;
    this._enum = { muses, msses, mcses };
    return this._enum;
  }

  muses() { return this.enumerate().muses; }
  msses() { return this.enumerate().msses; }
  mcses() { return this.enumerate().mcses; }

  freeFormulas() {
    const inMus = new Uint8Array(this.n);
    for (const m of this.muses()) for (const i of m) inMus[i] = 1;
    const r = [];
    for (let i = 0; i < this.n; i++) if (!inMus[i]) r.push(i);
    return r;
  }

  problematicFormulas() {
    const s = new Set();
    for (const m of this.muses()) for (const i of m) s.add(i);
    return Array.from(s).sort((a, b) => a - b);
  }

  // Connected components of overlapping MUS (Tweety's getMiComponents).
  miComponents() {
    const comps = this.muses().map(m => new Set(m));
    let changed = true;
    while (changed) {
      changed = false;
      outer: for (let i = 0; i < comps.length; i++) {
        for (let j = i + 1; j < comps.length; j++) {
          for (const x of comps[j]) {
            if (comps[i].has(x)) {
              for (const y of comps[j]) comps[i].add(y);
              comps.splice(j, 1);
              changed = true;
              break outer;
            }
          }
        }
      }
    }
    return comps.map(c => Array.from(c).sort((a, b) => a - b));
  }
}

// MUS enumeration for an arbitrary list of formulas (no caching).
function minimalInconsistentSubsets(formulas) {
  return new KBAnalysis(new KnowledgeBase(formulas)).muses();
}

IM.KBAnalysis = KBAnalysis;
IM.minimalInconsistentSubsets = minimalInconsistentSubsets;

// ===== 06-optim.js =====
// ---------------------------------------------------------------------------
// Optimisation
//   lpMaximize: dense two-phase primal simplex (Dantzig pricing with Bland's
//               rule as anti-cycling fallback); variables are non-negative.
//   minimizeBox: derivative-free minimisation over [0,1]^n (multi-start
//               coordinate descent with grid + golden-section line search,
//               followed by a pattern search), used by the fuzzy measures.
// ---------------------------------------------------------------------------

// constraints: [{a: Float64Array|Array (length nv), op: '<='|'>='|'=', b: number}]
function lpMaximize(nv, c, constraints) {
  const EPS = 1e-10;
  const rows = constraints.map(r => {
    let a = Array.from(r.a), b = r.b, op = r.op;
    if (b < 0) { a = a.map(x => -x); b = -b; op = op === '<=' ? '>=' : (op === '>=' ? '<=' : '='); }
    return { a, b, op };
  });
  const m = rows.length;
  let nSlack = 0, nArt = 0;
  for (const r of rows) { if (r.op !== '=') nSlack++; if (r.op !== '<=') nArt++; }
  const N = nv + nSlack + nArt;          // number of columns (without rhs)
  const T = [];                          // tableau rows, last entry = rhs
  const basis = new Int32Array(m);
  let si = nv, ai = nv + nSlack;
  const isArt = new Uint8Array(N);
  rows.forEach((r, i) => {
    const row = new Float64Array(N + 1);
    for (let j = 0; j < nv; j++) row[j] = r.a[j] || 0;
    row[N] = r.b;
    if (r.op === '<=') { row[si] = 1; basis[i] = si; si++; }
    else if (r.op === '>=') { row[si] = -1; si++; row[ai] = 1; basis[i] = ai; isArt[ai] = 1; ai++; }
    else { row[ai] = 1; basis[i] = ai; isArt[ai] = 1; ai++; }
    T.push(row);
  });

  function pivot(pr, pc) {
    const prow = T[pr];
    const pv = prow[pc];
    for (let j = 0; j <= N; j++) prow[j] /= pv;
    for (let i = 0; i < m; i++) {
      if (i === pr) continue;
      const row = T[i], f = row[pc];
      if (f !== 0) { for (let j = 0; j <= N; j++) row[j] -= f * prow[j]; row[pc] = 0; }
    }
    basis[pr] = pc;
  }

  // maximise objective vector obj (length N); returns 'optimal' or 'unbounded'
  function optimize(obj, allowed) {
    let degenerate = 0, iter = 0;
    for (;;) {
      if ((++iter & 63) === 0) checkDeadlineNow();
      // reduced costs d_j = obj_j - sum_i obj_{basis i} T_ij
      let enter = -1, best = EPS;
      const useBland = degenerate > 50;
      for (let j = 0; j < N; j++) {
        if (!allowed(j)) continue;
        let d = obj[j];
        for (let i = 0; i < m; i++) { const cb = obj[basis[i]]; if (cb !== 0) d -= cb * T[i][j]; }
        if (d > best) { enter = j; if (useBland) break; best = d; }
      }
      if (enter === -1) return 'optimal';
      let leave = -1, minRatio = Infinity;
      for (let i = 0; i < m; i++) {
        const a = T[i][enter];
        if (a > EPS) {
          const ratio = T[i][N] / a;
          if (ratio < minRatio - EPS || (Math.abs(ratio - minRatio) <= EPS && basis[i] < basis[leave])) { minRatio = ratio; leave = i; }
        }
      }
      if (leave === -1) return 'unbounded';
      degenerate = minRatio <= EPS ? degenerate + 1 : 0;
      pivot(leave, enter);
    }
  }

  // phase 1
  if (nArt > 0) {
    const obj1 = new Float64Array(N);
    for (let j = 0; j < N; j++) if (isArt[j]) obj1[j] = -1;
    optimize(obj1, () => true);
    let infeas = 0;
    for (let i = 0; i < m; i++) if (isArt[basis[i]]) infeas += T[i][N];
    if (infeas > 1e-7) return { status: 'infeasible' };
    // drive artificials out of the basis
    for (let i = 0; i < m; i++) {
      if (!isArt[basis[i]]) continue;
      let pc = -1;
      for (let j = 0; j < N; j++) if (!isArt[j] && Math.abs(T[i][j]) > 1e-9) { pc = j; break; }
      if (pc >= 0) pivot(i, pc);
      // otherwise the row is redundant; the artificial stays basic at value 0
    }
  }
  const obj2 = new Float64Array(N);
  for (let j = 0; j < nv; j++) obj2[j] = c[j] || 0;
  const st = optimize(obj2, j => !isArt[j]);
  if (st === 'unbounded') return { status: 'unbounded' };
  const x = new Float64Array(nv);
  for (let i = 0; i < m; i++) if (basis[i] < nv) x[basis[i]] = T[i][N];
  let value = 0;
  for (let j = 0; j < nv; j++) value += (c[j] || 0) * x[j];
  return { status: 'optimal', value, x };
}

// Derivative-free minimisation of f over [0,1]^n.
// options: {starts: [vectors], rng, maxSweeps}
function minimizeBox(f, n, options) {
  options = options || {};
  const rng = options.rng || makeRng(12345);
  if (n === 0) { const v = f(new Float64Array(0)); return { value: v, x: new Float64Array(0) }; }
  const starts = (options.starts || []).map(s => Float64Array.from(s));
  const nRandom = options.randomStarts == null ? 12 : options.randomStarts;
  for (let r = 0; r < nRandom; r++) { const x = new Float64Array(n); for (let i = 0; i < n; i++) x[i] = rng(); starts.push(x); }
  const GR = (Math.sqrt(5) - 1) / 2;

  function lineMin(x, i, fx) {
    const orig = x[i];
    let bestT = orig, bestV = fx;
    const G = 20;
    for (let g = 0; g <= G; g++) {
      x[i] = g / G;
      const v = f(x);
      if (v < bestV - 1e-15) { bestV = v; bestT = x[i]; }
    }
    let lo = Math.max(0, bestT - 1 / G), hi = Math.min(1, bestT + 1 / G);
    let a = hi - GR * (hi - lo), b = lo + GR * (hi - lo);
    x[i] = a; let fa = f(x);
    x[i] = b; let fb = f(x);
    for (let it = 0; it < 40; it++) {
      if (fa < fb) { hi = b; b = a; fb = fa; a = hi - GR * (hi - lo); x[i] = a; fa = f(x); }
      else { lo = a; a = b; fa = fb; b = lo + GR * (hi - lo); x[i] = b; fb = f(x); }
    }
    if (fa < bestV) { bestV = fa; bestT = a; }
    if (fb < bestV) { bestV = fb; bestT = b; }
    x[i] = bestT;
    return bestV;
  }

  function local(x0) {
    const x = Float64Array.from(x0);
    let fx = f(x);
    const maxSweeps = options.maxSweeps || 60;
    for (let sweep = 0; sweep < maxSweeps; sweep++) {
      checkDeadline();
      const before = fx;
      for (let i = 0; i < n; i++) fx = lineMin(x, i, fx);
      if (before - fx < 1e-13) break;
    }
    // pattern search along random directions (escapes coordinate-wise kinks)
    let step = 0.1;
    const dir = new Float64Array(n), y = new Float64Array(n);
    while (step > 1e-9) {
      checkDeadline();
      let improved = false;
      for (let k = 0; k < 4 * n + 4; k++) {
        let norm = 0;
        for (let i = 0; i < n; i++) { dir[i] = rng() * 2 - 1; norm += dir[i] * dir[i]; }
        norm = Math.sqrt(norm) || 1;
        for (let i = 0; i < n; i++) y[i] = Math.min(1, Math.max(0, x[i] + step * dir[i] / norm));
        const fy = f(y);
        if (fy < fx - 1e-15) { x.set(y); fx = fy; improved = true; }
      }
      if (!improved) step /= 2;
    }
    return { x, value: fx };
  }

  let best = null;
  for (const s of starts) {
    const r = local(s);
    if (best === null || r.value < best.value) best = r;
  }
  return best;
}

IM.lpMaximize = lpMaximize;
IM.minimizeBox = minimizeBox;

// ===== 07-measures.js =====
// ---------------------------------------------------------------------------
// Inconsistency measures (translation of org.tweetyproject.logics.commons.
// analysis.* and org.tweetyproject.logics.pl.analysis.*).
//
// Every measure maps a knowledge base to a number (possibly Infinity / NaN,
// following the conventions of the Java implementation). Measures receive a
// context {kb, an} where `an` is a (shared, caching) KBAnalysis.
// ---------------------------------------------------------------------------

const MEASURES = [];
const MEASURE_BY_ID = new Map();
function defineMeasure(spec) { MEASURES.push(spec); MEASURE_BY_ID.set(spec.id, spec); }

function bitsOf(n, arr) { return BitSet.of(n, arr); }

// ----- MUS-based measures ---------------------------------------------------

defineMeasure({
  id: 'drastic', label: 'Drastic', symbol: 'I_d', family: 'Basic',
  java: 'DrasticInconsistencyMeasure',
  description: '0 if the knowledge base is consistent, 1 otherwise.',
  reference: 'Hunter, Konieczny. Approaches to measuring inconsistent information. 2005',
  compute(ctx) { return ctx.an.isConsistent() ? 0 : 1; },
});

defineMeasure({
  id: 'mi', label: 'MI', symbol: 'I_MI', family: 'MUS-based',
  java: 'MiInconsistencyMeasure',
  description: 'Number of minimal inconsistent subsets.',
  reference: 'Hunter, Konieczny. On the measure of conflicts: Shapley inconsistency values. AIJ 2010',
  compute(ctx) { return ctx.an.muses().length; },
});

defineMeasure({
  id: 'mic', label: 'MIC', symbol: 'I_MI^C', family: 'MUS-based',
  java: 'MicInconsistencyMeasure',
  description: 'Sum of 1/|M| over all minimal inconsistent subsets M.',
  reference: 'Hunter, Konieczny. On the measure of conflicts: Shapley inconsistency values. AIJ 2010',
  compute(ctx) { let v = 0; for (const m of ctx.an.muses()) v += 1 / m.length; return v; },
});

defineMeasure({
  id: 'nmi', label: 'Normalized MI', symbol: 'I_MI^n', family: 'MUS-based',
  java: 'NormalizedMiInconsistencyMeasure',
  description: 'MI divided by the maximal number of minimal inconsistent subsets, C(|K|, ⌈|K|/2⌉).',
  reference: 'Thimm. Probabilistic reasoning with incomplete and inconsistent beliefs. PhD thesis, 2011',
  compute(ctx) {
    const v = ctx.an.muses().length;
    if (v === 0) return 0;
    const n = ctx.kb.size;
    return v / binomial(n, Math.ceil(n / 2));
  },
});

defineMeasure({
  id: 'nmic', label: 'Normalized MIC', symbol: 'I_MI^C,n', family: 'MUS-based',
  java: 'NormalizedMicInconsistencyMeasure',
  description: 'MIC divided by C(|K|, ⌈|K|/2⌉)/2.',
  reference: 'Thimm. Probabilistic reasoning with incomplete and inconsistent beliefs. PhD thesis, 2011',
  compute(ctx) {
    let v = 0;
    for (const m of ctx.an.muses()) v += 1 / m.length;
    if (v === 0) return 0;
    const n = ctx.kb.size;
    return v / (binomial(n, Math.ceil(n / 2)) / 2);
  },
});

defineMeasure({
  id: 'pr', label: 'Problematic (P)', symbol: 'I_P', family: 'MUS-based',
  java: 'PrInconsistencyMeasure',
  description: 'Number of formulas that belong to at least one minimal inconsistent subset.',
  reference: 'Grant, Hunter. Measuring consistency gain and information loss in stepwise inconsistency resolution. ECSQARU 2011',
  compute(ctx) { return ctx.an.problematicFormulas().length; },
});

defineMeasure({
  id: 'mc', label: 'MaxCons (M)', symbol: 'I_M', family: 'MUS-based',
  java: 'MaInconsistencyMeasure',
  description: 'Number of maximal consistent subsets plus number of self-contradictory formulas, minus 1.',
  reference: 'Grant, Hunter. Measuring consistency gain and information loss in stepwise inconsistency resolution. ECSQARU 2011',
  compute(ctx) { return ctx.an.selfContradictory().length + ctx.an.msses().length - 1; },
});

defineMeasure({
  id: 'nc', label: 'n-Consistency', symbol: 'I_nc', family: 'MUS-based',
  java: 'NConsInconsistencyMeasure',
  description: '|K| minus the size of the smallest minimal inconsistent subset plus 1 (0 if consistent).',
  reference: 'Doder, Raskovic, Markovic, Ognjanovic. Measures of inconsistency and defaults. IJAR 2010',
  compute(ctx) {
    const muses = ctx.an.muses();
    if (muses.length === 0) return 0;
    let min = ctx.kb.size;
    for (const m of muses) if (m.length < min) min = m.length;
    return ctx.kb.size - min + 1;
  },
});

defineMeasure({
  id: 'mv', label: 'MUS-Var', symbol: 'I_mv', family: 'MUS-based',
  java: 'MusVarInconsistencyMeasure',
  description: 'Fraction of atoms that appear in some minimal inconsistent subset.',
  reference: 'Xiao, Ma. Inconsistency measurement based on variables in minimal unsatisfiable subsets. ECAI 2012',
  compute(ctx) {
    if (ctx.kb.size === 0) return 0;
    const sig = new Set();
    for (const m of ctx.an.muses()) for (const i of m) for (const a of atoms(ctx.kb.formulas[i])) sig.add(a);
    return sig.size / ctx.kb.atoms.length;
  },
});

// Df measure with FracAggrFunction (default in TweetyProject's factory)
function dfConsistentSetCounts(inSet, inSize, rest, musBits, card) {
  checkDeadline();
  for (const mu of musBits) if (mu.isSubsetOf(inSet)) return new Float64Array(card);
  const joint = inSet.clone();
  for (const i of rest) joint.add(i);
  let containsMus = false;
  for (const mu of musBits) if (mu.isSubsetOf(joint)) { containsMus = true; break; }
  if (!containsMus) {
    const result = new Float64Array(card);
    if (inSize > 0) result[inSize - 1] = 1;
    for (let i = 1; i <= rest.length; i++) result[i + inSize - 1] = binomial(rest.length, i);
    return result;
  }
  const f = rest[0], newRest = rest.slice(1);
  const d1 = dfConsistentSetCounts(inSet, inSize, newRest, musBits, card);
  const in2 = inSet.clone().add(f);
  const d2 = dfConsistentSetCounts(in2, inSize + 1, newRest, musBits, card);
  for (let i = 0; i < card; i++) d1[i] += d2[i];
  return d1;
}
function fracAggr(x) {
  let r = 1;
  for (let i = 0; i < x.length; i++) r *= 1 - x[i] / (i + 1);
  return 1 - r;
}
defineMeasure({
  id: 'df', label: 'Df', symbol: 'I_Df', family: 'MUS-based',
  java: 'DfInconsistencyMeasure (FracAggrFunction)',
  description: 'Aggregates, for each size k, the ratio of minimal inconsistent subsets among all MUS and consistent subsets of size k (fractional aggregation 1-∏(1-R_k/k)).',
  reference: 'Mu, Liu, Jin, Bell. A syntax-based approach to measuring the degree of inconsistency for belief bases. IJAR 2011',
  compute(ctx) {
    const n = ctx.kb.size;
    const muses = ctx.an.muses();
    const vcard = new Float64Array(n);
    for (const m of muses) vcard[m.length - 1]++;
    const musBits = muses.map(m => bitsOf(n, m));
    const cn = dfConsistentSetCounts(new BitSet(n), 0, ctx.kb.formulas.map((_, i) => i), musBits, n);
    const ratios = new Float64Array(n);
    for (let i = 0; i < n; i++) ratios[i] = (vcard[i] + cn[i] === 0) ? 0 : vcard[i] / (vcard[i] + cn[i]);
    return fracAggr(ratios);
  },
});

defineMeasure({
  id: 'is', label: 'Independent sets', symbol: 'I_is', family: 'MUS-based',
  java: 'IsInconsistencyMeasure',
  description: 'Natural logarithm of the number of independent sets (sets of pairwise disjoint MUS, including ∅).',
  reference: 'Jabbour, Ma, Raddaoui, Sais. Quantifying conflicts in propositional logic through prime implicates. IJAR 2017',
  compute(ctx) {
    const n = ctx.kb.size;
    const bits = ctx.an.muses().map(m => bitsOf(n, m));
    let count = 0;
    (function rec(i, used) {
      checkDeadline();
      if (i === bits.length) { count++; return; }
      rec(i + 1, used);
      if (!bits[i].intersects(used)) rec(i + 1, used.or(bits[i]));
    })(0, new BitSet(n));
    return Math.log(count);
  },
});

defineMeasure({
  id: 'mcsc', label: 'MCSC', symbol: 'I_mcsc', family: 'MCS-based',
  java: 'McscInconsistencyMeasure',
  description: 'Minimal size of the union of a set of minimal correction sets with empty intersection (∞ if none exists).',
  reference: 'Ammoura, Raddaoui, Salhi, Oukacha. On measuring inconsistency using maximal consistent sets. ECSQARU 2015',
  compute(ctx) {
    if (ctx.an.isConsistent()) return 0;
    const n = ctx.kb.size;
    const md = ctx.an.mcses().map(m => bitsOf(n, m));
    // quick check: all MCS share an element -> no anticover
    let all = BitSet.full(n);
    for (const m of md) all = all.and(m);
    if (!all.isEmpty()) return Infinity;
    let best = Infinity;
    const rec = (j, U, I) => {
      checkDeadline();
      for (let k = j + 1; k < md.length; k++) {
        const U2 = U.or(md[k]);
        const s = U2.count();
        if (s >= best) continue;
        const I2 = I.and(md[k]);
        if (I2.isEmpty()) { best = s; continue; }
        rec(k, U2, I2);
      }
    };
    for (let j = 0; j < md.length; j++) {
      if (md[j].count() >= best) continue;
      rec(j, md[j], md[j]);
    }
    return best;
  },
});

// CC: maximal number of pairwise disjoint MUS M such that no other MUS is
// contained in the union of M (exact search on the constraint system of
// TweetyProject's ILP formulation).
defineMeasure({
  id: 'cc', label: 'CC', symbol: 'I_CC', family: 'MUS-based',
  java: 'CcInconsistencyMeasure (ILP)',
  description: 'Maximal number of minimal inconsistent subsets that can be packed disjointly such that their union contains no other MUS (closed set packing).',
  reference: 'Jabbour, Ma, Raddaoui, Sais, Salhi. On structure-based inconsistency measures and their computations via closed set packing. AAMAS 2015',
  compute(ctx) {
    const n = ctx.kb.size;
    const muses = ctx.an.muses();
    if (muses.length === 0) return 0;
    const bits = muses.map(m => bitsOf(n, m));
    const k = bits.length;
    const chosen = new Uint8Array(k);
    let best = 0;
    const rec = (i, U, c) => {
      checkDeadline();
      if (c + (k - i) <= best) return;
      if (i === k) {
        for (let j = 0; j < k; j++) if (!chosen[j] && bits[j].isSubsetOf(U)) return;
        best = c;
        return;
      }
      if (!bits[i].intersects(U)) {
        const U2 = U.or(bits[i]);
        let ok = true;
        for (let j = 0; j < i; j++) if (!chosen[j] && bits[j].isSubsetOf(U2)) { ok = false; break; }
        if (ok) { chosen[i] = 1; rec(i + 1, U2, c + 1); chosen[i] = 0; }
      }
      if (!bits[i].isSubsetOf(U)) rec(i + 1, U, c);
    };
    rec(0, new BitSet(n), 0);
    return best;
  },
});

// CSP: partition MI(K) into closed set packings P1..Pk with non-increasing
// sizes, maximising sum |Pi| / i (FractionSequenceFunction weights).
defineMeasure({
  id: 'csp', label: 'CSP', symbol: 'I_CSP', family: 'MUS-based',
  java: 'CspInconsistencyMeasure (ILP)',
  description: 'Maximal weighted sum Σ|P_i|/i over partitions of the minimal inconsistent subsets into closed set packings P_1,…,P_k ordered by decreasing size.',
  reference: 'Jabbour. On inconsistency measuring and resolving. ECAI 2016',
  compute(ctx) {
    const n = ctx.kb.size;
    const muses = ctx.an.muses();
    if (muses.length === 0) return 0;
    const bits = muses.map(m => bitsOf(n, m));
    const k = bits.length;
    const blockOf = new Int32Array(k).fill(-1);
    const unions = [], sizes = [];
    let best = -Infinity;
    const objective = () => {
      const s = sizes.slice().sort((a, b) => b - a);
      let v = 0;
      for (let i = 0; i < s.length; i++) v += s[i] / (i + 1);
      return v;
    };
    const closedAfterAdd = (b) => {
      const U = unions[b];
      for (let j = 0; j < k; j++) if (blockOf[j] !== b && bits[j].isSubsetOf(U)) return false;
      return true;
    };
    const rec = (i) => {
      checkDeadline();
      const cur = objective();
      if (cur + (k - i) <= best + 1e-12) return;
      if (i === k) { best = cur; return; }
      for (let b = 0; b <= unions.length; b++) {
        if (b === unions.length) {
          unions.push(bits[i].clone()); sizes.push(1); blockOf[i] = b;
          if (closedAfterAdd(b)) rec(i + 1);
          unions.pop(); sizes.pop(); blockOf[i] = -1;
        } else {
          if (bits[i].intersects(unions[b])) continue;
          const old = unions[b];
          unions[b] = old.or(bits[i]); sizes[b]++; blockOf[i] = b;
          if (closedAfterAdd(b)) rec(i + 1);
          unions[b] = old; sizes[b]--; blockOf[i] = -1;
        }
      }
    };
    rec(0);
    return best;
  },
});

// ----- Semantic / LP-based measures ----------------------------------------

defineMeasure({
  id: 'eta', label: 'η (Eta)', symbol: 'I_η', family: 'Semantic',
  java: 'EtaInconsistencyMeasure',
  description: '1 − η where η is the largest value such that some probability distribution over interpretations assigns probability ≥ η to every formula (linear program).',
  reference: 'Knight. Measuring inconsistency. Journal of Philosophical Logic 2002',
  compute(ctx) {
    const n = ctx.kb.size;
    // Only maximal consistent subsets matter: moving probability mass from a
    // world to one satisfying a superset of formulas never decreases the
    // objective, so the LP over all 2^|At| worlds has the same optimum.
    const msses = ctx.an.msses();
    const nv = msses.length + 1;  // p_j ..., eta
    const eta = msses.length;
    const cons = [];
    const sum = new Float64Array(nv);
    for (let j = 0; j < msses.length; j++) sum[j] = 1;
    cons.push({ a: sum, op: '=', b: 1 });
    const contains = msses.map(m => { const s = new Uint8Array(n); for (const i of m) s[i] = 1; return s; });
    for (let i = 0; i < n; i++) {
      const a = new Float64Array(nv);
      for (let j = 0; j < msses.length; j++) if (contains[j][i]) a[j] = 1;
      a[eta] = -1;
      cons.push({ a, op: '>=', b: 0 });
    }
    const ub = new Float64Array(nv); ub[eta] = 1;
    cons.push({ a: ub, op: '<=', b: 1 });
    const c = new Float64Array(nv); c[eta] = 1;
    const res = lpMaximize(nv, c, cons);
    if (res.status !== 'optimal') return 1;
    const v = 1 - res.x[eta];
    return Math.abs(v) < 1e-12 ? 0 : v;
  },
});

// Dual-rail encoding of Priest's three-valued logic LP: every formula gets a
// pair of literals (P, N) meaning "f is at least true" (T or B) and "¬f is at
// least true" (F or B). An atom p is B iff P(p) ∧ N(p).
function railEncoder(solver) {
  const enc = new Encoder(solver);
  const atomRail = new Map();
  const cache = new Map();
  const rail = (f) => {
    switch (f.t) {
      case 'prop': {
        let r = atomRail.get(f.name);
        if (!r) { r = [solver.newVar(), solver.newVar()]; solver.addClause([r[0], r[1]]); atomRail.set(f.name, r); }
        return r;
      }
      case 'top': { const t = enc.trueLit(); return [t, -t]; }
      case 'bot': { const t = enc.trueLit(); return [-t, t]; }
      case 'not': { const r = rail(f.k[0]); return [r[1], r[0]]; }
    }
    const k = key(f);
    if (cache.has(k)) return cache.get(k);
    let r;
    const xorRail = (x, y) => [
      enc.andGate([enc.orGate([x[0], y[0]]), enc.orGate([x[1], y[1]])]),
      enc.orGate([enc.andGate([x[1], y[1]]), enc.andGate([x[0], y[0]])]),
    ];
    switch (f.t) {
      case 'and': { const rs = f.k.map(rail); r = [enc.andGate(rs.map(x => x[0])), enc.orGate(rs.map(x => x[1]))]; break; }
      case 'or': { const rs = f.k.map(rail); r = [enc.orGate(rs.map(x => x[0])), enc.andGate(rs.map(x => x[1]))]; break; }
      case 'impl': { const a = rail(f.k[0]), b = rail(f.k[1]); r = [enc.orGate([a[1], b[0]]), enc.andGate([a[0], b[1]])]; break; }
      case 'equiv': {
        const a = rail(f.k[0]), b = rail(f.k[1]);
        r = [enc.andGate([enc.orGate([a[1], b[0]]), enc.orGate([b[1], a[0]])]),
             enc.orGate([enc.andGate([a[0], b[1]]), enc.andGate([b[0], a[1]])])];
        break;
      }
      case 'xor': {
        if (f.k.length === 0) { const t = enc.trueLit(); r = [-t, t]; break; }
        r = rail(f.k[0]);
        for (let i = 1; i < f.k.length; i++) r = xorRail(r, rail(f.k[i]));
        break;
      }
      default: throw new Error('Unknown formula type ' + f.t);
    }
    cache.set(k, r);
    return r;
  };
  return { rail, atomRail, enc };
}

defineMeasure({
  id: 'contension', label: 'Contension', symbol: 'I_c', family: 'Semantic',
  java: 'ContensionInconsistencyMeasure',
  description: 'Minimal number of atoms that have to be assigned the paradoxical truth value B in a model of Priest\'s three-valued logic LP (∞ if no model exists).',
  reference: 'Grant, Hunter. Measuring consistency gain and information loss in stepwise inconsistency resolution. ECSQARU 2011',
  compute(ctx) {
    const s = new SatSolver();
    const { rail, atomRail } = railEncoder(s);
    for (const f of ctx.kb.formulas) s.addClause([rail(f)[0]]);
    const bs = [];
    for (const [, r] of atomRail) { const b = s.newVar(); s.addClause([-r[0], -r[1], b]); bs.push(b); }
    return minimizeTrueCount(s, bs);
  },
});

defineMeasure({
  id: 'hs', label: 'Hitting set', symbol: 'I_hs', family: 'Semantic',
  java: 'HsInconsistencyMeasure',
  description: 'Minimal number of interpretations needed such that every formula is satisfied by one of them, minus 1 (∞ if a formula is unsatisfiable).',
  reference: 'Thimm. On the expressivity of inconsistency measures. AIJ 2016',
  compute(ctx) {
    const kb = ctx.kb, n = kb.size;
    if (n === 0) return 0;
    if (ctx.an.selfContradictory().length > 0) return Infinity;
    if (ctx.an.isConsistent()) return 0;
    for (let k = 2; k <= n; k++) {
      checkDeadlineNow();
      const s = new SatSolver();
      const outs = kb.formulas.map(() => []);
      for (let c = 0; c < k; c++) {
        const enc = new Encoder(s);
        kb.formulas.forEach((f, i) => outs[i].push(enc.lit(f)));
      }
      for (const o of outs) s.addClause(o);
      if (s.solve()) return k - 1;
    }
    return Infinity;
  },
});

// ----- Distance-based measures (Dalal distance) ----------------------------

const DALAL_ENUM_MAX_ATOMS = 22;
const DALAL_LOCAL_MAX_ATOMS = 20;
const INF16 = 32767;

// distance table of a formula over its own atoms (multi-source BFS on the
// hypercube from all models); INF16 if the formula has no model
function dalalTable(f) {
  const { atoms: at, tt } = localTruthTable(f);
  const m = at.length, N = 1 << m;
  const dist = new Int16Array(N).fill(INF16);
  const queue = new Int32Array(N);
  let qh = 0, qt = 0;
  for (let w = 0; w < N; w++) if (ttGet(tt, w)) { dist[w] = 0; queue[qt++] = w; }
  while (qh < qt) {
    const w = queue[qh++];
    const d = dist[w] + 1;
    for (let j = 0; j < m; j++) {
      const u = w ^ (1 << j);
      if (dist[u] > d) { dist[u] = d; queue[qt++] = u; }
    }
  }
  return { atoms: at, dist };
}

function dalalByEnumeration(kb, mode) {
  const n = kb.size;
  if (n === 0) return 0;
  const nA = kb.atoms.length;
  const tables = kb.formulas.map(dalalTable);
  // for each global atom: list of [formula, local bit]
  const occ = kb.atoms.map(() => []);
  tables.forEach((t, fi) => t.atoms.forEach((a, j) => occ[kb.atomIndex.get(a)].push(fi, 1 << j)));
  const local = new Int32Array(n);
  const total = 1 << nA;
  let best = Infinity;
  for (let step = 0; step < total; step++) {
    if (step > 0) {
      // Gray code: flip bit = index of lowest set bit of step
      const j = 31 - Math.clz32(step & -step);
      const o = occ[j];
      for (let t = 0; t < o.length; t += 2) local[o[t]] ^= o[t + 1];
      if ((step & 0xFFFF) === 0) checkDeadlineNow();
    }
    let v = 0;
    if (mode === 'sum') {
      for (let i = 0; i < n; i++) { const d = tables[i].dist[local[i]]; if (d === INF16) { v = Infinity; break; } v += d; }
    } else if (mode === 'max') {
      for (let i = 0; i < n; i++) { const d = tables[i].dist[local[i]]; if (d === INF16) { v = Infinity; break; } if (d > v) v = d; }
    } else {
      for (let i = 0; i < n; i++) if (tables[i].dist[local[i]] > 0) v++;
    }
    if (v < best) { best = v; if (best === 0) break; }
  }
  return best;
}

// SAT-based fallback for large signatures: one copy of the atoms per formula
// and difference indicators to a common world.
function dalalBySat(ctx, mode) {
  const kb = ctx.kb, n = kb.size;
  if (n === 0) return 0;
  if (mode === 'hit') {
    // own solver: the minimisation adds clauses that must not leak into the
    // shared analysis solver
    const s = new SatSolver();
    const enc = new Encoder(s);
    const sels = kb.formulas.map(f => { const sv = s.newVar(); s.addClause([-sv, enc.lit(f)]); return sv; });
    return minimizeTrueCount(s, sels.map(v => -v));
  }
  const s = new SatSolver();
  const world = new Map();
  for (const a of kb.atoms) world.set(a, s.newVar());
  const diffs = [];
  kb.formulas.forEach((f) => {
    const copy = new Map();
    const enc = new Encoder(s, (name) => { let v = copy.get(name); if (!v) { v = s.newVar(); copy.set(name, v); } return v; });
    s.addClause([enc.lit(f)]);
    const ds = [];
    for (const [name, x] of copy) {
      const w = world.get(name), d = s.newVar();
      s.addClause([-x, w, d]); s.addClause([x, -w, d]);
      ds.push(d);
    }
    diffs.push(ds);
  });
  if (mode === 'sum') return minimizeTrueCount(s, [].concat(...diffs));
  // max: minimise the largest per-formula count
  if (!s.solve()) return Infinity;
  const outs = diffs.map(ds => totalizer(s, ds));
  let best = Math.max(0, ...diffs.map(ds => countTrue(s, ds)));
  while (best > 0) {
    for (const o of outs) if (o.length >= best) s.addClause([-o[best - 1]]);
    if (!s.solve()) break;
    best = Math.max(0, ...diffs.map(ds => countTrue(s, ds)));
  }
  return best;
}

function dalalMeasure(ctx, mode) {
  const kb = ctx.kb;
  const useEnum = kb.atoms.length <= DALAL_ENUM_MAX_ATOMS && kb.formulas.every(f => atoms(f).length <= DALAL_LOCAL_MAX_ATOMS);
  return useEnum ? dalalByEnumeration(kb, mode) : dalalBySat(ctx, mode);
}

defineMeasure({
  id: 'dalalsum', label: 'Dalal-Sum', symbol: 'I_dalal^Σ', family: 'Distance-based',
  java: 'DSumInconsistencyMeasure (DalalDistance)',
  description: 'Minimal sum of Dalal (Hamming) distances from one interpretation to the models of each formula.',
  reference: 'Grant, Hunter. Distance-based measures of inconsistency. ECSQARU 2013',
  compute(ctx) { return dalalMeasure(ctx, 'sum'); },
});
defineMeasure({
  id: 'dalalmax', label: 'Dalal-Max', symbol: 'I_dalal^max', family: 'Distance-based',
  java: 'DMaxInconsistencyMeasure (DalalDistance)',
  description: 'Minimal maximum Dalal distance from one interpretation to the models of each formula.',
  reference: 'Grant, Hunter. Distance-based measures of inconsistency. ECSQARU 2013',
  compute(ctx) { return dalalMeasure(ctx, 'max'); },
});
defineMeasure({
  id: 'dalalhit', label: 'Dalal-Hit', symbol: 'I_dalal^hit', family: 'Distance-based',
  java: 'DHitInconsistencyMeasure (DalalDistance)',
  description: 'Minimal number of formulas not satisfied by an interpretation.',
  reference: 'Grant, Hunter. Distance-based measures of inconsistency. ECSQARU 2013',
  compute(ctx) { return dalalMeasure(ctx, 'hit'); },
});

// ----- Proof-based / syntactic measures ------------------------------------

defineMeasure({
  id: 'pm', label: 'Minimal proofs (Pm)', symbol: 'I_pm', family: 'Proof-based',
  java: 'PmInconsistencyMeasure',
  description: 'Sum over all atoms x of (#minimal proofs of x)·(#minimal proofs of ¬x).',
  reference: 'Jabbour, Raddaoui. Measuring inconsistency through minimal proofs. ECSQARU 2013',
  compute(ctx) {
    const kb = ctx.kb;
    const numProofs = (f) => {
      const negF = complement(f);
      const kNeg = key(negF);
      const ext = kb.formulas.slice();
      let negIdx = ext.findIndex(g => key(g) === kNeg);
      if (negIdx < 0) { ext.push(negF); negIdx = ext.length - 1; }
      const muses = minimalInconsistentSubsets(ext);
      const kF = key(f);
      let r = 0;
      for (const m of muses) {
        if (m.includes(negIdx)) r++;
        else if (m.length === 1) {
          const lits = literals(ext[m[0]]);
          if (lits.has(kF) || lits.has(kNeg)) r++;
        }
      }
      return r;
    };
    let result = 0;
    for (const a of kb.atoms) {
      checkDeadlineNow();
      const x = Prop(a);
      result += numProofs(x) * numProofs(Not(x));
    }
    return result;
  },
});

defineMeasure({
  id: 'fb', label: 'Forgetting-based', symbol: 'I_fb', family: 'Syntactic',
  java: 'FbInconsistencyMeasure',
  description: 'Minimal number of atom occurrences that have to be forgotten (replaced by ⊤ or ⊥) to make the knowledge base consistent.',
  reference: 'Besnard. Forgetting-based inconsistency measure. SUM 2016',
  compute(ctx) {
    const kb = ctx.kb;
    const s = new SatSolver();
    const atomVar = new Map();
    const av = (name) => { let v = atomVar.get(name); if (!v) { v = s.newVar(); atomVar.set(name, v); } return v; };
    const sels = [];
    // every occurrence becomes its own variable z, tied to its atom unless forgotten
    const occVar = new Map();
    let counter = 0;
    const rename = (f) => {
      if (f.t === 'prop') {
        const name = '\u0000' + (counter++);
        const z = s.newVar(), sel = s.newVar(), p = av(f.name);
        s.addClause([sel, -z, p]); s.addClause([sel, z, -p]);
        sels.push(sel);
        occVar.set(name, z);
        return Prop(name);
      }
      if (!f.k) return f;
      return { t: f.t, k: f.k.map(rename) };
    };
    const enc = new Encoder(s, (name) => occVar.get(name));
    for (const f of kb.formulas) s.addClause([enc.lit(rename(f))]);
    return minimizeTrueCount(s, sels);
  },
});

// ----- Fuzzy measures -------------------------------------------------------

// TweetyProject's syntactic toCnf()/trim()/collapseAssociativeFormulas(),
// needed because FuzzyInconsistencyMeasure evaluates an exclusive or through
// the (de-duplicated) result of ExclusiveDisjunction.toCnf(). Where Java builds
// associative formulas from hash sets, set semantics are used (unordered key).
function ukey(f) {
  switch (f.t) {
    case 'and': case 'or': case 'xor': return f.t + '(' + f.k.map(ukey).sort().join('|') + ')';
    case 'not': return '!(' + ukey(f.k[0]) + ')';
    case 'impl': case 'equiv': return f.t + '(' + ukey(f.k[0]) + '|' + ukey(f.k[1]) + ')';
    default: return key(f);
  }
}
function twSet(list) { const m = new Map(); for (const g of list) m.set(ukey(g), g); return Array.from(m.values()); }
function twTrim(f) {
  switch (f.t) {
    case 'not': { const g = twTrim(f.k[0]); return g.t === 'not' ? g.k[0] : Not(g); }
    case 'and': case 'or': case 'xor': return { t: f.t, k: twSet(f.k.map(twTrim)) };
    case 'impl': case 'equiv': { const a = twTrim(f.k[0]), b = twTrim(f.k[1]); return ukey(a) === ukey(b) ? TOP : { t: f.t, k: [a, b] }; }
    default: return f;
  }
}
function twCollapse(f) {
  switch (f.t) {
    case 'and': case 'or': case 'xor': {
      if (f.k.length === 0) return f.t === 'and' ? TOP : BOT;
      if (f.k.length === 1) return twCollapse(f.k[0]);
      const out = [];
      for (const g of f.k) { const h = twCollapse(g); if (h.t === f.t) out.push(...h.k); else out.push(h); }
      return { t: f.t, k: out };
    }
    case 'not': return Not(twCollapse(f.k[0]));
    case 'impl': case 'equiv': return { t: f.t, k: [twCollapse(f.k[0]), twCollapse(f.k[1])] };
    default: return f;
  }
}
function twCnf(f) {
  checkDeadline();
  switch (f.t) {
    case 'prop': case 'top': case 'bot': return And([Or([f])]);
    case 'not': {
      const g = f.k[0];
      const comp = (h) => h.t === 'not' ? h.k[0] : Not(h);
      if (g.t === 'not') return twCnf(g.k[0]);
      if (g.t === 'and') return twCnf(Or(g.k.map(comp)));
      if (g.t === 'or') return twCnf(And(g.k.map(comp)));
      if (g.t === 'bot') return And([Or([TOP])]);
      if (g.t === 'top') return And([Or([BOT])]);
      if (g.t === 'impl' || g.t === 'equiv' || g.t === 'xor') return twCnf(Not(twCnf(g)));
      return And([Or([f])]);
    }
    case 'and': {
      const cnf = [];
      for (const c of f.k) for (const cl of twCnf(c).k) cnf.push(cl);
      return twTrim(And(twSet(cnf)));
    }
    case 'or': {
      if (f.k.every(isLiteral)) return And([f]);
      const conjs = new Map();
      for (const g of f.k) { const cls = twSet(twCnf(g).k); conjs.set(cls.map(ukey).sort().join('#'), cls); }
      // distribute: one clause from each operand's CNF; Java builds all combinations and
      // trims the result to a set of clauses (sets of literals), so partial disjunctions
      // with the same literals can be merged on the way
      let partial = new Map([['', []]]);
      for (const cls of conjs.values()) {
        const next = new Map();
        for (const lits of partial.values()) {
          for (const cl of cls) {
            const merged = twSet(lits.concat(cl.t === 'or' ? cl.k : [cl]));
            const k = merged.map(ukey).sort().join('|');
            if (!next.has(k)) next.set(k, merged);
          }
        }
        partial = next;
        if (partial.size > 200000) throw new LimitError('CNF too large');
        checkDeadline();
      }
      return twTrim(And(twSet(Array.from(partial.values()).map(l => Or(l)))));
    }
    case 'impl': return twCnf(Or([Not(f.k[0]), f.k[1]]));
    case 'equiv': return twCnf(And([Or([Not(f.k[0]), f.k[1]]), Or([Not(f.k[1]), f.k[0]])]));
    case 'xor': {
      if (f.k.length === 0) return And([]);
      let tl = twCollapse(twCnf(f.k[0]));
      for (let i = 1; i < f.k.length; i++) {
        const tr = twCollapse(twCnf(f.k[i]));
        tl = And([Or([Not(tl), Not(tr)]), Or([tl, tr])]);
      }
      // as the corrected ExclusiveDisjunction.toCnf(), which normalises the negated
      // and disjoined operand CNFs (before, e.g. (a&&b)^^c gave the clause !(a&&b)||!c)
      return twCnf(tl);
    }
  }
  throw new Error('Unknown formula type ' + f.t);
}

function compileFuzzy(f, idx, tnorm) {
  const T = tnorm === 'min' ? (a, b) => Math.min(a, b) : (a, b) => a * b;
  const S = tnorm === 'min' ? (a, b) => Math.max(a, b) : (a, b) => a + b - a * b;
  const rec = (g) => {
    switch (g.t) {
      case 'prop': { const j = idx.get(g.name); return (x) => x[j]; }
      case 'top': return () => 1;
      case 'bot': return () => 0;
      case 'not': { const h = rec(g.k[0]); return (x) => 1 - h(x); }
      case 'and': { const hs = g.k.map(rec); return (x) => { let v = 1; for (const h of hs) v = T(v, h(x)); return v; }; }
      case 'or': { const hs = g.k.map(rec); return (x) => { let v = 0; for (const h of hs) v = S(v, h(x)); return v; }; }
      case 'impl': { const a = rec(g.k[0]), b = rec(g.k[1]); return (x) => S(1 - a(x), b(x)); }
      case 'equiv': { const a = rec(g.k[0]), b = rec(g.k[1]); return (x) => { const va = a(x), vb = b(x); return T(S(1 - va, vb), S(1 - vb, va)); }; }
      case 'xor': {
        // as in TweetyProject: T-norm over the clauses of the formula's toCnf()
        const hs = twCnf(g).k.map(rec);
        return (x) => { let v = 1; for (const h of hs) v = T(v, h(x)); return v; };
      }
    }
    throw new Error('Unknown formula type ' + g.t);
  };
  return rec(f);
}

function fuzzyMeasure(kb, tnorm, variant, rngSeed) {
  if (kb.size === 0) return 0;
  const n = kb.atoms.length;
  const terms = kb.formulas.map(f => compileFuzzy(f, kb.atomIndex, tnorm));
  const T = tnorm === 'min' ? (a, b) => Math.min(a, b) : (a, b) => a * b;
  const obj = variant === 'sum'
    ? (x) => { let v = 0; for (const t of terms) v += 1 - t(x); return v; }
    : (x) => { let v = 1; for (const t of terms) v = T(v, t(x)); return 1 - v; };
  // Three-valued grid {0, 1/2, 1}^n: exact for the minimum t-norm (all vertices
  // of the piecewise-linear objective lie on it), good starts for products.
  const starts = [];
  const scored = [];
  const x = new Float64Array(n);
  const GRID_MAX = tnorm === 'min' ? 12 : 9;
  if (n <= GRID_MAX) {
    const total = Math.pow(3, n);
    for (let c = 0; c < total; c++) {
      if ((c & 4095) === 0) checkDeadlineNow();
      let r = c;
      for (let i = 0; i < n; i++) { x[i] = (r % 3) / 2; r = (r / 3) | 0; }
      scored.push([obj(x), c]);
    }
    scored.sort((a, b) => a[0] - b[0]);
    if (tnorm === 'min') return Math.max(0, scored[0][0]);
    for (const [, c] of scored.slice(0, 6)) {
      const s = new Float64Array(n);
      let r = c;
      for (let i = 0; i < n; i++) { s[i] = (r % 3) / 2; r = (r / 3) | 0; }
      starts.push(s);
    }
  } else {
    const rng = makeRng(rngSeed || 7);
    for (let k = 0; k < 64; k++) { const s = new Float64Array(n); for (let i = 0; i < n; i++) s[i] = rng.int(0, 2) / 2; starts.push(s); }
    starts.sort((a, b) => obj(a) - obj(b));
    starts.length = 8;
  }
  const res = minimizeBox(obj, n, { starts, randomStarts: 8, rng: makeRng(rngSeed || 11) });
  const v = res.value;
  return Math.abs(v) < 1e-12 ? 0 : v;
}

defineMeasure({
  id: 'fuzzy', label: 'Fuzzy', symbol: 'I_fuzzy', family: 'Fuzzy',
  java: 'FuzzyInconsistencyMeasure',
  description: 'Minimal degree of violation over all fuzzy interpretations, w.r.t. a t-norm (non-nilpotent: minimum or product) and its dual t-conorm. T-variant: 1 − T(K); sum variant: Σ(1 − v(φ)).',
  reference: 'Thimm. Measuring inconsistency in probabilistic knowledge bases / fuzzy measures (TweetyProject); cf. Grant, Hunter (fuzzy logic based measures)',
  params: [
    { id: 'tnorm', label: 't-norm', options: [['product', 'Product'], ['min', 'Minimum']], default: 'product' },
    { id: 'variant', label: 'Variant', options: [['t', 'T-fuzzy (1 − T(K))'], ['sum', 'Sum-fuzzy (Σ 1 − v(φ))']], default: 't' },
  ],
  approximate: true,
  compute(ctx, p) {
    // a classical model gives every formula the value 1, so consistent bases have value 0
    if (ctx.an.isConsistent()) return 0;
    return fuzzyMeasure(ctx.kb, p.tnorm || 'product', p.variant || 't');
  },
});

// ----- Iceberg measures (De Bona, Hunter. AIJ 2017) -------------------------

function flattenConj(f) {
  if (f.t !== 'and') return [f];
  const out = [];
  for (const g of f.k) {
    const h = collapse(g);
    if (h.t === 'and') out.push(...flattenConj(h)); else out.push(h);
  }
  return out;
}
function collapse(f) {
  if (isAssoc(f)) {
    if (f.k.length === 0) return f.t === 'and' ? TOP : BOT;
    if (f.k.length === 1) return collapse(f.k[0]);
    const out = [];
    for (const g of f.k) { const h = collapse(g); if (h.t === f.t) out.push(...h.k); else out.push(h); }
    return { t: f.t, k: out };
  }
  if (f.t === 'not') return Not(collapse(f.k[0]));
  if (f.t === 'impl' || f.t === 'equiv') return { t: f.t, k: [collapse(f.k[0]), collapse(f.k[1])] };
  return f;
}

// conjuncts of a formula: the formula itself and all (order preserving)
// sub-conjunctions of its flattened top-level conjunction
function conjunctKeys(f, smallestOnly, javaCompat) {
  const res = new Set();
  if (javaCompat) {
    // exactly TweetyProject's sets (used for validation only): CONJUNCTS takes
    // the suffixes of a conjunction, SMALLEST_CONJUNCTS its elements; literals
    // contribute themselves, all other formulas nothing
    const c = collapse(f);
    if (f.t === 'and' && c.t === 'and') {
      if (smallestOnly) for (const g of c.k) res.add(key(g));
      else for (let i = 0; i < c.k.length; i++) { const suf = c.k.slice(i); res.add(key(suf.length === 1 ? collapse(suf[0]) : And(suf))); }
    }
    if (isLiteral(f)) res.add(key(f));
    return res;
  }
  const c = collapse(f);
  if (c.t !== 'and') { res.add(key(f)); res.add(key(c)); return res; }
  const parts = c.k;
  if (smallestOnly) { for (const g of parts) res.add(key(g)); return res; }
  res.add(key(f));
  const m = parts.length;
  if (m > 12) { for (const g of parts) res.add(key(g)); res.add(key(c)); return res; }
  for (let mask = 1; mask < (1 << m); mask++) {
    const sel = [];
    for (let j = 0; j < m; j++) if (mask & (1 << j)) sel.push(parts[j]);
    res.add(key(sel.length === 1 ? sel[0] : And(sel)));
  }
  return res;
}

function icebergMeasure(ctx, op, sumVariant, javaCompat) {
  const kb = ctx.kb, n = kb.size;
  if (n > 16) throw new LimitError('The iceberg measure enumerates all subsets; at most 16 formulas are supported.');
  const F = kb.formulas;
  const muses = ctx.an.muses();
  const musMasks = muses.map(m => m.reduce((a, i) => a | (1 << i), 0));
  const inconsistent = (mask) => musMasks.some(mm => (mm & mask) === mm);
  const conjSets = F.map(f => conjunctKeys(f, false, javaCompat));
  const smallSets = F.map(f => conjunctKeys(f, true, javaCompat));
  const keys = F.map(key);
  const piCache = new Map();
  const pis = (i) => { if (!piCache.has(i)) piCache.set(i, new Set(primeImplicants(F[i]).map(t => t.join('&')))); return piCache.get(i); };
  const entailCache = new Map();
  const entailsIdx = (mask, i) => {   // F[mask] |= F[i]
    const ck = mask * 64 + i;
    if (entailCache.has(ck)) return entailCache.get(ck);
    const prem = [];
    for (let j = 0; j < n; j++) if (mask & (1 << j)) prem.push(F[j]);
    const r = entails(prem, F[i]);
    entailCache.set(ck, r);
    return r;
  };
  const singleEntailCache = new Map();
  const entailsSingle = (j, i) => {
    const ck = j * 64 + i;
    if (!singleEntailCache.has(ck)) singleEntailCache.set(ck, entails([F[j]], F[i]));
    return singleEntailCache.get(ck);
  };
  // is formula i in Cn*(F[mask])?
  const inCnCache = new Map();
  const inCn = (i, mask) => {
    const ck = mask * 64 + i;
    if (inCnCache.has(ck)) return inCnCache.get(ck);
    let r = false;
    switch (op) {
      case 'identity': r = (mask & (1 << i)) !== 0; break;
      case 'conjuncts': case 'smallest_conjuncts': {
        const sets = op === 'conjuncts' ? conjSets : smallSets;
        for (let j = 0; j < n && !r; j++) if ((mask & (1 << j)) && sets[j].has(keys[i])) r = true;
        break;
      }
      case 'classical': r = entailsIdx(mask, i); break;
      case 'opposite_literals': r = isLiteral(F[i]) && entailsIdx(mask, i); break;
      case 'prime_implicants': {
        const pi = pis(i);
        for (let j = 0; j < n && !r; j++) {
          if (!(mask & (1 << j))) continue;
          if (!entailsSingle(j, i)) continue;
          const pj = pis(j);
          let all = true;
          for (const t of pi) if (!pj.has(t)) { all = false; break; }
          if (all) r = true;
        }
        break;
      }
      case 'modus_ponens': {
        const base = new Map();
        for (let j = 0; j < n; j++) if (mask & (1 << j)) {
          for (const g of [F[j], ...flattenConj(collapse(F[j]))]) base.set(key(g), g);
          for (const kk of conjSets[j]) if (!base.has(kk)) base.set(kk, null);
        }
        let changed = true;
        while (changed) {
          changed = false;
          for (const g of Array.from(base.values())) {
            if (g && g.t === 'impl' && base.has(key(g.k[0])) && !base.has(key(g.k[1]))) {
              const c = g.k[1];
              base.set(key(c), c);
              for (const h of flattenConj(collapse(c))) if (!base.has(key(h))) base.set(key(h), h);
              changed = true;
            }
          }
        }
        r = base.has(keys[i]);
        break;
      }
      default: throw new Error('Unknown consequence operation ' + op);
    }
    inCnCache.set(ck, r);
    return r;
  };
  // minimal subsets E of `mask` with formula i in Cn*(E)
  const minEntailing = (i, mask) => {
    const members = [];
    for (let j = 0; j < n; j++) if (mask & (1 << j)) members.push(j);
    const res = [];
    const m = members.length;
    const subs = [];
    for (let s = 0; s < (1 << m); s++) subs.push(s);
    subs.sort((a, b) => popcount32(a) - popcount32(b));
    for (const s of subs) {
      let e = 0;
      for (let j = 0; j < m; j++) if (s & (1 << j)) e |= 1 << members[j];
      if (res.some(r => (r & e) === r)) continue;
      if (inCn(i, e)) res.push(e);
    }
    return res;
  };
  const hasStarMapping = (mus, mask) => {
    const options = mus.map(i => minEntailing(i, mask));
    if (options.some(o => o.length === 0)) return false;
    const rest = new Array(options.length + 1).fill(0);
    for (let t = options.length - 1; t >= 0; t--) rest[t] = rest[t + 1] | options[t].reduce((a, b) => a | b, 0);
    const rec = (t, acc) => {
      if (t === options.length) return acc === mask;
      if (((acc | rest[t]) & mask) !== mask) return false;
      for (const o of options[t]) if (rec(t + 1, acc | o)) return true;
      return false;
    };
    return rec(0, 0);
  };
  let result = 0;
  const conflicts = [];
  for (let mask = 1; mask < (1 << n); mask++) {
    checkDeadline();
    if (!inconsistent(mask)) continue;
    let found = false;
    for (const mus of muses) {
      if (mus.every(i => inCn(i, mask)) && hasStarMapping(mus, mask)) { found = true; break; }
    }
    if (found) {
      const size = popcount32(mask);
      conflicts.push(mask);
      result += sumVariant ? 1 / size : 1;
    }
  }
  return result;
}

defineMeasure({
  id: 'iceberg', label: 'Iceberg', symbol: 'I_ice', family: 'Syntactic',
  java: 'IcebergInconsistencyMeasure',
  description: 'Number of *-conflicts: inconsistent subsets C whose consequences Cn*(C) contain a minimal inconsistent subset M such that every formula of C is needed to derive some formula of M (sum variant: Σ 1/|C|).',
  reference: 'De Bona, Hunter. Localising iceberg inconsistencies. AIJ 2017',
  params: [
    { id: 'op', label: 'Consequence operation', options: [['identity', 'Identity'], ['conjuncts', 'Conjuncts'], ['smallest_conjuncts', 'Smallest conjuncts'], ['classical', 'Modular classical consequence'], ['modus_ponens', 'Modus ponens'], ['prime_implicants', 'Prime implicants'], ['opposite_literals', 'Opposite literals']], default: 'classical' },
    { id: 'sum', label: 'Variant', options: [['false', 'Count'], ['true', 'Sum of 1/|C|']], default: 'false' },
  ],
  compute(ctx, p) { return icebergMeasure(ctx, p.op || 'classical', p.sum === 'true' || p.sum === true, p.javaCompat === true); },
});

// ----- Prime implicant based measure ---------------------------------------

function pibItems(f) {
  const { atoms: at, tt } = localTruthTable(f);
  const m = at.length;
  if (m > 16) throw new LimitError('Formula with too many atoms for the prime implicant based measure.');
  const idx = new Map(at.map((a, i) => [a, i]));
  const lits = Array.from(literals(f).values());
  const sets = new Map();
  for (let w = 0; w < (1 << m); w++) {
    if (!ttGet(tt, w)) continue;
    const nm = [];
    for (const l of lits) {
      let nw;
      if (l.t === 'prop') { const b = 1 << idx.get(l.name); nw = (w & b) ? (w & ~b) : w; }
      else { const b = 1 << idx.get(l.k[0].name); nw = w | b; }
      if (!ttGet(tt, nw)) nm.push(key(l));
    }
    nm.sort();
    sets.set(nm.join(','), nm);
  }
  const all = Array.from(sets.values());
  const items = new Map();   // itemKey -> {kind, lits}
  const nonCommon = new Set();
  for (const p of all) for (const l of p) {
    if (all.every(p1 => p1.includes(l))) items.set('L:' + l, { kind: 'lit', lits: [l] });
    else nonCommon.add(l);
  }
  if (nonCommon.size > 0) {
    const ls = Array.from(nonCommon).sort();
    items.set('C:' + ls.join(','), { kind: 'clause', lits: ls });
  }
  return Array.from(items.entries());
}
function negLitKey(k) { return k.startsWith('!(') ? k.slice(2, -1) : '!(' + k + ')'; }

defineMeasure({
  id: 'pib', label: 'Prime implicant based', symbol: 'I_pi', family: 'Syntactic',
  java: 'PrimeImplicantBasedInconsistencyMeasure',
  description: 'Half the number of conflicting (complementary) prime-implicant items of the formulas, divided by the total number of atom occurrences per formula (TweetyProject\'s SimplePrimeImplicantEnumerator heuristic).',
  reference: 'Jabbour, Ma, Raddaoui, Sais. Quantifying conflicts in propositional logic through prime implicates. IJAR 2017',
  compute(ctx) {
    const kb = ctx.kb;
    const allItems = new Map();
    for (const f of kb.formulas) for (const [k, it] of pibItems(f)) allItems.set(k, it);
    const units = new Map();   // literal key -> item keys that are unit
    for (const [k, it] of allItems) if (it.lits.length === 1) {
      const l = it.lits[0];
      if (!units.has(l)) units.set(l, []);
      units.get(l).push(k);
    }
    const conflicts = new Set();
    for (const [l, ks] of units) {
      const other = units.get(negLitKey(l));
      if (other) { for (const k of ks) conflicts.add(k); for (const k of other) conflicts.add(k); }
    }
    let litCount = 0;
    for (const f of kb.formulas) litCount += atoms(f).length;
    return (conflicts.size / 2) / litCount;
  },
});

// ----- Evaluation -----------------------------------------------------------

function makeContext(kb) { return { kb, an: new KBAnalysis(kb) }; }

function defaultParams(m) {
  const p = {};
  for (const par of (m.params || [])) p[par.id] = par.default;
  return p;
}

function computeMeasure(id, ctxOrKb, params) {
  const m = MEASURE_BY_ID.get(id);
  if (!m) throw new Error('Unknown measure ' + id);
  const ctx = ctxOrKb instanceof KnowledgeBase ? makeContext(ctxOrKb) : ctxOrKb;
  return m.compute(ctx, Object.assign(defaultParams(m), params || {}));
}

IM.MEASURES = MEASURES;
IM.MEASURE_BY_ID = MEASURE_BY_ID;
IM.makeContext = makeContext;
IM.computeMeasure = computeMeasure;
IM.defaultParams = defaultParams;
IM.dalalByEnumeration = dalalByEnumeration;
IM.dalalBySat = dalalBySat;
IM.fuzzyMeasure = fuzzyMeasure;
IM.icebergMeasure = icebergMeasure;

// ===== 08-tools.js =====
// ---------------------------------------------------------------------------
// Analysis tools: sub-base analyses, Shapley inconsistency values (port of
// ShapleyCulpabilityMeasure), removal impact, rationality postulates (port of
// org.tweetyproject.logics.pl.postulates), random knowledge base sampling,
// incremental analysis, rank correlation of measures, possible worlds.
// ---------------------------------------------------------------------------

// Analysis of a sub-base of an analysed knowledge base without new SAT calls:
// MI(S) = {M in MI(K) : M ⊆ S}; MSS(S) = maximal elements of {T ∩ S : T in MSS(K)}.
function deriveAnalysis(parent, indices) {
  const sub = parent.kb.subset(indices);
  const an = new KBAnalysis(sub);
  const pe = parent.enumerate();
  const pos = new Map(indices.map((i, j) => [i, j]));
  const muses = [];
  for (const m of pe.muses) if (m.every(i => pos.has(i))) muses.push(m.map(i => pos.get(i)).sort((a, b) => a - b));
  const cand = new Map();
  for (const t of pe.msses) {
    const r = [];
    for (const i of t) if (pos.has(i)) r.push(pos.get(i));
    r.sort((a, b) => a - b);
    cand.set(r.join(','), r);
  }
  const list = Array.from(cand.values()).sort((a, b) => b.length - a.length);
  const msses = [];
  for (const c of list) {
    const cs = new Set(c);
    if (msses.some(m => m.length > c.length && c.every(x => m.includes(x)))) continue;
    if (msses.some(m => m.length === c.length && m.every(x => cs.has(x)))) continue;
    msses.push(c);
  }
  msses.sort(cmpIndexArrays);
  muses.sort(cmpIndexArrays);
  const n = indices.length;
  const mcses = msses.map(m => { const s = new Set(m); const r = []; for (let i = 0; i < n; i++) if (!s.has(i)) r.push(i); return r; }).sort(cmpIndexArrays);
  an._enum = { muses, msses, mcses };
  an._consistent = muses.length === 0;
  an._selfContra = muses.filter(m => m.length === 1).map(m => m[0]).sort((a, b) => a - b);
  return an;
}

function subContext(ctx, indices) {
  return { kb: ctx.kb.subset(indices), an: deriveAnalysis(ctx.an, indices) };
}

function maskToIndices(mask, n) { const r = []; for (let i = 0; i < n; i++) if (mask & (1 << i)) r.push(i); return r; }

const SHAPLEY_MAX = 14;

// Shapley inconsistency values for all formulas (Hunter, Konieczny 2010).
function shapleyValues(ctx, measureId, params, onProgress) {
  const n = ctx.kb.size;
  if (n > SHAPLEY_MAX) throw new LimitError('Shapley values need all 2^n sub-bases; at most ' + SHAPLEY_MAX + ' formulas are supported.');
  const m = MEASURE_BY_ID.get(measureId);
  const p = Object.assign(defaultParams(m), params || {});
  ctx.an.enumerate();
  const total = 1 << n;
  const vals = new Float64Array(total);
  for (let mask = 0; mask < total; mask++) {
    checkDeadlineNow();
    vals[mask] = m.compute(subContext(ctx, maskToIndices(mask, n)), p);
    if (onProgress && (mask & 63) === 0) onProgress(mask / total);
  }
  const fac = [1];
  for (let i = 1; i <= n; i++) fac.push(fac[i - 1] * i);
  const res = [];
  for (let i = 0; i < n; i++) {
    let sum = 0;
    for (let mask = 0; mask < total; mask++) {
      if (mask & (1 << i)) continue;
      const s = popcount32(mask);
      let t = vals[mask | (1 << i)] - vals[mask];
      t *= fac[s]; t *= fac[n - s - 1]; t /= fac[n];
      sum += t;
    }
    res.push(sum);
  }
  return { values: res, total: vals[total - 1] };
}

// I(K) - I(K \ {φ}) for every formula.
function removalImpact(ctx, measureId, params) {
  const m = MEASURE_BY_ID.get(measureId);
  const p = Object.assign(defaultParams(m), params || {});
  const n = ctx.kb.size;
  const all = m.compute(ctx, p);
  const res = [];
  for (let i = 0; i < n; i++) {
    checkDeadlineNow();
    const idx = [];
    for (let j = 0; j < n; j++) if (j !== i) idx.push(j);
    const v = m.compute(subContext(ctx, idx), p);
    res.push({ without: v, impact: all - v });
  }
  return { total: all, values: res };
}

// ----- Rationality postulates ------------------------------------------------

const P_EPS = 1e-9;
const feq = (a, b) => approxEqual(a, b, P_EPS);
const fle = (a, b) => a <= b || feq(a, b);
const fge = (a, b) => a >= b || feq(a, b);
const fgt = (a, b) => a > b && !feq(a, b);

function bipartitions(n, limit, rng) {
  const res = [];
  if (n < 2) return res;
  const total = Math.pow(2, n - 1) - 1;  // masks with formula 0 in K1, K2 non-empty
  if (total <= limit) {
    for (let mask = 0; mask < total; mask++) {
      const k1 = [0], k2 = [];
      for (let i = 1; i < n; i++) ((mask >> (i - 1)) & 1 ? k1 : k2).push(i);
      if (k2.length) res.push([k1, k2]);
    }
  } else {
    for (let t = 0; t < limit; t++) {
      const k1 = [0], k2 = [];
      for (let i = 1; i < n; i++) (rng() < 0.5 ? k1 : k2).push(i);
      if (k2.length) res.push([k1, k2]); else { k1.pop(); k2.push(n - 1); res.push([k1, k2]); }
    }
  }
  return res;
}

const POSTULATES = [
  { id: 'consistency', name: 'Consistency', short: 'CO', description: 'I(K) = 0 if and only if K is consistent.' },
  { id: 'normalization', name: 'Normalization', short: 'NO', description: '0 ≤ I(K) ≤ 1.' },
  { id: 'monotony', name: 'Monotony', short: 'MO', description: 'I(K) ≤ I(K ∪ K′); checked as I(K∖{φ}) ≤ I(K) for every φ ∈ K.' },
  { id: 'freeformulaindependence', name: 'Free-formula independence', short: 'IN', description: 'If φ is free (in no minimal inconsistent subset), then I(K) = I(K∖{φ}).' },
  { id: 'safeformulaindependence', name: 'Safe-formula independence', short: 'SI', description: 'If φ is consistent and shares no atom with K∖{φ}, then I(K) = I(K∖{φ}).' },
  { id: 'freeformuladilution', name: 'Free-formula dilution', short: 'FD', description: 'If φ is free, then I(K) ≥ I(K∖{φ}) (TweetyProject\'s formulation).' },
  { id: 'dominance', name: 'Dominance', short: 'DO', description: 'If φ is consistent and φ ⊨ ψ, then I(K′ ∪ {φ}) ≥ I(K′ ∪ {ψ}).' },
  { id: 'weakdominance', name: 'Weak dominance', short: 'WD', description: 'Dominance restricted to φ ⊨ ψ where the prime implicants of φ include those of ψ.' },
  { id: 'superadditivity', name: 'Super-additivity', short: 'SA', description: 'If K₁ ∩ K₂ = ∅, then I(K₁ ∪ K₂) ≥ I(K₁) + I(K₂).' },
  { id: 'penalty', name: 'Penalty', short: 'PY', description: 'If φ is not free, then I(K) > I(K∖{φ}).' },
  { id: 'minormalization', name: 'MI-normalization', short: 'MN', description: 'I(M) = 1 for every minimal inconsistent subset M.' },
  { id: 'miseparability', name: 'MI-separability', short: 'MI', description: 'If MI(K₁ ∪ K₂) = MI(K₁) ∪ MI(K₂) (disjointly), then I(K₁ ∪ K₂) = I(K₁) + I(K₂).' },
  { id: 'attenuation', name: 'Attenuation', short: 'AT', description: 'For M, M′ ∈ MI(K) with |M| < |M′|: I(M) > I(M′).' },
  { id: 'equalconflict', name: 'Equal conflict', short: 'EC', description: 'For M, M′ ∈ MI(K) with |M| = |M′|: I(M) = I(M′).' },
  { id: 'adjunctioninvariance', name: 'Adjunction invariance', short: 'AI', description: 'I(K ∪ {φ, ψ}) = I(K ∪ {φ ∧ ψ}).' },
  { id: 'irrelevanceofsyntax', name: 'Irrelevance of syntax', short: 'IS', description: 'Replacing a formula by an equivalent syntactic variant (commuted, NNF, CNF) does not change I.' },
  { id: 'exchange', name: 'Exchange', short: 'EX', description: 'If φ ≡ ψ and φ is consistent, then I(K ∪ {φ}) = I(K ∪ {ψ}).' },
  { id: 'contradiction', name: 'Contradiction', short: 'CD', description: 'I(K) = 1 if and only if every non-empty subset of K is inconsistent.' },
];
const POSTULATE_BY_ID = new Map(POSTULATES.map(p => [p.id, p]));

// Check postulates for one measure on instances derived from kb.
// Returns {postulateId: {instances, violations:[{text, values}]}}
function checkPostulates(kb, measureId, params, postulateIds, options) {
  options = options || {};
  const maxInst = options.maxInstances || 128;
  const rng = makeRng(options.seed || 99);
  const m = MEASURE_BY_ID.get(measureId);
  const p = Object.assign(defaultParams(m), params || {});
  const ctx = makeContext(kb);
  const n = kb.size;
  const cache = new Map();
  const F = kb.formulas;
  const T = (i) => kb.texts[i];
  const I = (indices) => {
    const idx = indices.slice().sort((a, b) => a - b);
    const k = 'S' + idx.join(',');
    if (!cache.has(k)) { checkDeadlineNow(); cache.set(k, idx.length === n ? m.compute(ctx, p) : m.compute(subContext(ctx, idx), p)); }
    return cache.get(k);
  };
  const IF = (formulas) => {
    const kb2 = KnowledgeBase.fromFormulas(formulas);
    const k = 'F' + kb2.key();
    if (!cache.has(k)) { checkDeadlineNow(); cache.set(k, m.compute(makeContext(kb2), p)); }
    return cache.get(k);
  };
  const all = F.map((_, i) => i);
  const without = (...ex) => all.filter(i => !ex.includes(i));
  const fmt = (v) => (typeof v === 'number' ? (Number.isInteger(v) || !isFinite(v) ? String(v) : v.toFixed(6)) : String(v));
  const setStr = (idx) => '{' + idx.map(T).join(', ') + '}';
  const res = {};
  const an = ctx.an;
  const lazy = {};
  const free = () => lazy.free || (lazy.free = an.freeFormulas());
  const muses = () => an.muses();
  const consistentF = (i) => an.selfContradictory().indexOf(i) < 0;

  for (const pid of postulateIds) {
    const out = { instances: 0, violations: [] };
    const viol = (text, values) => { if (out.violations.length < 5) out.violations.push({ text, values }); else out.more = (out.more || 0) + 1; };
    const inst = () => out.instances++ < maxInst;
    switch (pid) {
      case 'consistency': {
        if (n === 0) break;
        inst();
        const v = I(all), cons = an.isConsistent();
        if (cons ? !feq(v, 0) : !(v > 0 && !feq(v, 0))) viol(cons ? 'K is consistent but I(K) ≠ 0' : 'K is inconsistent but I(K) = 0', 'I(K) = ' + fmt(v));
        break;
      }
      case 'normalization': {
        inst();
        const v = I(all);
        if (!(fge(v, 0) && fle(v, 1))) viol('I(K) ∉ [0,1]', 'I(K) = ' + fmt(v));
        break;
      }
      case 'monotony':
        for (let i = 0; i < n && inst(); i++) {
          const a = I(without(i)), b = I(all);
          if (!fle(a, b)) viol('Removing ' + T(i) + ' increases the value', 'I(K∖{φ}) = ' + fmt(a) + ' > I(K) = ' + fmt(b));
        }
        break;
      case 'freeformulaindependence':
      case 'freeformuladilution':
      case 'penalty': {
        const fr = new Set(free());
        for (let i = 0; i < n; i++) {
          const isFree = fr.has(i);
          if ((pid === 'penalty') === isFree) continue;
          if (!inst()) break;
          const a = I(all), b = I(without(i));
          if (pid === 'freeformulaindependence' && !feq(a, b)) viol('Free formula ' + T(i) + ' changes the value', 'I(K) = ' + fmt(a) + ', I(K∖{φ}) = ' + fmt(b));
          if (pid === 'freeformuladilution' && !fge(a, b)) viol('Free formula ' + T(i) + ' decreases the value', 'I(K) = ' + fmt(a) + ' < I(K∖{φ}) = ' + fmt(b));
          if (pid === 'penalty' && !fgt(a, b)) viol('Removing problematic formula ' + T(i) + ' does not decrease the value', 'I(K) = ' + fmt(a) + ', I(K∖{φ}) = ' + fmt(b));
        }
        break;
      }
      case 'safeformulaindependence':
        for (let i = 0; i < n; i++) {
          if (!consistentF(i)) continue;
          const at = new Set(atoms(F[i]));
          let safe = true;
          for (let j = 0; j < n && safe; j++) if (j !== i) for (const a of atoms(F[j])) if (at.has(a)) { safe = false; break; }
          if (!safe) continue;
          if (!inst()) break;
          const a = I(all), b = I(without(i));
          if (!feq(a, b)) viol('Safe formula ' + T(i) + ' changes the value', 'I(K) = ' + fmt(a) + ', I(K∖{φ}) = ' + fmt(b));
        }
        break;
      case 'dominance':
      case 'weakdominance':
        for (let i = 0; i < n; i++) {
          if (!consistentF(i)) continue;
          for (let j = 0; j < n; j++) {
            if (i === j || !entails([F[i]], F[j])) continue;
            if (pid === 'weakdominance') {
              let ok;
              try {
                const pi = new Set(primeImplicants(F[i]).map(t => t.join('&')));
                ok = primeImplicants(F[j]).every(t => pi.has(t.join('&')));
              } catch (e) { ok = false; }
              if (!ok) continue;
            }
            if (!inst()) break;
            const a = I(without(j)), b = I(without(i));
            if (!fge(a, b)) viol(T(i) + ' ⊨ ' + T(j) + ' but I(K′ ∪ {' + T(i) + '}) < I(K′ ∪ {' + T(j) + '})', fmt(a) + ' < ' + fmt(b));
          }
        }
        break;
      case 'superadditivity':
      case 'miseparability': {
        const mu = muses();
        for (const [k1, k2] of bipartitions(n, maxInst, rng)) {
          if (pid === 'miseparability') {
            const s1 = new Set(k1), s2 = new Set(k2);
            if (!mu.every(M => M.every(i => s1.has(i)) || M.every(i => s2.has(i)))) continue;
          }
          if (!inst()) break;
          const a = I(all), b = I(k1), c = I(k2);
          if (pid === 'superadditivity' && !fge(a, b + c)) viol('K₁ = ' + setStr(k1) + ', K₂ = ' + setStr(k2), 'I(K) = ' + fmt(a) + ' < ' + fmt(b) + ' + ' + fmt(c));
          if (pid === 'miseparability' && !feq(a, b + c)) viol('K₁ = ' + setStr(k1) + ', K₂ = ' + setStr(k2), 'I(K) = ' + fmt(a) + ' ≠ ' + fmt(b) + ' + ' + fmt(c));
        }
        break;
      }
      case 'minormalization':
        for (const M of muses()) {
          if (!inst()) break;
          const v = I(M);
          if (!feq(v, 1)) viol('M = ' + setStr(M), 'I(M) = ' + fmt(v));
        }
        break;
      case 'attenuation':
      case 'equalconflict': {
        const mu = muses();
        for (let x = 0; x < mu.length; x++) for (let y = 0; y < mu.length; y++) {
          if (x === y) continue;
          const A = mu[x], B = mu[y];
          if (pid === 'attenuation' && !(A.length < B.length)) continue;
          if (pid === 'equalconflict' && !(A.length === B.length && x < y)) continue;
          if (!inst()) break;
          const a = I(A), b = I(B);
          if (pid === 'attenuation' && !fgt(a, b)) viol('M = ' + setStr(A) + ', M′ = ' + setStr(B), 'I(M) = ' + fmt(a) + ' ≤ I(M′) = ' + fmt(b));
          if (pid === 'equalconflict' && !feq(a, b)) viol('M = ' + setStr(A) + ', M′ = ' + setStr(B), 'I(M) = ' + fmt(a) + ' ≠ I(M′) = ' + fmt(b));
        }
        break;
      }
      case 'adjunctioninvariance':
        for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
          if (!inst()) break;
          const rest = F.filter((_, t) => t !== i && t !== j);
          const a = I(all), b = IF(rest.concat([And([F[i], F[j]])]));
          if (!feq(a, b)) viol('Joining ' + T(i) + ' and ' + T(j), 'I(K) = ' + fmt(a) + ', after conjunction ' + fmt(b));
        }
        break;
      case 'irrelevanceofsyntax':
        for (let i = 0; i < n; i++) {
          const variants = new Map();
          const add = (g) => { if (key(g) !== key(F[i])) variants.set(key(g), g); };
          add(commuted(F[i]));
          add(toNnf(F[i]));
          try { add(toCnfFormula(F[i])); } catch (e) { /* too large */ }
          for (const g of variants.values()) {
            if (!inst()) break;
            const a = I(all), b = IF(F.map((h, t) => t === i ? g : h));
            if (!feq(a, b)) viol('Replacing ' + T(i) + ' by ' + toPretty(g), 'I = ' + fmt(a) + ' vs. ' + fmt(b));
          }
        }
        break;
      case 'exchange':
        for (let i = 0; i < n; i++) {
          if (!consistentF(i)) continue;
          for (let j = 0; j < n; j++) {
            if (i === j || !equivalent(F[i], F[j])) continue;
            if (!inst()) break;
            const a = I(without(i)), b = I(without(j));
            if (!feq(a, b)) viol(T(i) + ' ≡ ' + T(j), 'I(K∖{' + T(i) + '}) = ' + fmt(a) + ' ≠ I(K∖{' + T(j) + '}) = ' + fmt(b));
          }
        }
        break;
      case 'contradiction': {
        if (n === 0) break;
        inst();
        const allContra = an.selfContradictory().length === n;
        const v = I(all);
        if (allContra !== feq(v, 1)) viol(allContra ? 'All non-empty subsets are inconsistent but I(K) ≠ 1' : 'K has a consistent non-empty subset but I(K) = 1', 'I(K) = ' + fmt(v));
        break;
      }
      default: throw new Error('Unknown postulate ' + pid);
    }
    out.instances = Math.min(out.instances, maxInst);
    res[pid] = out;
  }
  return res;
}

// ----- Random knowledge bases --------------------------------------------------

const DEFAULT_SAMPLER = {
  atoms: 4, minFormulas: 3, maxFormulas: 6, maxDepth: 2,
  pNot: 0.15, pAnd: 0.3, pOr: 0.3, pImpl: 0.15, pEquiv: 0.07, pXor: 0.03,
  pLiteralNeg: 0.4, pLeaf: 0.25, constants: false, mode: 'syntactic', clauseLength: 3, seed: 1,
};

function sampleFormula(rng, atomNames, depth, o) {
  const literal = () => {
    if (o.constants && rng() < 0.03) return rng() < 0.5 ? TOP : BOT;
    const a = Prop(rng.pick(atomNames));
    return rng() < o.pLiteralNeg ? Not(a) : a;
  };
  if (depth <= 0 || rng() < o.pLeaf) return literal();
  const w = [o.pNot, o.pAnd, o.pOr, o.pImpl, o.pEquiv, o.pXor];
  const tot = w.reduce((a, b) => a + b, 0) || 1;
  let r = rng() * tot, op = 0;
  while (op < w.length - 1 && r >= w[op]) { r -= w[op]; op++; }
  const sub = () => sampleFormula(rng, atomNames, depth - 1, o);
  const nary = () => { const k = rng.int(2, 3); const l = []; for (let i = 0; i < k; i++) l.push(sub()); return l; };
  switch (op) {
    case 0: return Not(sub());
    case 1: return And(nary());
    case 2: return Or(nary());
    case 3: return Impl(sub(), sub());
    case 4: return Equiv(sub(), sub());
    default: return Xor([sub(), sub()]);
  }
}

function sampleKB(options, rngOrSeed) {
  const o = Object.assign({}, DEFAULT_SAMPLER, options || {});
  const rng = typeof rngOrSeed === 'function' ? rngOrSeed : makeRng(rngOrSeed != null ? rngOrSeed : o.seed);
  const atomNames = [];
  const letters = 'abcdefghijklmnopqrstuvwxyz';
  for (let i = 0; i < o.atoms; i++) atomNames.push(o.atoms <= 26 ? letters[i] : 'x' + (i + 1));
  const nForm = rng.int(Math.max(0, o.minFormulas), Math.max(o.minFormulas, o.maxFormulas));
  const seen = new Set(), fs = [];
  for (let tries = 0; fs.length < nForm && tries < nForm * 20; tries++) {
    let f;
    if (o.mode === 'cnf') {
      const k = Math.max(1, o.clauseLength), lits = [];
      for (let i = 0; i < k; i++) { const a = Prop(rng.pick(atomNames)); lits.push(rng() < 0.5 ? Not(a) : a); }
      f = lits.length === 1 ? lits[0] : Or(lits);
    } else {
      f = sampleFormula(rng, atomNames, rng.int(0, o.maxDepth), o);
    }
    f = parseFormula(toTweetyString(f));
    const k = key(f);
    if (seen.has(k)) continue;
    seen.add(k);
    fs.push(f);
  }
  return new KnowledgeBase(fs, fs.map(f => toPretty(f)));
}

// Postulate compliance over random knowledge bases.
function postulatesOnRandom(measureId, params, postulateIds, samplerOptions, count, onProgress) {
  const rng = makeRng((samplerOptions && samplerOptions.seed) || 1);
  const agg = {};
  for (const pid of postulateIds) agg[pid] = { kbs: 0, applicable: 0, violatedKbs: 0, instances: 0, example: null };
  for (let t = 0; t < count; t++) {
    checkDeadlineNow();
    const kb = sampleKB(samplerOptions, rng);
    const r = checkPostulates(kb, measureId, params, postulateIds, { maxInstances: 32, seed: t + 1 });
    for (const pid of postulateIds) {
      const a = agg[pid], x = r[pid];
      a.kbs++;
      if (x.instances > 0) a.applicable++;
      a.instances += x.instances;
      if (x.violations.length) {
        a.violatedKbs++;
        if (!a.example) a.example = { kb: kb.texts.slice(), violation: x.violations[0] };
      }
    }
    if (onProgress) onProgress((t + 1) / count);
  }
  return agg;
}

// ----- Incremental analysis ---------------------------------------------------------

function incrementalValues(kb, measures, onProgress) {
  const ctx = makeContext(kb);
  const n = kb.size;
  const series = measures.map(() => []);
  for (let j = 1; j <= n; j++) {
    const idx = [];
    for (let i = 0; i < j; i++) idx.push(i);
    const sub = j === n ? ctx : subContext(ctx, idx);
    measures.forEach((ms, t) => {
      checkDeadlineNow();
      const m = MEASURE_BY_ID.get(ms.id);
      let v;
      try { v = m.compute(sub, Object.assign(defaultParams(m), ms.params || {})); } catch (e) { if (e instanceof TimeoutError) throw e; v = null; }
      series[t].push(v);
    });
    if (onProgress) onProgress(j / n);
  }
  return series;
}

// ----- Rank correlation -----------------------------------------------------------------

function kendallTauB(x, y) {
  let nc = 0, nd = 0, tx = 0, ty = 0;
  const n = x.length;
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
    const dx = Math.sign(cmpVal(x[i], x[j])), dy = Math.sign(cmpVal(y[i], y[j]));
    if (dx === 0 && dy === 0) continue;
    if (dx === 0) { tx++; continue; }
    if (dy === 0) { ty++; continue; }
    if (dx === dy) nc++; else nd++;
  }
  const den = Math.sqrt((nc + nd + tx) * (nc + nd + ty));
  return den === 0 ? NaN : (nc - nd) / den;
}
function cmpVal(a, b) {
  if (a === b) return 0;
  if (Math.abs(a - b) <= 1e-9 * Math.max(1, Math.abs(a), Math.abs(b))) return 0;
  return a < b ? -1 : 1;
}

function compareMeasures(measures, samplerOptions, count, onProgress) {
  const rng = makeRng((samplerOptions && samplerOptions.seed) || 1);
  const kbs = [], values = measures.map(() => []);
  for (let t = 0; t < count; t++) {
    checkDeadlineNow();
    const kb = sampleKB(samplerOptions, rng);
    const ctx = makeContext(kb);
    const row = [];
    let ok = true;
    for (const ms of measures) {
      const m = MEASURE_BY_ID.get(ms.id);
      let v;
      try { v = m.compute(ctx, Object.assign(defaultParams(m), ms.params || {})); } catch (e) { if (e instanceof TimeoutError) throw e; v = NaN; }
      if (Number.isNaN(v)) ok = false;
      row.push(v);
    }
    if (ok) { kbs.push(kb.texts); row.forEach((v, i) => values[i].push(v)); }
    if (onProgress) onProgress((t + 1) / count);
  }
  const k = measures.length;
  const tau = [];
  for (let i = 0; i < k; i++) { tau.push([]); for (let j = 0; j < k; j++) tau[i].push(i === j ? 1 : kendallTauB(values[i], values[j])); }
  return { tau, values, kbs };
}

// ----- Possible worlds ------------------------------------------------------------------

function possibleWorlds(kb, maxAtoms) {
  const nA = kb.atoms.length;
  if (nA > (maxAtoms || 12)) throw new LimitError('Too many atoms to list all possible worlds (' + nA + ').');
  const tts = kb.formulas.map(f => truthTable(f, kb.atomIndex, nA));
  const dt = kb.formulas.map(dalalTable);
  const worlds = [];
  for (let w = 0; w < (1 << nA); w++) {
    const sat = [], dist = [];
    kb.formulas.forEach((f, i) => {
      sat.push(ttGet(tts[i], w) === 1);
      let li = 0;
      dt[i].atoms.forEach((a, j) => { if (w & (1 << kb.atomIndex.get(a))) li |= 1 << j; });
      const d = dt[i].dist[li];
      dist.push(d === INF16 ? Infinity : d);
    });
    worlds.push({ w, sat, dist });
  }
  return { atoms: kb.atoms, worlds };
}

// ----- Structure --------------------------------------------------------------------------

function structure(ctx) {
  const an = ctx.an;
  const e = an.enumerate();
  return {
    consistent: an.isConsistent(),
    muses: e.muses, mcses: e.mcses, msses: e.msses,
    free: an.freeFormulas(), problematic: an.problematicFormulas(),
    selfContradictory: an.selfContradictory(),
    components: an.miComponents(),
    atoms: ctx.kb.atoms,
  };
}

IM.deriveAnalysis = deriveAnalysis;
IM.subContext = subContext;
IM.shapleyValues = shapleyValues;
IM.removalImpact = removalImpact;
IM.POSTULATES = POSTULATES;
IM.POSTULATE_BY_ID = POSTULATE_BY_ID;
IM.checkPostulates = checkPostulates;
IM.postulatesOnRandom = postulatesOnRandom;
IM.DEFAULT_SAMPLER = DEFAULT_SAMPLER;
IM.sampleKB = sampleKB;
IM.incrementalValues = incrementalValues;
IM.kendallTauB = kendallTauB;
IM.compareMeasures = compareMeasures;
IM.possibleWorlds = possibleWorlds;
IM.structure = structure;

// ===== 09-api.js =====
// ---------------------------------------------------------------------------
// Request API used by the Web Worker (and usable directly).
// handleRequest(req, progress) -> result; throws on errors / timeouts.
// Analysis contexts are cached per knowledge base so that MUS enumeration is
// shared between measures.
// ---------------------------------------------------------------------------

const ctxCache = new Map();
function contextFor(text) {
  let ctx = ctxCache.get(text);
  if (ctx) { ctxCache.delete(text); ctxCache.set(text, ctx); return ctx; }
  const { kb, errors } = parseKB(text);
  if (errors.length) throw new Error('Knowledge base contains syntax errors (line ' + errors[0].line + ': ' + errors[0].message + ')');
  ctx = makeContext(kb);
  ctxCache.set(text, ctx);
  while (ctxCache.size > 8) ctxCache.delete(ctxCache.keys().next().value);
  return ctx;
}

function serializeValue(v) {
  if (typeof v !== 'number') return v;
  if (Number.isNaN(v)) return 'NaN';
  if (v === Infinity) return 'Infinity';
  if (v === -Infinity) return '-Infinity';
  return v;
}
function deserializeValue(v) {
  if (v === 'NaN') return NaN;
  if (v === 'Infinity') return Infinity;
  if (v === '-Infinity') return -Infinity;
  return v;
}

function measureInfo() {
  return MEASURES.map(m => ({ id: m.id, label: m.label, symbol: m.symbol, family: m.family, description: m.description, reference: m.reference, java: m.java, params: m.params || [], approximate: !!m.approximate }));
}

function handleRequest(req, progress) {
  progress = progress || (() => {});
  switch (req.op) {
    case 'info':
      return { measures: measureInfo(), postulates: POSTULATES };
    case 'measure': {
      const ctx = contextFor(req.text);
      const m = MEASURE_BY_ID.get(req.id);
      if (!m) throw new Error('Unknown measure ' + req.id);
      const t0 = Date.now();
      const v = m.compute(ctx, Object.assign(defaultParams(m), req.params || {}));
      return { value: serializeValue(v), ms: Date.now() - t0 };
    }
    case 'structure': {
      const ctx = contextFor(req.text);
      const t0 = Date.now();
      const s = structure(ctx);
      s.ms = Date.now() - t0;
      s.satCalls = ctx.an.satCalls;
      return s;
    }
    case 'shapley': {
      const ctx = contextFor(req.text);
      const r = shapleyValues(ctx, req.id, req.params, progress);
      return { values: r.values.map(serializeValue), total: serializeValue(r.total) };
    }
    case 'removal': {
      const ctx = contextFor(req.text);
      const r = removalImpact(ctx, req.id, req.params);
      return { total: serializeValue(r.total), values: r.values.map(x => ({ without: serializeValue(x.without), impact: serializeValue(x.impact) })) };
    }
    case 'postulates': {
      if (req.mode === 'random') {
        const out = {};
        req.measures.forEach((ms, i) => {
          out[ms.key || ms.id] = postulatesOnRandom(ms.id, ms.params, req.postulates, req.sampler, req.count,
            (f) => progress((i + f) / req.measures.length));
        });
        return out;
      }
      const ctx = contextFor(req.text);
      const out = {};
      req.measures.forEach((ms, i) => {
        out[ms.key || ms.id] = checkPostulates(ctx.kb, ms.id, ms.params, req.postulates, { maxInstances: req.maxInstances || 128 });
        progress((i + 1) / req.measures.length);
      });
      return out;
    }
    case 'incremental': {
      const ctx = contextFor(req.text);
      const series = incrementalValues(ctx.kb, req.measures, progress);
      return { series: series.map(s => s.map(serializeValue)) };
    }
    case 'compare': {
      const r = compareMeasures(req.measures, req.sampler, req.count, progress);
      return { tau: r.tau.map(row => row.map(serializeValue)), values: r.values.map(s => s.map(serializeValue)), kbs: r.kbs };
    }
    case 'worlds': {
      const ctx = contextFor(req.text);
      const r = possibleWorlds(ctx.kb, req.maxAtoms || 12);
      return { atoms: r.atoms, worlds: r.worlds.map(w => ({ w: w.w, sat: w.sat, dist: w.dist.map(serializeValue) })) };
    }
    case 'sample': {
      const kb = sampleKB(req.sampler, req.seed);
      return { text: kb.formulas.map(f => toPretty(f)).join('\n') };
    }
    default:
      throw new Error('Unknown request ' + req.op);
  }
}

IM.handleRequest = handleRequest;
IM.serializeValue = serializeValue;
IM.deserializeValue = deserializeValue;
IM.measureInfo = measureInfo;

IM.version = '1.0.0';
return IM;
}
(function (root) {
  const IM = imCore();
  if (typeof module !== 'undefined' && module.exports) module.exports = IM;
  else root.IM = IM;
})(typeof self !== 'undefined' ? self : this);
