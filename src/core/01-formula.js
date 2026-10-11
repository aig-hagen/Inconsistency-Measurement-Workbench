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
