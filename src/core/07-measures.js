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
