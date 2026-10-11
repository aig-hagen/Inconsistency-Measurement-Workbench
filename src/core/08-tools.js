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
