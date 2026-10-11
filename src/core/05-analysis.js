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
