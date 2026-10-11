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
