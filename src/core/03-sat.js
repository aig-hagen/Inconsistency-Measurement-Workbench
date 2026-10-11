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
