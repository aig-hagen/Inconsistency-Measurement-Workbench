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
