// Internal consistency checks for the CDCL solver: brute force comparison on
// small random CNFs, model verification, assumption cores, incremental use.
const IM = require('../dist/im-core.js');
const rng = IM.makeRng(4711);

function randomCnf(n, m, kmin, kmax) {
  const cls = [];
  for (let i = 0; i < m; i++) {
    const k = rng.int(kmin, kmax);
    const c = [];
    for (let j = 0; j < k; j++) { const v = rng.int(1, n); c.push(rng() < 0.5 ? v : -v); }
    cls.push(c);
  }
  return cls;
}
function brute(n, cls) {
  for (let w = 0; w < (1 << n); w++) {
    if (cls.every(c => c.some(l => ((w >> (Math.abs(l) - 1)) & 1) === (l > 0 ? 1 : 0)))) return true;
  }
  return false;
}
function check(cls, model) { return cls.every(c => c.some(l => (model[Math.abs(l)] === 1) === (l > 0))); }

let fails = 0, sat = 0;
for (let t = 0; t < 3000; t++) {
  const n = rng.int(1, 14), m = rng.int(1, Math.round(n * 6));
  const cls = randomCnf(n, m, 1, 4);
  const r = IM.solveCnf(cls, n);
  const b = brute(n, cls);
  if (r.sat !== b) { fails++; console.log('MISMATCH', n, JSON.stringify(cls)); }
  if (r.sat) { sat++; if (!check(cls, r.model)) { fails++; console.log('BAD MODEL'); } }
}
console.log('brute-force comparison: 3000 instances,', sat, 'SAT,', fails, 'failures');

// assumptions + cores + incremental clause addition
let coreFails = 0;
for (let t = 0; t < 2000; t++) {
  const n = rng.int(3, 12);
  const cls = randomCnf(n, rng.int(1, n * 3), 2, 3);
  const s = new IM.SatSolver();
  s.ensureVars(n);
  for (const c of cls) s.addClause(c);
  for (let round = 0; round < 5; round++) {
    const assum = [];
    for (let v = 1; v <= n; v++) if (rng() < 0.4) assum.push(rng() < 0.5 ? v : -v);
    const res = s.solve(assum);
    const all = cls.concat(assum.map(a => [a]));
    const b = brute(n, all);
    if (res !== b) { coreFails++; console.log('ASSUMPTION MISMATCH'); }
    if (!res) {
      // core must be a subset of the assumptions and itself inconsistent with the clauses
      const core = s.core;
      if (!core.every(l => assum.includes(l))) { coreFails++; console.log('CORE NOT SUBSET'); }
      if (brute(n, cls.concat(core.map(a => [a])))) { coreFails++; console.log('CORE SAT', JSON.stringify(cls), assum, core); }
    } else if (!check(all, s.model)) { coreFails++; console.log('BAD MODEL (assumptions)'); }
    // incremental: add a random clause
    const c = randomCnf(n, 1, 2, 3)[0];
    cls.push(c); s.addClause(c);
  }
}
console.log('assumptions/cores/incremental: 10000 solves,', coreFails, 'failures');

// performance on harder instances
for (const [n, ratio] of [[100, 4.26], [150, 4.26], [200, 4.2]]) {
  let t0 = Date.now(), nsat = 0;
  for (let i = 0; i < 10; i++) {
    const cls = randomCnf(n, Math.round(n * ratio), 3, 3);
    const r = IM.solveCnf(cls, n);
    if (r.sat) { nsat++; if (!check(cls, r.model)) console.log('BAD MODEL large'); }
  }
  console.log(`3-SAT n=${n} ratio=${ratio}: 10 instances, ${nsat} SAT, ${Date.now() - t0} ms`);
}
process.exit(fails + coreFails > 0 ? 1 : 0);
