// Generates the seeded validation inputs:
//   data/kbs.txt   1000 random knowledge bases in TweetyProject syntax
//   data/cnfs.txt  1000 random / structured CNF instances (DIMACS blocks)
const fs = require('fs');
const path = require('path');
const IM = require('../dist/im-core.js');
const { Prop, Not, And, Or, Xor, Impl, Equiv, TOP, BOT } = IM.F;

const DATA = path.join(__dirname, 'data');
fs.mkdirSync(DATA, { recursive: true });

// ----- knowledge bases ------------------------------------------------------
function genFormula(rng, atoms, depth) {
  const literal = () => {
    if (rng() < 0.03) return rng() < 0.5 ? TOP : BOT;
    const a = Prop(rng.pick(atoms));
    return rng() < 0.4 ? Not(a) : a;
  };
  if (depth === 0 || rng() < 0.2) return literal();
  const r = rng();
  if (r < 0.15) return Not(genFormula(rng, atoms, depth - 1));
  if (r < 0.45) { const k = rng.int(2, 3); const l = []; for (let i = 0; i < k; i++) l.push(genFormula(rng, atoms, depth - 1)); return And(l); }
  if (r < 0.75) { const k = rng.int(2, 3); const l = []; for (let i = 0; i < k; i++) l.push(genFormula(rng, atoms, depth - 1)); return Or(l); }
  if (r < 0.90) return Impl(genFormula(rng, atoms, depth - 1), genFormula(rng, atoms, depth - 1));
  if (r < 0.97) return Equiv(genFormula(rng, atoms, depth - 1), genFormula(rng, atoms, depth - 1));
  // XOR only over literals (TweetyProject's SAT interface fails on complex XOR operands)
  const lit = () => { const a = Prop(rng.pick(atoms)); return rng() < 0.4 ? Not(a) : a; };
  return Xor([lit(), lit()]);
}

let kbOut = '';
for (let i = 0; i < 1000; i++) {
  const rng = IM.makeRng(100003 * (i + 1));
  const nAtoms = rng.int(1, 5);
  const atoms = ['a', 'b', 'c', 'd', 'e'].slice(0, nAtoms);
  const nForm = rng.int(1, 8);
  const seen = new Set();
  const fs_ = [];
  for (let tries = 0; fs_.length < nForm && tries < 50; tries++) {
    const depth = rng.pick([0, 0, 1, 1, 2, 2, 3]);
    const f = genFormula(rng, atoms, depth);
    // TweetyProject's Sat4jSolver crashes on top-level XOR formulas (documented separately)
    if (f.t === 'xor') continue;
    const s = IM.toTweetyString(f);
    // re-parse to obtain exactly the structure TweetyProject will see
    const g = IM.parseFormula(s);
    const k = IM.key(g);
    if (seen.has(k)) continue;
    seen.add(k);
    fs_.push(s);
  }
  kbOut += `# kb ${i}\n` + fs_.join('\n') + '\n';
}
fs.writeFileSync(path.join(DATA, 'kbs.txt'), kbOut);

// ----- CNF instances ----------------------------------------------------------
const rng = IM.makeRng(20251010);
const instances = [];
function randomKSat(n, m, kmin, kmax) {
  const cls = [];
  for (let i = 0; i < m; i++) {
    const k = rng.int(kmin, kmax), c = new Set();
    while (c.size < Math.min(k, n)) { const v = rng.int(1, n); if (!c.has(v) && !c.has(-v)) c.add(rng() < 0.5 ? v : -v); }
    cls.push(Array.from(c));
  }
  return { n, cls, kind: `random ${kmin}-${kmax}-SAT` };
}
function pigeonhole(h) {   // h+1 pigeons, h holes: UNSAT
  const v = (p, j) => p * h + j + 1;
  const cls = [];
  for (let p = 0; p <= h; p++) { const c = []; for (let j = 0; j < h; j++) c.push(v(p, j)); cls.push(c); }
  for (let j = 0; j < h; j++) for (let p = 0; p <= h; p++) for (let q = p + 1; q <= h; q++) cls.push([-v(p, j), -v(q, j)]);
  return { n: (h + 1) * h, cls, kind: 'pigeonhole' };
}
function parity(n, sat) {   // chain of XORs x1^...^xn = b encoded with auxiliary vars
  const cls = [];
  let prev = 1, next = n + 1;
  for (let i = 2; i <= n; i++) {
    const y = next++;
    cls.push([-y, prev, i], [-y, -prev, -i], [y, -prev, i], [y, prev, -i]);
    prev = y;
  }
  cls.push([sat ? prev : -prev]);
  // add a contradicting second chain over a permutation of the variables
  if (!sat) {
    let p2 = n, aux = next;
    for (let i = n - 1; i >= 1; i--) {
      const y = aux++;
      cls.push([-y, p2, i], [-y, -p2, -i], [y, -p2, i], [y, p2, -i]);
      p2 = y;
    }
    cls.push([p2]);
    return { n: aux - 1, cls, kind: 'parity (UNSAT)' };
  }
  return { n: next - 1, cls, kind: 'parity' };
}
function coloring(nv, edgesP, k) {
  const v = (x, c) => x * k + c + 1;
  const cls = [];
  for (let x = 0; x < nv; x++) { const c = []; for (let j = 0; j < k; j++) c.push(v(x, j)); cls.push(c); }
  for (let x = 0; x < nv; x++) for (let y = x + 1; y < nv; y++) if (rng() < edgesP) for (let j = 0; j < k; j++) cls.push([-v(x, j), -v(y, j)]);
  return { n: nv * k, cls, kind: 'graph coloring' };
}
for (let i = 0; i < 400; i++) { const n = rng.int(20, 150); instances.push(randomKSat(n, Math.round(n * (3.6 + rng() * 1.2)), 3, 3)); }
for (let i = 0; i < 300; i++) { const n = rng.int(5, 60); instances.push(randomKSat(n, rng.int(n, n * 5), 1, 6)); }
for (let i = 0; i < 200; i++) { const n = rng.int(3, 12); instances.push(randomKSat(n, rng.int(1, n * 6), 1, 4)); }
for (let i = 0; i < 25; i++) instances.push(pigeonhole(2 + (i % 5)));
for (let i = 0; i < 25; i++) instances.push(parity(rng.int(5, 40), i % 2 === 0));
for (let i = 0; i < 50; i++) instances.push(coloring(rng.int(8, 30), 0.15 + rng() * 0.3, 3));
let cnfOut = '';
instances.forEach((inst, i) => {
  cnfOut += `c instance ${i}\nc kind ${inst.kind}\np cnf ${inst.n} ${inst.cls.length}\n` + inst.cls.map(c => c.join(' ') + ' 0').join('\n') + '\n';
});
fs.writeFileSync(path.join(DATA, 'cnfs.txt'), cnfOut);
fs.writeFileSync(path.join(DATA, 'cnf-kinds.json'), JSON.stringify(instances.map(x => x.kind)));
console.log('wrote 1000 KBs and', instances.length, 'CNF instances');
