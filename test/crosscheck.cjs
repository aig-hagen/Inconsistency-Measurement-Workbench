// Cross-checks alternative JavaScript code paths on random knowledge bases:
//  - Dalal measures: world enumeration vs. SAT encoding (used for large signatures)
//  - sub-base analyses derived from the parent (Shapley/postulates) vs. fresh MUS enumeration
const IM = require('../dist/im-core.js');
let fails = 0, n = 0;
for (let t = 0; t < 300; t++) {
  const kb = IM.sampleKB({ atoms: 3 + (t % 8), minFormulas: 2, maxFormulas: 9, maxDepth: 3, constants: t % 5 === 0, pXor: 0.08 }, 1000 + t);
  const ctx = IM.makeContext(kb);
  for (const mode of ['sum', 'max', 'hit']) {
    const a = IM.dalalByEnumeration(kb, mode), b = IM.dalalBySat(ctx, mode);
    n++;
    if (a !== b) { fails++; console.log('DALAL', mode, a, b, kb.texts.join(' ; ')); }
  }
  // derived sub-base analysis vs fresh
  const idx = kb.formulas.map((_, i) => i).filter((_, i) => (t >> (i % 5)) & 1 || i % 2 === 0);
  const d = IM.deriveAnalysis(ctx.an, idx);
  const fresh = new IM.KBAnalysis(kb.subset(idx));
  const key = (e) => JSON.stringify([e.muses, e.msses, e.mcses]);
  n++;
  if (key(d.enumerate()) !== key(fresh.enumerate())) { fails++; console.log('DERIVE', JSON.stringify(idx), kb.texts.join(' ; ')); }
}
console.log('cross-checks:', n, 'comparisons,', fails, 'failures');
process.exit(fails ? 1 : 0);
