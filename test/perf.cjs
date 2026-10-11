// Runtime probe of all measures on larger random knowledge bases.
const IM = require('../dist/im-core.js');
const configs = [
  { atoms: 8, minFormulas: 15, maxFormulas: 15, maxDepth: 2 },
  { atoms: 15, minFormulas: 30, maxFormulas: 30, maxDepth: 2 },
  { atoms: 30, minFormulas: 60, maxFormulas: 60, maxDepth: 1, mode: 'cnf', clauseLength: 3 },
];
for (const c of configs) {
  const kb = IM.sampleKB(c, 7);
  const ctx = IM.makeContext(kb);
  const t0 = Date.now(); IM.Deadline.set(20000);
  let e; try { e = ctx.an.enumerate(); } catch (x) { e = null; } IM.Deadline.clear();
  console.log(`\n${kb.size} formulas, ${kb.atoms.length} atoms: MUS=${e ? e.muses.length : '?'} MSS=${e ? e.msses.length : '?'} (${Date.now() - t0} ms)`);
  const row = [];
  for (const m of IM.MEASURES) {
    const s = Date.now(); IM.Deadline.set(5000);
    let v; try { v = IM.serializeValue(m.compute(ctx, IM.defaultParams(m))); } catch (x) { v = x.name; }
    IM.Deadline.clear();
    row.push(`${m.id}=${typeof v === 'number' ? +v.toFixed(3) : v}(${Date.now() - s}ms)`);
  }
  console.log(row.join('  '));
}
