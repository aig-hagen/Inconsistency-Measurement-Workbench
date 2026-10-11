// Quick smoke test of the core library on textbook examples.
const IM = require('../dist/im-core.js');

const examples = {
  'a,!a': 'a\n!a',
  'classic': 'a\n!a\nb\n!b\na || b',
  'thimm': 'a && c\n!a\nb\n!b\na || !b',
  'chain': 'a\na => b\nb => c\n!c',
  'consistent': 'a\nb\na => b',
  'selfcontra': 'a && !a\nb',
  'empty': '',
};
const ids = IM.MEASURES.map(m => m.id);
for (const [name, text] of Object.entries(examples)) {
  const { kb, errors } = IM.parseKB(text);
  if (errors.length) { console.log(name, errors); continue; }
  const ctx = IM.makeContext(kb);
  const out = {};
  for (const id of ids) {
    const t0 = Date.now();
    try { out[id] = IM.computeMeasure(id, ctx); } catch (e) { out[id] = 'ERR ' + e.message; }
    const dt = Date.now() - t0;
    if (dt > 200) out[id] += ` (${dt}ms)`;
  }
  console.log('==', name, '| MUS:', JSON.stringify(ctx.an.muses()), 'MCS:', JSON.stringify(ctx.an.mcses()));
  console.log(Object.entries(out).map(([k, v]) => `${k}=${typeof v === 'number' ? +v.toFixed(6) : v}`).join('  '));
}
