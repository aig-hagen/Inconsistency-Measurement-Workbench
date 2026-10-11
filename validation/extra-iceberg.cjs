// Renaming test for the Java Iceberg implementation: for every knowledge base
// where Java and JS differ (classical consequence), run Java again on a copy
// with renamed atoms (a->p, b->q, c->r, d->s, e->t). Inconsistency values are
// invariant under renaming, so a changed Java value shows dependence on hash
// codes. Writes data/extra-checks.json.
const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');
const { compare } = require('./compare.cjs');
const IM = require('../dist/im-core.js');
const D = (f) => path.join(__dirname, 'data', f);

const op = process.argv[2] || 'iceberg:classical';
const res = compare(D('kbs.txt'), D('js-results.jsonl'), [D('java-results-iceberg.jsonl')]);
const mism = (res.details[op] || { mismatches: [] }).mismatches.filter(x => typeof x.js === 'number' || typeof x.js === 'string');
const ids = mism.map(x => x.kb).slice(0, 150);
const ren = { a: 'p', b: 'q', c: 'r', d: 's', e: 't' };
const rename = (line) => line.replace(/[a-e]/g, (c) => ren[c]);
let orig = '', renamed = '';
ids.forEach((k, i) => {
  orig += `# kb ${i}\n` + res.kbs[k].join('\n') + '\n';
  renamed += `# kb ${i}\n` + res.kbs[k].map(rename).join('\n') + '\n';
});
fs.writeFileSync(D('ice-orig.txt'), orig);
fs.writeFileSync(D('ice-renamed.txt'), renamed);
// original (unpatched) TweetyProject build; run-java.cjs restarts the JVM after timeouts
const cpFile = path.join(__dirname, 'java', 'build', fs.existsSync(path.join(__dirname, 'java', 'build', 'classpath.orig.txt')) ? 'classpath.orig.txt' : 'classpath.txt');
const run = (file) => {
  const out = file.replace(/\.txt$/, '.jsonl');
  if (fs.existsSync(out)) fs.unlinkSync(out);
  execFileSync('node', [path.join(__dirname, 'run-java.cjs'), file, out, op, '20000'], { env: Object.assign({}, process.env, { CP_FILE: cpFile }), stdio: 'ignore' });
  const res = [];
  for (const o of fs.readFileSync(out, 'utf8').trim().split('\n').filter(Boolean).map(l => JSON.parse(l))) res[o.kb] = o;
  return res;
};
const a = run(D('ice-orig.txt')), b = run(D('ice-renamed.txt'));
let changed = 0, tested = 0, jsInvariant = 0;
const examples = [];
const m = op.split(':');
for (let i = 0; i < ids.length; i++) {
  if (!a[i] || !b[i] || a[i].v === undefined || b[i].v === undefined) continue;
  tested++;
  if (a[i].v !== b[i].v) { changed++; if (examples.length < 5) examples.push({ kb: ids[i], java: a[i].v, javaRenamed: b[i].v }); }
  const kbR = IM.parseKB(res.kbs[ids[i]].map(rename).join('\n')).kb;
  const kbO = IM.parseKB(res.kbs[ids[i]].join('\n')).kb;
  const p = { op: m[1], sum: m[2] === 'sum' ? 'true' : 'false' };
  if (IM.computeMeasure('iceberg', kbR, p) === IM.computeMeasure('iceberg', kbO, p)) jsInvariant++;
}
const extraFile = D('extra-checks.json');
const extra = fs.existsSync(extraFile) ? JSON.parse(fs.readFileSync(extraFile, 'utf8')) : {};
extra.icebergRenaming = { op, tested, changed, jsInvariant, examples };
fs.writeFileSync(extraFile, JSON.stringify(extra, null, 1));
console.log(JSON.stringify(extra.icebergRenaming));
