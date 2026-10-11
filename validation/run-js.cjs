// Computes the JavaScript values for the validation KBs (same measure ids as
// the Java harness). Usage: node run-js.cjs <kbFile> <outFile> <measureIdsCsv> [timeoutMs]
const fs = require('fs');
const IM = require('../dist/im-core.js');

const [kbFile, outFile, measuresCsv, timeoutArg] = process.argv.slice(2);
const timeout = parseInt(timeoutArg || '20000', 10);
const measures = measuresCsv.split(',');

function readKbs(file) {
  const kbs = [];
  let cur = null;
  for (const line of fs.readFileSync(file, 'utf8').split('\n')) {
    if (line.startsWith('# kb')) { if (cur) kbs.push(cur); cur = []; }
    else if (line.trim()) cur.push(line.trim());
  }
  if (cur) kbs.push(cur);
  return kbs;
}

function resolve(id) {
  const base = id.replace(/_sat$/, '');
  if (base.startsWith('fuzzy:')) { const [, tnorm, variant] = base.split(':'); return { id: 'fuzzy', params: { tnorm, variant } }; }
  if (base.startsWith('iceberg:')) { const [, op, sum] = base.split(':'); return { id: 'iceberg', params: { op, sum: sum === 'sum' ? 'true' : 'false' } }; }
  if (base.startsWith('icebergcompat:')) { const [, op, sum] = base.split(':'); return { id: 'iceberg', params: { op, sum: sum === 'sum' ? 'true' : 'false', javaCompat: true } }; }
  return { id: base, params: {} };
}

const kbs = readKbs(kbFile);
const out = fs.openSync(outFile, 'w');
const t0 = Date.now();
kbs.forEach((lines, k) => {
  const parsed = IM.parseKB(lines.join('\n'));
  if (parsed.errors.length) throw new Error('parse error in kb ' + k + ': ' + JSON.stringify(parsed.errors));
  const context = IM.makeContext(parsed.kb);
  for (const mid of measures) {
    const rec = { kb: k, m: mid };
    const s = Date.now();
    IM.Deadline.set(timeout);
    try {
      if (mid.startsWith('shapley:')) {
        const r = resolve(mid.slice(8));
        rec.v = IM.shapleyValues(context, r.id, r.params).values.map(IM.serializeValue);
      } else {
        const r = resolve(mid);
        rec.v = IM.serializeValue(IM.computeMeasure(r.id, context, r.params));
      }
    } catch (e) {
      rec.status = e instanceof IM.TimeoutError ? 'timeout' : 'error';
      rec.msg = e.message;
    } finally {
      IM.Deadline.clear();
    }
    rec.ms = Date.now() - s;
    fs.writeSync(out, JSON.stringify(rec) + '\n');
  }
  if (k % 100 === 99) process.stdout.write(`${k + 1} KBs (${Math.round((Date.now() - t0) / 1000)}s)\n`);
});
fs.closeSync(out);
console.log('done in', Math.round((Date.now() - t0) / 1000), 's');
