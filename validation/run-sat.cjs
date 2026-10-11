// Solves data/cnfs.txt with the JavaScript CDCL solver; verifies every model and
// compares small instances with brute force. Output: data/sat-js.jsonl
const fs = require('fs');
const path = require('path');
const IM = require('../dist/im-core.js');

const text = fs.readFileSync(path.join(__dirname, 'data', 'cnfs.txt'), 'utf8');
const blocks = text.split(/^c instance /m).filter(Boolean);
const out = [];
let t0 = Date.now();
for (const b of blocks) {
  const id = parseInt(b, 10);
  const { nVars, clauses } = IM.parseDimacsCnf(b.slice(b.indexOf('\n') + 1));
  const s0 = Date.now();
  const r = IM.solveCnf(clauses, nVars);
  const ms = Date.now() - s0;
  let modelOk = null;
  if (r.sat) modelOk = clauses.every(c => c.some(l => (r.model[Math.abs(l)] === 1) === (l > 0)));
  let brute = null;
  if (nVars <= 20) {
    brute = false;
    for (let w = 0; w < (1 << nVars) && !brute; w++) {
      if (clauses.every(c => c.some(l => ((w >> (Math.abs(l) - 1)) & 1) === (l > 0 ? 1 : 0)))) brute = true;
    }
  }
  out.push(JSON.stringify({ id, sat: r.sat, modelOk, brute, ms, nVars, nClauses: clauses.length }));
}
fs.writeFileSync(path.join(__dirname, 'data', 'sat-js.jsonl'), out.join('\n') + '\n');
console.log('solved', out.length, 'instances in', Date.now() - t0, 'ms');
