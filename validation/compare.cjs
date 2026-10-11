// Compares Java and JavaScript results.
// CLI:    node compare.cjs <kbFile> <jsResults> <javaResults...>
// Module: compare(kbFile, jsFile, javaFiles) -> {stats, details, kbs}
const fs = require('fs');

function readKbs(kbFile) {
  const kbs = [];
  let cur = null;
  for (const line of fs.readFileSync(kbFile, 'utf8').split('\n')) {
    if (line.startsWith('# kb')) { if (cur) kbs.push(cur); cur = []; }
    else if (line.trim()) cur.push(line.trim());
  }
  if (cur) kbs.push(cur);
  return kbs;
}
const load = (f) => fs.existsSync(f) ? fs.readFileSync(f, 'utf8').trim().split('\n').filter(Boolean).map(l => JSON.parse(l)) : [];
const num = (v) => v === 'NaN' ? NaN : v === 'Infinity' ? Infinity : v === '-Infinity' ? -Infinity : v;
function tolFor(m) {
  if (m.startsWith('fuzzy')) return 1e-3;
  if (m === 'eta' || m === 'cc' || m === 'csp') return 1e-6;   // simplex / GLPK output precision
  if (m.startsWith('shapley')) return 1e-6;
  return 1e-9;
}
function eq(a, b, tol) {
  if (Number.isNaN(a) || Number.isNaN(b)) return Number.isNaN(a) && Number.isNaN(b);
  if (!isFinite(a) || !isFinite(b)) return a === b;
  return Math.abs(a - b) <= tol * Math.max(1, Math.abs(a), Math.abs(b));
}
function eqVal(a, b, tol) {
  if (Array.isArray(a) || Array.isArray(b)) {
    if (!Array.isArray(a) || !Array.isArray(b) || a.length !== b.length) return false;
    return a.every((x, i) => eq(num(x), num(b[i]), tol));
  }
  return eq(num(a), num(b), tol);
}

function compare(kbFile, jsFile, javaFiles) {
  const kbs = readKbs(kbFile);
  const js = new Map();
  for (const o of load(jsFile)) js.set(o.kb + '|' + o.m, o);
  // later files override earlier ones for the same (kb, measure), e.g. retries
  const jmap = new Map();
  for (const f of javaFiles) for (const o of load(f)) jmap.set(o.kb + '|' + o.m, o);
  const java = Array.from(jmap.values());
  const stats = {}, details = {};
  for (const o of java) {
    const jsId = o.m.replace(/_sat$/, '');
    const st = stats[o.m] || (stats[o.m] = { total: 0, match: 0, mismatch: 0, javaTimeout: 0, javaError: 0, convention: 0, jsBetter: 0, jsError: 0 });
    const det = details[o.m] || (details[o.m] = { mismatches: [], javaErrors: {}, javaErrorKbs: [], conventions: {}, jsBetter: [] });
    st.total++;
    const j = js.get(o.kb + '|' + jsId);
    if (o.status === 'timeout') { st.javaTimeout++; continue; }
    if (!j || j.status) { st.jsError++; det.mismatches.push({ kb: o.kb, java: o.v, js: j ? j.status + ': ' + j.msg : 'missing' }); continue; }
    if (o.status === 'error') {
      const msg = o.msg.replace(/\s*\(.*$/, '').replace(/class org\.tweetyproject\.[a-z.]*\./g, '').slice(0, 120);
      if (/no paraconsistent model/.test(o.msg) && num(j.v) === Infinity) {
        st.convention++;
        const c = 'Java throws "no paraconsistent model found", JS returns ∞';
        det.conventions[c] = (det.conventions[c] || 0) + 1;
        continue;
      }
      st.javaError++;
      det.javaErrors[msg] = (det.javaErrors[msg] || 0) + 1;
      det.javaErrorKbs.push(o.kb);
      continue;
    }
    if (eqVal(o.v, j.v, tolFor(o.m))) { st.match++; continue; }
    if (o.m === 'fb' && o.v === 2147483647 && num(j.v) === Infinity) {
      st.convention++;
      const c = 'Java returns Integer.MAX_VALUE, JS returns ∞';
      det.conventions[c] = (det.conventions[c] || 0) + 1;
      continue;
    }
    if (o.m.startsWith('fuzzy') && typeof j.v === 'number' && typeof o.v === 'number' && j.v < o.v) { st.jsBetter++; det.jsBetter.push({ kb: o.kb, java: o.v, js: j.v }); continue; }
    st.mismatch++;
    det.mismatches.push({ kb: o.kb, java: o.v, js: j.v });
  }
  return { stats, details, kbs };
}

if (require.main === module) {
  const [kbFile, jsFile, ...javaFiles] = process.argv.slice(2);
  const { stats, details, kbs } = compare(kbFile, jsFile, javaFiles);
  console.log('measure'.padEnd(28) + ' total  match  conv  better  mism  j-to  j-err  js-err');
  for (const [m, s] of Object.entries(stats)) {
    console.log(m.padEnd(28) + [s.total, s.match, s.convention, s.jsBetter, s.mismatch, s.javaTimeout, s.javaError, s.jsError].map(x => String(x).padStart(6)).join(' '));
  }
  for (const [m, d] of Object.entries(details)) {
    if (!d.mismatches.length && !Object.keys(d.javaErrors).length) continue;
    console.log('\n## ' + m);
    for (const [msg, c] of Object.entries(d.javaErrors)) console.log('  java error x' + c + ': ' + msg);
    for (const x of d.mismatches.slice(0, 4)) console.log('  kb ' + x.kb + ': java=' + JSON.stringify(x.java) + ' js=' + JSON.stringify(x.js) + '   ' + kbs[x.kb].join(' ; '));
    if (d.mismatches.length > 4) console.log('  ... ' + (d.mismatches.length - 4) + ' more');
  }
}
module.exports = { compare, readKbs, load, num };
