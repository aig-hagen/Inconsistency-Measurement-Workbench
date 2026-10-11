// Re-runs Java computations that timed out in data/java-results.jsonl with a
// longer time limit; writes data/java-results-retry.jsonl (original KB ids).
// Usage: node retry-java.cjs [timeoutMs] [parallel]
// Environment (all optional, relative to data/): KBS, FROM (comma-separated
// result files), OUT, DIR (work directory), SKIP (measures not retried, default
// fb), and CP_FILE for another Java build (see run-java.cjs).
const fs = require('fs');
const path = require('path');
const { spawn } = require('child_process');
const { readKbs, load } = require('./compare.cjs');
const D = (f) => path.join(__dirname, 'data', f);
const timeout = process.argv[2] || '60000';
const parallel = parseInt(process.argv[3] || '7', 10);

const env = process.env;
const kbs = readKbs(D(env.KBS || 'kbs.txt'));
const skip = (env.SKIP === undefined ? 'fb' : env.SKIP).split(',');
const dir = env.DIR || 'retry';
const todo = new Map();   // measure -> [kb ids]
const latest = new Map();
for (const f of (env.FROM || 'java-results.jsonl').split(',')) for (const o of load(D(f))) latest.set(o.kb + '|' + o.m, o);
for (const o of latest.values()) {
  if (o.status !== 'timeout' || skip.includes(o.m)) continue;
  if (!todo.has(o.m)) todo.set(o.m, []);
  todo.get(o.m).push(o.kb);
}
fs.mkdirSync(D(dir), { recursive: true });
const jobs = [];
for (const [m, ids] of todo) {
  // split long lists so that the parallel workers stay busy
  for (let s = 0; s < ids.length; s += 20) {
    const part = ids.slice(s, s + 20);
    const tag = m.replace(/[^a-z0-9]/gi, '_') + '_' + s;
    fs.writeFileSync(D(dir + '/' + tag + '.txt'), part.map((k, i) => `# kb ${i}\n` + kbs[k].join('\n') + '\n').join(''));
    jobs.push({ m, ids: part, tag });
  }
}
console.log('retry jobs:', jobs.length, 'pairs:', jobs.reduce((a, j) => a + j.ids.length, 0));
const out = D(env.OUT || 'java-results-retry.jsonl');
fs.writeFileSync(out, '');
let next = 0, running = 0;
function launch() {
  while (running < parallel && next < jobs.length) {
    const job = jobs[next++];
    running++;
    const res = D(dir + '/' + job.tag + '.jsonl');
    if (fs.existsSync(res)) fs.unlinkSync(res);
    const p = spawn('node', [path.join(__dirname, 'run-java.cjs'), D(dir + '/' + job.tag + '.txt'), res, job.m, timeout], { stdio: 'ignore' });
    p.on('exit', () => {
      const lines = fs.existsSync(res) ? load(res) : [];
      fs.appendFileSync(out, lines.map(o => { o.kb = job.ids[o.kb]; o.retry = true; return JSON.stringify(o); }).join('\n') + (lines.length ? '\n' : ''));
      running--;
      if (next >= jobs.length && running === 0) console.log('RETRY DONE');
      launch();
    });
  }
}
launch();
