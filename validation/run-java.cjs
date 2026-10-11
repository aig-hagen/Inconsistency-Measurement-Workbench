// Drives the Java harness over all KBs and measures, restarting the JVM after
// timeouts (naive TweetyProject algorithms cannot be interrupted).
// Usage: node run-java.cjs <kbFile> <outFile> <measureIdsCsv> [timeoutMs]
const fs = require('fs');
const path = require('path');
const { spawnSync } = require('child_process');

const [kbFile, outFile, measuresCsv, timeoutArg, offsetArg] = process.argv.slice(2);
const offset = parseInt(offsetArg || '0', 10);
const timeout = timeoutArg || '10000';
const measures = measuresCsv.split(',');
const cp = fs.readFileSync(process.env.CP_FILE || path.join(__dirname, 'java', 'build', 'classpath.txt'), 'utf8').trim();
const nKbs = (fs.readFileSync(kbFile, 'utf8').match(/^# kb/gm) || []).length;

// resume support
let startKb = 0, startM = 0;
if (fs.existsSync(outFile)) {
  const lines = fs.readFileSync(outFile, 'utf8').trim().split('\n').filter(Boolean);
  if (lines.length) {
    const last = JSON.parse(lines[lines.length - 1]);
    startKb = last.kb - offset; startM = measures.indexOf(last.m) + 1;
    if (startM >= measures.length) { startKb++; startM = 0; }
  }
}
const t0 = Date.now();
while (startKb < nKbs) {
  const r = spawnSync('java', ['-Xss64m', '-cp', cp, 'ImHarness', 'measures', kbFile, measuresCsv, String(startKb), String(startM), timeout],
    { encoding: 'utf8', maxBuffer: 1 << 30 });
  const lines = (r.stdout || '').trim().split('\n').filter(l => l.startsWith('{'));
  if (lines.length) fs.appendFileSync(outFile, lines.map(l => { const o = JSON.parse(l); o.kb += offset; return JSON.stringify(o); }).join('\n') + '\n');
  if (r.status === 0) break;
  if (!lines.length) { console.error('harness failed without output:', r.stderr); process.exit(1); }
  const last = JSON.parse(lines[lines.length - 1]);
  startKb = last.kb; startM = measures.indexOf(last.m) + 1;
  if (startM >= measures.length) { startKb++; startM = 0; }
  process.stdout.write(`restart at kb ${startKb} measure ${startM} (${Math.round((Date.now() - t0) / 1000)}s)\n`);
}
console.log('done in', Math.round((Date.now() - t0) / 1000), 's');
