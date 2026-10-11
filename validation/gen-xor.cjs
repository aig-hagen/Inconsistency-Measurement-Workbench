// Generates data/kbs-xor.txt: 300 random knowledge bases in which exclusive or
// also occurs at the top level and over complex operands. TweetyProject's SAT
// interface failed on these before ExclusiveDisjunction.isClause()/toCnf() were
// fixed, so gen.cjs restricts exclusive or to literals; this set validates the
// fixed sources (validation/run-fixed.sh).
const fs = require('fs');
const path = require('path');
const IM = require('../dist/im-core.js');
const { Prop, Not, And, Or, Xor, Impl, Equiv, TOP, BOT } = IM.F;

function genFormula(rng, atoms, depth) {
  const literal = () => {
    if (rng() < 0.05) return rng() < 0.5 ? TOP : BOT;
    const a = Prop(rng.pick(atoms));
    return rng() < 0.4 ? Not(a) : a;
  };
  if (depth === 0 || rng() < 0.15) return literal();
  const r = rng();
  const sub = () => genFormula(rng, atoms, depth - 1);
  if (r < 0.12) return Not(sub());
  if (r < 0.32) return And([sub(), sub()]);
  if (r < 0.52) return Or([sub(), sub()]);
  if (r < 0.62) return Impl(sub(), sub());
  if (r < 0.70) return Equiv(sub(), sub());
  return rng() < 0.85 ? Xor([sub(), sub()]) : Xor([sub(), sub(), sub()]);
}

let out = '';
for (let i = 0; i < 300; i++) {
  const rng = IM.makeRng(700001 * (i + 1));
  const atoms = ['a', 'b', 'c', 'd'].slice(0, rng.int(1, 4));
  const nForm = rng.int(1, 6);
  const seen = new Set(), fs_ = [];
  for (let tries = 0; fs_.length < nForm && tries < 50; tries++) {
    const f = genFormula(rng, atoms, rng.pick([1, 1, 2, 2, 3]));
    const s = IM.toTweetyString(f);
    const k = IM.key(IM.parseFormula(s));
    if (seen.has(k)) continue;
    seen.add(k);
    fs_.push(s);
  }
  if (!fs_.some(s => s.includes('^^'))) fs_.push(IM.toTweetyString(Xor([genFormula(rng, atoms, 1), genFormula(rng, atoms, 1)])));
  out += `# kb ${i}\n` + fs_.join('\n') + '\n';
}
fs.writeFileSync(path.join(__dirname, 'data', 'kbs-xor.txt'), out);
console.log('wrote data/kbs-xor.txt');
