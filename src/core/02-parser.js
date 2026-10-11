// ---------------------------------------------------------------------------
// Parser for TweetyProject's propositional syntax (port of PlParser).
//
//   FORMULA ::= PROP | "(" FORMULA ")" | FORMULA "&&" FORMULA | FORMULA "||" FORMULA
//             | FORMULA "^^" FORMULA | FORMULA "=>" FORMULA | FORMULA "<=>" FORMULA
//             | "!" FORMULA | "+" | "-"
//
// Binding strength (weakest first): <=>, =>, ^^, ||, &&, !.  &&, || and ^^ are
// n-ary (flat lists), parenthesised sub-formulas stay nested, as in Tweety.
// The logical symbols ¬ ∧ ∨ ⊕ → ↔ ⊤ ⊥ are accepted as alternatives to
// ! && || ^^ => <=> + -.
// Differences to Tweety's parser: chained => and <=> are right-associative
// (Tweety silently concatenates atom names), "!!a" is accepted, and lines
// starting with '%' or '#' are comments. As in Tweety, blanks inside a name
// are ignored ("a b" is the atom "ab"); proposition names may contain any
// character except | & ! ( ) < > = ^ and whitespace.
// ---------------------------------------------------------------------------

class ParseError extends Error {
  constructor(msg, pos) { super(msg); this.name = 'ParseError'; this.pos = pos; }
}

const SPECIAL = new Set(['|', '&', '!', '(', ')', '<', '>', '=', '^', '¬', '∧', '∨', '⊕', '→', '⇒', '↔', '⇔', '⊤', '⊥']);
// logical symbols accepted as alternatives to TweetyProject's ASCII operators
const SYMBOL_TOKENS = { '¬': '!', '∧': '&&', '∨': '||', '⊕': '^^', '→': '=>', '⇒': '=>', '↔': '<=>', '⇔': '<=>' };

function tokenize(s) {
  const toks = [];
  let i = 0;
  const n = s.length;
  while (i < n) {
    const c = s[i];
    if (c === ' ' || c === '\t') { i++; continue; }
    if (c === '(' || c === ')' || c === '!') { toks.push({ v: c, pos: i }); i++; continue; }
    if (SYMBOL_TOKENS[c]) { toks.push({ v: SYMBOL_TOKENS[c], pos: i }); i++; continue; }
    if (c === '⊤' || c === '⊥') { toks.push({ v: c === '⊤' ? '+' : '-', pos: i, name: true }); i++; continue; }
    if (c === '&' || c === '|' || c === '^') {
      if (s[i + 1] === c) { toks.push({ v: c + c, pos: i }); i += 2; continue; }
      throw new ParseError("Unexpected '" + c + "' (did you mean '" + c + c + "'?)", i);
    }
    if (c === '=') {
      if (s[i + 1] === '>') { toks.push({ v: '=>', pos: i }); i += 2; continue; }
      throw new ParseError("Unexpected '=' (did you mean '=>'?)", i);
    }
    if (c === '<') {
      if (s[i + 1] === '=' && s[i + 2] === '>') { toks.push({ v: '<=>', pos: i }); i += 3; continue; }
      throw new ParseError("Unexpected '<' (did you mean '<=>'?)", i);
    }
    if (c === '>') throw new ParseError("Unexpected '>'", i);
    // a name: maximal run of non-special characters (blanks are skipped)
    let name = '';
    const start = i;
    while (i < n && !SPECIAL.has(s[i])) {
      if (s[i] !== ' ' && s[i] !== '\t') name += s[i];
      i++;
    }
    if (/\s/.test(name)) throw new ParseError('Invalid whitespace in name', start);
    toks.push({ v: name, pos: start, name: true });
  }
  return toks;
}

function parseFormula(text) {
  const toks = tokenize(text);
  let p = 0;
  const peek = () => toks[p] ? toks[p].v : null;
  const posOf = () => toks[p] ? toks[p].pos : text.length;
  function expect(v) {
    if (peek() !== v) throw new ParseError("Expected '" + v + "'" + (peek() === null ? ' but reached end of formula' : " but found '" + peek() + "'"), posOf());
    p++;
  }
  function parseEquiv() {
    const left = parseImpl();
    if (peek() === '<=>') { p++; return Equiv(left, parseEquiv()); }
    return left;
  }
  function parseImpl() {
    const left = parseXor();
    if (peek() === '=>') { p++; return Impl(left, parseImpl()); }
    return left;
  }
  function parseNary(op, type, next) {
    const first = next();
    if (peek() !== op) return first;
    const list = [first];
    while (peek() === op) { p++; list.push(next()); }
    return { t: type, k: list };
  }
  function parseXor() { return parseNary('^^', 'xor', parseOr); }
  function parseOr() { return parseNary('||', 'or', parseAnd); }
  function parseAnd() { return parseNary('&&', 'and', parseUnary); }
  function parseUnary() {
    const v = peek();
    if (v === '!') { p++; return Not(parseUnary()); }
    if (v === '(') {
      p++;
      if (peek() === ')') throw new ParseError('Empty parentheses', posOf());
      const f = parseEquiv();
      expect(')');
      return f;
    }
    if (v === null) throw new ParseError('Unexpected end of formula', posOf());
    const tok = toks[p];
    if (!tok.name) throw new ParseError("Unexpected '" + v + "'", tok.pos);
    p++;
    if (v === '+') return TOP;
    if (v === '-') return BOT;
    return Prop(v);
  }
  if (toks.length === 0) throw new ParseError('Empty formula', 0);
  const f = parseEquiv();
  if (p < toks.length) throw new ParseError("Unexpected '" + peek() + "'", posOf());
  return f;
}

// A knowledge base: a set of formulas (syntactic duplicates are merged, as
// in Tweety's PlBeliefSet) together with source information.
class KnowledgeBase {
  constructor(formulas, texts, lines) {
    this.formulas = formulas;
    this.texts = texts || formulas.map(f => toPretty(f));
    this.lines = lines || formulas.map((_, i) => i + 1);
    const set = new Set();
    for (const f of formulas) for (const a of atoms(f)) set.add(a);
    this.atoms = Array.from(set).sort(cmpNames);
    this.atomIndex = new Map(this.atoms.map((a, i) => [a, i]));
  }
  get size() { return this.formulas.length; }
  key() {
    if (this._key === undefined) this._key = this.formulas.map(key).join('\n');
    return this._key;
  }
  subset(indices) {
    return new KnowledgeBase(indices.map(i => this.formulas[i]), indices.map(i => this.texts[i]), indices.map(i => this.lines[i]));
  }
  static fromFormulas(formulas) {
    const seen = new Set(), fs = [];
    for (const f of formulas) { const k = key(f); if (!seen.has(k)) { seen.add(k); fs.push(f); } }
    return new KnowledgeBase(fs);
  }
  toTweetyString() { return this.formulas.map(toTweetyString).join('\n'); }
}

// Parse a knowledge base given as text, one formula per line.
// Returns {kb, errors:[{line, col, message, text}], duplicates:[{line, firstLine}]}
function parseKB(text) {
  const lines = text.split(/\r\n|\r|\n/);
  const formulas = [], texts = [], lineNos = [], errors = [], duplicates = [];
  const seen = new Map();
  lines.forEach((raw, i) => {
    const t = raw.trim();
    if (t === '' || t[0] === '%' || t[0] === '#') return;
    try {
      const f = parseFormula(t);
      const k = key(f);
      if (seen.has(k)) { duplicates.push({ line: i + 1, firstLine: seen.get(k) }); return; }
      seen.set(k, i + 1);
      formulas.push(f); texts.push(t); lineNos.push(i + 1);
    } catch (e) {
      if (e instanceof ParseError) {
        const lead = raw.length - raw.trimStart().length;
        errors.push({ line: i + 1, col: (e.pos || 0) + lead + 1, message: e.message, text: t });
      } else throw e;
    }
  });
  return { kb: new KnowledgeBase(formulas, texts, lineNos), errors, duplicates };
}

// DIMACS CNF -> knowledge base with one clause per formula.
function parseDimacs(text) {
  const formulas = [];
  let cur = [];
  for (const raw of text.split(/\r\n|\r|\n/)) {
    const line = raw.trim();
    if (line === '' || line[0] === 'c' || line[0] === 'p' || line[0] === '%') continue;
    for (const tok of line.split(/\s+/)) {
      const v = parseInt(tok, 10);
      if (isNaN(v)) throw new ParseError('Invalid DIMACS token ' + tok, 0);
      if (v === 0) { formulas.push(cur.length === 0 ? BOT : (cur.length === 1 ? cur[0] : Or(cur))); cur = []; }
      else { const a = Prop('x' + Math.abs(v)); cur.push(v > 0 ? a : Not(a)); }
    }
  }
  if (cur.length) formulas.push(cur.length === 1 ? cur[0] : Or(cur));
  return KnowledgeBase.fromFormulas(formulas);
}

IM.ParseError = ParseError;
IM.parseFormula = parseFormula;
IM.parseKB = parseKB;
IM.parseDimacs = parseDimacs;
IM.KnowledgeBase = KnowledgeBase;
