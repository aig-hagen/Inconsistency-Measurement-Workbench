// Inconsistency Measurement Workbench - user interface
(function () {
  'use strict';
  const IMC = window.IM;
  const $ = (s, r) => (r || document).querySelector(s);
  const $$ = (s, r) => Array.from((r || document).querySelectorAll(s));

  // ---------------------------------------------------------------- helpers
  function el(tag, attrs, ...kids) {
    const e = document.createElement(tag);
    if (attrs) for (const [k, v] of Object.entries(attrs)) {
      if (v == null || v === false) continue;
      if (k === 'class') e.className = v;
      else if (k === 'text') e.textContent = v;
      else if (k === 'html') e.innerHTML = v;
      else if (k.startsWith('on')) e.addEventListener(k.slice(2), v);
      // native tooltips cannot use the formula font; texts with φ go to the page tooltip
      else if (k === 'title' && String(v).indexOf('φ') >= 0) e.setAttribute('data-tip', esc(v));
      else if (v === true) e.setAttribute(k, '');
      else e.setAttribute(k, v);
    }
    for (const k of kids.flat()) if (k != null && k !== false) e.append(k instanceof Node ? k : document.createTextNode(String(k)));
    return e;
  }
  const esc = (s) => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
  const store = {
    get(k, d) { try { const v = localStorage.getItem('imw:' + k); return v === null ? d : JSON.parse(v); } catch (e) { return d; } },
    set(k, v) { try { localStorage.setItem('imw:' + k, JSON.stringify(v)); } catch (e) { /* storage unavailable */ } },
  };
  const deser = (v) => IMC.deserializeValue(v);
  function fmtNum(v, digits) {
    v = deser(v);
    if (v === null || v === undefined) return '–';
    if (v === Infinity) return '∞';
    if (v === -Infinity) return '−∞';
    if (Number.isNaN(v)) return 'NaN';
    if (Number.isInteger(v)) return String(v);
    const d = digits == null ? 4 : digits;
    const s = (+v.toFixed(d)).toString();
    return s === '-0' ? '0' : s;
  }
  function symbolNode(sym) {
    const m = /^([^_^]+)(?:_([^^]+))?(?:\^(.+))?$/.exec(sym) || [sym, sym];
    const span = el('span', { class: 'm-symbol', 'aria-label': sym }, m[1]);
    // both indices: stacked as in TeX (I_{MI}^{C}), superscript above subscript
    if (m[2] && m[3]) span.append(el('span', { class: 'scripts', 'aria-hidden': 'true' }, el('span', { class: 's-sup' }, m[3]), el('span', { class: 's-sub' }, m[2])));
    else if (m[2]) span.append(el('sub', null, m[2]));
    else if (m[3]) span.append(el('sup', null, m[3]));
    return span;
  }
  function fmtFull(v) { v = deser(v); if (typeof v !== 'number' || !isFinite(v)) return fmtNum(v); return String(v); }
  function fmtMs(ms) { if (ms == null) return ''; if (ms < 1) return '<1 ms'; if (ms < 1000) return ms + ' ms'; return (ms / 1000).toFixed(ms < 10000 ? 2 : 1) + ' s'; }
  function truncate(s, n) { return s.length > n ? s.slice(0, n - 1) + '…' : s; }
  let toastTimer = null;
  function toast(msg) {
    const t = $('#toast');
    t.textContent = msg; t.hidden = false;
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => { t.hidden = true; }, 2600);
  }
  async function copyText(text, what) {
    try { await navigator.clipboard.writeText(text); toast((what || 'Text') + ' copied to the clipboard'); }
    catch (e) {
      const ta = el('textarea', { style: 'position:fixed;left:-9999px;top:0' }); ta.value = text; document.body.append(ta); ta.select();
      let ok = false; try { ok = document.execCommand('copy'); } catch (e2) { ok = false; }
      ta.remove();
      toast(ok ? (what || 'Text') + ' copied to the clipboard' : 'Copying is blocked here; select the text manually.');
    }
  }
  function download(name, text, mime) {
    const a = el('a', { href: URL.createObjectURL(new Blob([text], { type: mime || 'text/plain' })), download: name });
    document.body.append(a); a.click(); setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 500);
  }
  const cssVar = (name) => getComputedStyle(document.documentElement).getPropertyValue(name).trim();
  const tip = $('#tooltip');
  function showTip(evt, html) {
    tip.innerHTML = html; tip.hidden = false;
    const pad = 14, w = tip.offsetWidth, h = tip.offsetHeight;
    let x = evt.clientX + pad, y = evt.clientY + pad;
    if (x + w > window.innerWidth - 8) x = evt.clientX - w - pad;
    if (y + h > window.innerHeight - 8) y = evt.clientY - h - pad;
    tip.style.left = Math.max(4, x) + 'px'; tip.style.top = Math.max(4, y) + 'px';
  }
  function hideTip() { tip.hidden = true; }
  function bindTips(root) {
    root.addEventListener('mousemove', (e) => { const t = e.target.closest('[data-tip]'); if (t) showTip(e, t.getAttribute('data-tip')); else hideTip(); });
    root.addEventListener('mouseleave', hideTip);
  }

  // ---------------------------------------------------------------- one glyph for φ
  // Fonts draw U+03C6 differently (loopy or straight), and the UI font has no
  // Greek letters, so every φ in the page is rendered with the formula font.
  const SVG_NS = 'http://www.w3.org/2000/svg';
  const SKIP_PHI = new Set(['TEXTAREA', 'SCRIPT', 'STYLE', 'OPTION', 'TITLE', 'INPUT']);
  function wrapPhi(node) {
    if (node.nodeType === 3) {
      const p = node.parentNode;
      if (!p || node.nodeValue.indexOf('φ') < 0 || SKIP_PHI.has(p.nodeName) || (p.classList && p.classList.contains('phi'))) return;
      const isSvg = p.namespaceURI === SVG_NS;
      const frag = document.createDocumentFragment();
      for (const part of node.nodeValue.split(/(φ)/)) {
        if (part === 'φ') {
          const span = isSvg ? document.createElementNS(SVG_NS, 'tspan') : document.createElement('span');
          span.setAttribute('class', 'phi');
          span.textContent = 'φ';
          frag.append(span);
        } else if (part) frag.append(document.createTextNode(part));
      }
      p.replaceChild(frag, node);
    } else if (node.nodeType === 1 && !SKIP_PHI.has(node.nodeName)) {
      for (const c of Array.from(node.childNodes)) wrapPhi(c);
    }
  }
  new MutationObserver((muts) => {
    for (const m of muts) {
      if (m.type === 'characterData') wrapPhi(m.target);
      else for (const n of m.addedNodes) wrapPhi(n);
    }
  }).observe(document.body, { childList: true, subtree: true, characterData: true });
  wrapPhi(document.body);
  bindTips(document.body);

  // ---------------------------------------------------------------- notation (TweetyProject syntax vs. logical symbols)
  const BOUNDARY = '\\s()&|^!=<>¬∧∨⊕→↔⇒⇔';
  const CONST_RE = new RegExp('(?<=^|[' + BOUNDARY + '])([+-])(?=$|[' + BOUNDARY + '])', 'g');
  const SYM_CONST_RE = /[⊤⊥]/g;
  function lineToSymbols(line) {
    if (/^\s*[%#]/.test(line)) return line;
    return line.replace(CONST_RE, (m) => (m === '+' ? '⊤' : '⊥'))
      .replace(/<=>/g, '↔').replace(/=>/g, '→').replace(/&&/g, '∧').replace(/\|\|/g, '∨').replace(/\^\^/g, '⊕').replace(/!/g, '¬');
  }
  function lineToTweety(line) {
    if (/^\s*[%#]/.test(line)) return line;
    return line.replace(SYM_CONST_RE, (m) => (m === '⊤' ? '+' : '-'))
      .replace(/[↔⇔]/g, '<=>').replace(/[→⇒]/g, '=>').replace(/∧/g, '&&').replace(/∨/g, '||').replace(/⊕/g, '^^').replace(/¬/g, '!');
  }
  const toSymbols = (text) => text.split('\n').map(lineToSymbols).join('\n');
  const toTweety = (text) => text.split('\n').map(lineToTweety).join('\n');
  const inNotation = (asciiText) => (S.notation === 'symbols' ? toSymbols(asciiText) : asciiText);

  // ---------------------------------------------------------------- worker runner
  function workerMain() {
    self.onmessage = function (e) {
      const d = e.data;
      IM.Deadline.set(d.timeout);
      try {
        const result = IM.handleRequest(d.req, function (p) { self.postMessage({ id: d.id, progress: p }); });
        self.postMessage({ id: d.id, result: result });
      } catch (err) {
        self.postMessage({ id: d.id, error: { name: (err && err.name) || 'Error', message: String((err && err.message) || err) } });
      } finally { IM.Deadline.clear(); }
    };
  }
  const workerUrl = (() => {
    try {
      const src = imCore.toString() + '\nself.IM = imCore();\n(' + workerMain.toString() + ')();\n';
      return URL.createObjectURL(new Blob([src], { type: 'text/javascript' }));
    } catch (e) { return null; }
  })();
  class RunError extends Error { constructor(name, msg) { super(msg); this.name = name; } }
  class Runner {
    constructor() { this.queue = []; this.pending = null; this.seq = 0; this.create(); }
    create() {
      this.w = null;
      if (!workerUrl) return;
      try {
        this.w = new Worker(workerUrl);
        this.w.onmessage = (e) => this.onMessage(e.data);
        this.w.onerror = (e) => { e.preventDefault(); if (this.pending) this.finish(null, new RunError('Error', e.message || 'Worker error')); };
      } catch (e) { this.w = null; }
    }
    call(req, opts) {
      opts = opts || {};
      return new Promise((resolve, reject) => {
        this.queue.push({ id: ++this.seq, req, timeout: opts.timeout || 60000, onProgress: opts.onProgress, resolve, reject });
        this.pump();
      });
    }
    pump() {
      if (this.pending || !this.queue.length) return;
      const job = this.pending = this.queue.shift();
      if (!this.w) {   // fallback: run on the main thread
        setTimeout(() => {
          IMC.Deadline.set(job.timeout);
          let res, err;
          try { res = IMC.handleRequest(job.req, job.onProgress); } catch (e) { err = new RunError(e.name, e.message); } finally { IMC.Deadline.clear(); }
          this.finish(res, err);
        }, 20);
        return;
      }
      job.timer = setTimeout(() => {
        this.w.terminate(); this.create();
        this.finish(null, new RunError('TimeoutError', 'Computation timed out'));
      }, job.timeout + 2500);
      this.w.postMessage({ id: job.id, req: job.req, timeout: job.timeout });
    }
    onMessage(d) {
      const job = this.pending;
      if (!job || d.id !== job.id) return;
      if ('progress' in d) { if (job.onProgress) job.onProgress(d.progress); return; }
      if (d.error) this.finish(null, new RunError(d.error.name, d.error.message));
      else this.finish(d.result, null);
    }
    finish(res, err) {
      const job = this.pending;
      if (!job) return;
      clearTimeout(job.timer);
      this.pending = null;
      if (err) job.reject(err); else job.resolve(res);
      this.pump();
    }
    cancelAll() {
      const jobs = (this.pending ? [this.pending] : []).concat(this.queue);
      this.queue = [];
      if (this.pending) { clearTimeout(this.pending.timer); this.pending = null; }
      if (this.w) { this.w.terminate(); this.create(); }
      for (const j of jobs) j.reject(new RunError('CancelError', 'Cancelled'));
    }
  }
  const main = new Runner();   // user-triggered computations
  const bg = new Runner();     // background analysis of the knowledge base

  // ---------------------------------------------------------------- measures and measure instances
  const INFO = IMC.measureInfo();
  const BY_ID = new Map(INFO.map(m => [m.id, m]));
  const FAMILY_ORDER = ['Basic', 'MUS-based', 'MCS-based', 'Semantic', 'Distance-based', 'Proof-based', 'Syntactic', 'Fuzzy'];
  const ORDERED = INFO.slice().sort((a, b) => FAMILY_ORDER.indexOf(a.family) - FAMILY_ORDER.indexOf(b.family));
  const GITHUB = 'https://github.com/TweetyProjectTeam/TweetyProject/blob/main/';
  const PL_ANALYSIS = 'org-tweetyproject-logics-pl/src/main/java/org/tweetyproject/logics/pl/analysis/';
  const COMMONS_ANALYSIS = 'org-tweetyproject-logics-commons/src/main/java/org/tweetyproject/logics/commons/analysis/';
  const JAVA_PATHS = {
    ContensionInconsistencyMeasure: PL_ANALYSIS, PmInconsistencyMeasure: PL_ANALYSIS, MusVarInconsistencyMeasure: PL_ANALYSIS,
    FbInconsistencyMeasure: PL_ANALYSIS, FuzzyInconsistencyMeasure: PL_ANALYSIS, IcebergInconsistencyMeasure: PL_ANALYSIS,
    PrimeImplicantBasedInconsistencyMeasure: PL_ANALYSIS, DalalDistance: PL_ANALYSIS,
    FracAggrFunction: 'org-tweetyproject-math/src/main/java/org/tweetyproject/math/func/',
  };
  function javaLink(className) {
    const path = JAVA_PATHS[className] || COMMONS_ANALYSIS;
    return el('a', { href: GITHUB + path + className + '.java', target: '_blank', rel: 'noopener', class: 'mono' }, className);
  }
  // "DSumInconsistencyMeasure (DalalDistance)" -> linked class names
  function javaRef(java) {
    const m = /^(\w+)(?:\s*\((.*)\))?$/.exec(java);
    if (!m) return el('code', null, java);
    const extra = m[2] ? (JAVA_PATHS[m[2]] ? [' with ', javaLink(m[2])] : [' (' + m[2] + ')']) : [];
    return el('span', null, javaLink(m[1]), ...extra);
  }

  // an instance is one row of the measure table: a measure with a parameter setting
  function defaultInstances() {
    const oldParams = store.get('params', {});
    return ORDERED.map(m => ({ key: m.id, id: m.id, params: Object.assign(IMC.defaultParams(IMC.MEASURE_BY_ID.get(m.id)), oldParams[m.id] || {}) }));
  }
  function loadInstances() {
    const saved = store.get('instances', null);
    if (!Array.isArray(saved)) return defaultInstances();
    const list = saved.filter(x => x && BY_ID.has(x.id) && typeof x.key === 'string');
    for (const m of ORDERED) if (!list.some(x => x.key === m.id)) list.push({ key: m.id, id: m.id, params: IMC.defaultParams(IMC.MEASURE_BY_ID.get(m.id)) });
    for (const x of list) x.params = Object.assign(IMC.defaultParams(IMC.MEASURE_BY_ID.get(x.id)), x.params || {});
    return list;
  }

  const S = {
    text: '',
    parsed: null,
    notation: store.get('notation', 'tweety') === 'symbols' ? 'symbols' : 'tweety',
    instances: loadInstances(),
    selected: null,
    results: {},
    running: false,
    cancelled: false,
    lastRun: null,
    structure: null, structureKey: null, structureErr: null,
    tab: store.get('tab', 'measures'),
  };
  S.selected = new Set(store.get('selected', S.instances.map(x => x.key)));
  const instByKey = (k) => S.instances.find(x => x.key === k);
  function orderedInstances() {
    const out = [];
    for (const m of ORDERED) for (const x of S.instances) if (x.id === m.id) out.push(x);
    return out;
  }
  function paramLabel(inst) {
    const m = BY_ID.get(inst.id);
    if (!m.params.length) return '';
    return m.params.map(p => { const o = p.options.find(x => x[0] === String(inst.params[p.id])); return o ? o[1] : ''; }).join(', ');
  }
  function instLabel(inst) {
    const pl = paramLabel(inst);
    return BY_ID.get(inst.id).label + (pl ? ' (' + pl + ')' : '');
  }
  const saveInstances = () => store.set('instances', S.instances);
  const saveSelected = () => store.set('selected', Array.from(S.selected));
  const kbKey = () => (S.parsed ? S.parsed.kb.key() : '');
  const paramKey = (inst) => JSON.stringify(inst.params || {});
  const selectedInstances = () => orderedInstances().filter(x => S.selected.has(x.key));
  let copyCounter = Math.max(1, ...S.instances.map(x => parseInt((x.key.split('#')[1] || '0'), 10) || 0));

  // ---------------------------------------------------------------- theme
  function applyTheme(t) {
    if (t === 'system') document.documentElement.removeAttribute('data-theme'); else document.documentElement.setAttribute('data-theme', t);
    for (const b of $$('.theme-toggle button')) b.setAttribute('aria-pressed', String(b.dataset.themeChoice === t));
    store.set('theme', t);
    rerenderCharts();
  }
  for (const b of $$('.theme-toggle button')) b.addEventListener('click', () => applyTheme(b.dataset.themeChoice));

  // ---------------------------------------------------------------- editor
  const input = $('#kb-input');
  const gutter = $('#gutter');
  // set the editor text from TweetyProject syntax (converted to the current notation)
  function setText(asciiText, opts) {
    input.value = inNotation(asciiText);
    onTextChange(opts);
  }
  function renderGutter() {
    const lines = input.value.split(/\r\n|\r|\n/);
    const p = S.parsed;
    const errAt = new Map((p ? p.errors : []).map(e => [e.line, e]));
    const dupAt = new Map((p ? p.duplicates : []).map(d => [d.line, d]));
    const fAt = new Map();
    if (p) p.kb.lines.forEach((ln, i) => fAt.set(ln, i));
    const frag = document.createDocumentFragment();
    lines.forEach((_, i) => {
      const ln = i + 1;
      let d;
      if (errAt.has(ln)) d = el('div', { class: 'g-err', title: 'Line ' + ln + ': ' + errAt.get(ln).message }, 'error');
      else if (dupAt.has(ln)) d = el('div', { class: 'g-dup', title: 'Duplicate of line ' + dupAt.get(ln).firstLine }, 'dup');
      else if (fAt.has(ln)) d = el('div', { class: 'g-f', 'data-tip': esc('Formula φ' + (fAt.get(ln) + 1) + ' (line ' + ln + ')') }, 'φ' + (fAt.get(ln) + 1));
      else d = el('div', { class: 'g-c' }, ' ');
      frag.append(d);
    });
    gutter.replaceChildren(frag);
    gutter.scrollTop = input.scrollTop;
  }
  input.addEventListener('scroll', () => { gutter.scrollTop = input.scrollTop; });
  let changeTimer = null, structTimer = null;
  input.addEventListener('input', () => {
    clearTimeout(changeTimer);
    changeTimer = setTimeout(() => onTextChange(), 180);
  });
  input.addEventListener('keydown', (e) => {
    if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') { e.preventDefault(); onTextChange(); computeSelected(); }
  });

  function onTextChange(opts) {
    opts = opts || {};
    S.text = input.value;
    store.set('text', S.text);
    S.parsed = IMC.parseKB(S.text);
    renderGutter();
    renderErrors();
    renderStatus();
    renderMeasureValues();
    clearTimeout(structTimer);
    structTimer = setTimeout(requestStructure, opts.immediate ? 0 : 350);
    invalidateViews();
  }
  function renderErrors() {
    const ul = $('#kb-errors');
    ul.replaceChildren();
    const p = S.parsed;
    for (const e of p.errors.slice(0, 6)) ul.append(el('li', null, 'Line ' + e.line + ', column ' + e.col + ': ' + e.message));
    if (p.errors.length > 6) ul.append(el('li', null, (p.errors.length - 6) + ' more syntax errors'));
    if (p.duplicates.length) ul.append(el('li', { class: 'dup' }, (p.duplicates.length === 1 ? 'Line ' + p.duplicates[0].line + ' repeats' : p.duplicates.length + ' lines repeat') + ' an earlier formula and ' + (p.duplicates.length === 1 ? 'is' : 'are') + ' ignored (a knowledge base is a set).'));
  }
  function renderStatus() {
    const box = $('#kb-status');
    const p = S.parsed;
    const n = p.kb.size, a = p.kb.atoms.length;
    const parts = [el('span', null, n + (n === 1 ? ' formula' : ' formulas')), el('span', { class: 'sep' }, '·'), el('span', null, a + (a === 1 ? ' atom' : ' atoms'))];
    if (p.errors.length) parts.push(el('span', { class: 'sep' }, '·'), el('span', { class: 'pill bad' }, el('span', { class: 'dot' }), 'Syntax errors'));
    else if (S.structure && S.structureKey === kbKey()) {
      const st = S.structure;
      parts.push(el('span', { class: 'sep' }, '·'));
      parts.push(st.consistent ? el('span', { class: 'pill good' }, el('span', { class: 'dot' }), 'Consistent')
        : el('span', { class: 'pill bad' }, el('span', { class: 'dot' }), 'Inconsistent'));
      if (!st.consistent) parts.push(el('span', null, st.muses.length + ' minimal inconsistent subset' + (st.muses.length === 1 ? '' : 's')));
    } else if (S.structureErr && S.structureKey === kbKey()) {
      parts.push(el('span', { class: 'sep' }, '·'), el('span', { class: 'pill warn' }, 'Analysis: ' + S.structureErr));
    } else if (n > 0) parts.push(el('span', { class: 'sep' }, '·'), el('span', { class: 'pill neutral' }, el('span', { class: 'spinner' }), 'Analysing'));
    box.replaceChildren(...parts);
  }
  async function requestStructure() {
    const key = kbKey();
    if (S.parsed.errors.length) return;
    try {
      bg.cancelAll();
      const r = await bg.call({ op: 'structure', text: S.text }, { timeout: 15000 });
      if (key !== kbKey()) return;
      S.structure = r; S.structureKey = key; S.structureErr = null;
    } catch (e) {
      if (e.name === 'CancelError' || key !== kbKey()) return;
      S.structure = null; S.structureKey = key;
      S.structureErr = e.name === 'TimeoutError' ? 'timed out (too many conflicts)' : e.message;
    }
    renderStatus();
    if (S.tab === 'structure') renderStructure();
  }

  // notation switch and symbol buttons
  function applyNotation(n, convert) {
    S.notation = n;
    store.set('notation', n);
    for (const r of $$('input[name=notation]')) r.checked = r.value === n;
    $('#symbol-bar').hidden = n !== 'symbols';
    if (convert) {
      const pos = input.selectionStart;
      input.value = n === 'symbols' ? toSymbols(input.value) : toTweety(input.value);
      onTextChange({ immediate: true });
      try { input.setSelectionRange(Math.min(pos, input.value.length), Math.min(pos, input.value.length)); } catch (e) { /* ignore */ }
    }
  }
  for (const r of $$('input[name=notation]')) r.addEventListener('change', () => { if (r.checked) applyNotation(r.value, true); });
  $('#symbol-bar').addEventListener('click', (e) => {
    const b = e.target.closest('button[data-sym]');
    if (!b) return;
    const sym = b.dataset.sym;
    const binary = '∧∨⊕→↔'.includes(sym);
    const start = input.selectionStart, end = input.selectionEnd;
    const before = input.value.slice(0, start);
    let ins = sym;
    if (binary) ins = (before.length && !/\s$/.test(before) ? ' ' : '') + sym + ' ';
    input.focus();
    let done = false;
    try { done = document.execCommand('insertText', false, ins); } catch (err) { done = false; }
    if (!done) { input.setRangeText(ins, start, end, 'end'); }
    input.dispatchEvent(new Event('input'));
  });

  // examples, random, upload, download, clear
  const exSel = $('#example-select');
  (window.IM_EXAMPLES || []).forEach((ex, i) => exSel.append(el('option', { value: String(i) }, ex.name)));
  exSel.addEventListener('change', () => {
    const ex = window.IM_EXAMPLES[+exSel.value];
    exSel.value = '';
    if (!ex) return;
    setText(ex.text, { immediate: true });
    toast('Loaded “' + ex.name + '”');
    computeSelected();
  });
  function openGenerator(focus) {
    const p = $('#random-panel');
    p.hidden = false;
    $('#btn-random-toggle').setAttribute('aria-expanded', 'true');
    if (focus) { p.scrollIntoView({ block: 'nearest', behavior: 'smooth' }); $('#rnd-atoms').focus({ preventScroll: true }); }
  }
  $('#btn-random-toggle').addEventListener('click', () => {
    const p = $('#random-panel');
    if (p.hidden) openGenerator(false);
    else { p.hidden = true; $('#btn-random-toggle').setAttribute('aria-expanded', 'false'); }
  });
  const RND_FIELDS = { atoms: 'rnd-atoms', minFormulas: 'rnd-min', maxFormulas: 'rnd-max', maxDepth: 'rnd-depth', clauseLength: 'rnd-clause', seed: 'rnd-seed' };
  function samplerSettings() {
    const o = {};
    for (const [k, id] of Object.entries(RND_FIELDS)) o[k] = Math.max(0, parseInt($('#' + id).value, 10) || 0);
    o.atoms = Math.max(1, Math.min(26, o.atoms));
    o.minFormulas = Math.max(1, o.minFormulas);
    o.maxFormulas = Math.max(o.minFormulas, o.maxFormulas);
    o.mode = $('#rnd-mode').value;
    o.constants = $('#rnd-constants').checked;
    o.seed = o.seed || 1;
    return o;
  }
  function samplerSummary() {
    const o = samplerSettings();
    const forms = o.minFormulas === o.maxFormulas ? o.minFormulas + ' formulas' : o.minFormulas + '–' + o.maxFormulas + ' formulas';
    const shape = o.mode === 'cnf' ? 'clauses of length ' + o.clauseLength : 'formulas of depth ≤ ' + o.maxDepth;
    return o.atoms + ' atoms, ' + forms + ', ' + shape + (o.constants ? ', with ⊤/⊥' : '') + ', seed ' + o.seed;
  }
  const savedSampler = store.get('sampler', null);
  if (savedSampler) {
    for (const [k, id] of Object.entries(RND_FIELDS)) if (savedSampler[k] != null) $('#' + id).value = savedSampler[k];
    if (savedSampler.mode) $('#rnd-mode').value = savedSampler.mode;
    $('#rnd-constants').checked = !!savedSampler.constants;
  }
  function onSamplerChange() { store.set('sampler', samplerSettings()); renderSelectionLines(); }
  $('#random-panel').addEventListener('change', onSamplerChange);
  $('#btn-random-seed').addEventListener('click', () => { $('#rnd-seed').value = 1 + Math.floor(Math.random() * 99999); onSamplerChange(); });
  $('#btn-random').addEventListener('click', () => {
    const o = samplerSettings();
    const kb = IMC.sampleKB(o, o.seed);
    setText('% random knowledge base (seed ' + o.seed + ')\n' + kb.formulas.map(f => IMC.toPretty(f)).join('\n'), { immediate: true });
    $('#rnd-seed').value = o.seed + 1;
    onSamplerChange();
    computeSelected();
  });
  const fileInput = $('#file-input');
  $('#btn-upload').addEventListener('click', () => fileInput.click());
  fileInput.addEventListener('change', () => { if (fileInput.files[0]) loadFile(fileInput.files[0]); fileInput.value = ''; });
  function loadFile(file) {
    const r = new FileReader();
    r.onload = () => {
      let text = String(r.result);
      if (/\.(cnf|dimacs)$/i.test(file.name) || /^\s*(c\s.*\n\s*)*p\s+cnf/m.test(text)) {
        try {
          const kb = IMC.parseDimacs(text);
          text = '% ' + file.name + ' (DIMACS, one clause per formula)\n' + kb.formulas.map(f => IMC.toPretty(f)).join('\n');
        } catch (e) { toast('Could not read the DIMACS file: ' + e.message); return; }
      } else text = toTweety(text);
      setText(text, { immediate: true });
      toast('Loaded ' + file.name);
    };
    r.onerror = () => toast('Could not read ' + file.name);
    r.readAsText(file);
  }
  const editorBox = $('#editor');
  ['dragenter', 'dragover'].forEach(t => editorBox.addEventListener(t, (e) => { e.preventDefault(); editorBox.classList.add('dragging'); $('#drop-hint').hidden = false; }));
  ['dragleave', 'drop'].forEach(t => editorBox.addEventListener(t, (e) => { e.preventDefault(); editorBox.classList.remove('dragging'); $('#drop-hint').hidden = true; }));
  editorBox.addEventListener('drop', (e) => { const f = e.dataTransfer && e.dataTransfer.files[0]; if (f) loadFile(f); });
  // downloads are always in TweetyProject syntax
  $('#btn-download').addEventListener('click', () => { const t = toTweety(S.text); download('knowledge-base.txt', t.endsWith('\n') ? t : t + '\n'); });
  $('#btn-clear').addEventListener('click', () => { setText(''); input.focus(); });

  // ---------------------------------------------------------------- tabs
  const TABS = ['measures', 'structure', 'culpability', 'postulates', 'incremental', 'compare', 'worlds', 'help'];
  function selectTab(name) {
    if (!TABS.includes(name)) name = 'measures';
    S.tab = name; store.set('tab', name);
    for (const t of TABS) {
      $('#tab-' + t).setAttribute('aria-selected', String(t === name));
      $('#tab-' + t).tabIndex = t === name ? 0 : -1;
      $('#view-' + t).hidden = t !== name;
    }
    if (name === 'structure') renderStructure();
    if (name === 'worlds') renderWorlds();
    if (name === 'help') renderHelp();
    if (name === 'incremental' || name === 'compare' || name === 'postulates') renderSelectionLines();
  }
  TABS.forEach(t => $('#tab-' + t).addEventListener('click', () => selectTab(t)));
  $('.tabs').addEventListener('keydown', (e) => {
    if (e.key !== 'ArrowRight' && e.key !== 'ArrowLeft') return;
    const i = TABS.indexOf(S.tab) + (e.key === 'ArrowRight' ? 1 : -1);
    const t = TABS[(i + TABS.length) % TABS.length];
    selectTab(t); $('#tab-' + t).focus();
  });
  function invalidateViews() {
    if (S.tab === 'worlds') renderWorlds();
  }
  // header link and #reference address open the Reference tab
  function openReference() {
    selectTab('help');
    $('.tabs').scrollIntoView({ block: 'nearest' });
  }
  $('#link-reference').addEventListener('click', (e) => {
    e.preventDefault();
    openReference();
    try { if (location.hash !== '#reference') history.pushState(null, '', '#reference'); } catch (err) { /* history unavailable */ }
  });
  window.addEventListener('hashchange', () => { if (location.hash === '#reference') openReference(); });

  // "Measures: … [Change]" and "Generator: … [Change]" lines on the analysis tabs
  function measuresLine() {
    const sel = selectedInstances();
    return [el('span', { class: 'lbl' }, 'Measures:'),
      ...(sel.length ? sel.map(x => el('span', { class: 'mchip' }, instLabel(x))) : [el('span', { class: 'fine' }, 'none selected')]),
      el('button', { type: 'button', class: 'compact', onclick: () => { selectTab('measures'); $('#tab-measures').focus(); } }, 'Change')];
  }
  function generatorLine() {
    return [el('span', { class: 'lbl' }, 'Generator:'), el('span', null, samplerSummary()),
      el('button', { type: 'button', class: 'compact', onclick: () => openGenerator(true) }, 'Change')];
  }
  function renderSelectionLines() {
    $('#incr-measures-line').replaceChildren(...measuresLine());
    $('#cmp-measures-line').replaceChildren(...measuresLine());
    $('#cmp-gen-line').replaceChildren(...generatorLine());
    $('#post-gen-line').replaceChildren(...generatorLine());
    $('#post-gen-line').hidden = postMode() !== 'random';
  }

  // ---------------------------------------------------------------- measures tab
  const tbody = $('#measures-body');
  function paramControls(inst, onChange) {
    const m = BY_ID.get(inst.id);
    if (!m.params.length) return null;
    const box = el('div', { class: 'm-params' });
    for (const p of m.params) {
      const sel = el('select', { 'aria-label': m.label + ': ' + p.label, title: p.label });
      for (const [v, l] of p.options) sel.append(el('option', { value: v }, l));
      sel.value = String(inst.params[p.id]);
      sel.addEventListener('change', () => { inst.params[p.id] = sel.value; saveInstances(); if (onChange) onChange(); });
      box.append(sel);
    }
    return box;
  }
  function addCopy(inst) {
    const copy = { key: inst.id + '#' + (++copyCounter), id: inst.id, params: Object.assign({}, inst.params) };
    S.instances.splice(S.instances.indexOf(inst) + 1, 0, copy);
    S.selected.add(copy.key);
    saveInstances(); saveSelected();
    buildMeasureTable();
    renderPostPickers();
    renderCulpSelect();
    const row = tbody.querySelector('tr[data-key="' + copy.key + '"] select');
    if (row) row.focus();
  }
  function removeCopy(inst) {
    S.instances = S.instances.filter(x => x !== inst);
    S.selected.delete(inst.key);
    postSel.measures.delete(inst.key);
    delete S.results[inst.key];
    saveInstances(); saveSelected(); store.set('postMeasures', Array.from(postSel.measures));
    buildMeasureTable();
    renderPostPickers();
    renderCulpSelect();
  }
  function buildMeasureTable() {
    tbody.replaceChildren();
    let fam = null;
    for (const inst of orderedInstances()) {
      const m = BY_ID.get(inst.id);
      if (m.family !== fam) { fam = m.family; tbody.append(el('tr', { class: 'family-row' }, el('td', { colspan: '5' }, fam))); }
      const isCopy = inst.key !== inst.id;
      const cb = el('input', { type: 'checkbox', 'aria-label': 'Select ' + instLabel(inst) });
      cb.checked = S.selected.has(inst.key);
      cb.addEventListener('change', () => { if (cb.checked) S.selected.add(inst.key); else S.selected.delete(inst.key); saveSelected(); syncSelection(); });
      const params = paramControls(inst, () => { renderMeasureValues(); renderSelectionLines(); renderPostPickers(); renderCulpSelect(); });
      if (params) {
        params.append(el('button', { type: 'button', class: 'param-btn', title: 'Add a copy of this measure with its own parameters', 'aria-label': 'Add a copy of ' + m.label, onclick: () => addCopy(inst) }, '+'));
        if (isCopy) params.append(el('button', { type: 'button', class: 'param-btn', title: 'Remove this copy', 'aria-label': 'Remove this copy of ' + m.label, onclick: () => removeCopy(inst) }, '−'));
      }
      const info = el('button', { type: 'button', class: 'info-btn', 'aria-label': 'About ' + m.label, title: 'Definition and reference', 'aria-expanded': 'false' }, 'i');
      const tr = el('tr', { 'data-key': inst.key },
        el('td', { class: 'c-check' }, cb),
        el('td', null, el('div', { class: 'm-name' }, el('span', { class: 'm-head' }, el('span', { class: 'm-label' }, m.label), symbolNode(m.symbol)), params)),
        el('td', { class: 'c-val' }),
        el('td', { class: 'c-ms' }),
        el('td', { class: 'c-info' }, info));
      const detail = el('tr', { class: 'detail', hidden: true },
        el('td', { colspan: '5' }, el('div', { class: 'detail-inner' },
          el('span', null, m.description),
          el('span', { class: 'fine' }, m.reference),
          el('span', { class: 'fine' }, 'TweetyProject: ', javaRef(m.java)),
          m.approximate ? el('span', { class: 'fine' }, 'Computed by numerical optimisation; exact for the minimum t-norm.') : null)));
      info.addEventListener('click', () => { detail.hidden = !detail.hidden; info.setAttribute('aria-expanded', String(!detail.hidden)); });
      tbody.append(tr, detail);
    }
    syncSelection();
    renderMeasureValues();
  }
  function syncSelection() {
    for (const tr of $$('tr[data-key]', tbody)) {
      const k = tr.dataset.key;
      tr.classList.toggle('unselected', !S.selected.has(k));
      $('input[type=checkbox]', tr).checked = S.selected.has(k);
    }
    const all = $('#check-all');
    all.checked = S.selected.size === S.instances.length;
    all.indeterminate = S.selected.size > 0 && S.selected.size < S.instances.length;
    $('#btn-compute').disabled = S.selected.size === 0 || S.running;
    renderSelectionLines();
  }
  $('#check-all').addEventListener('change', (e) => {
    S.selected = e.target.checked ? new Set(S.instances.map(x => x.key)) : new Set();
    saveSelected(); syncSelection();
  });
  function renderMeasureValues() {
    const key = kbKey();
    for (const tr of $$('tr[data-key]', tbody)) {
      const inst = instByKey(tr.dataset.key);
      const r = S.results[inst.key];
      const vc = $('.c-val', tr), mc = $('.c-ms', tr);
      vc.replaceChildren(); mc.textContent = ''; vc.removeAttribute('title');
      if (!r) continue;
      if (r.status === 'queued') { vc.append(el('span', { class: 'v-run' }, 'queued')); continue; }
      if (r.status === 'running') { vc.append(el('span', { class: 'v-run' }, el('span', { class: 'spinner' }), 'running')); continue; }
      const stale = r.key !== key || r.pkey !== paramKey(inst);
      const dot = el('span', { class: 'vdot ' + (stale ? 'old' : 'fresh'), role: 'img', 'aria-label': stale ? 'outdated' : 'up to date' });
      if (r.status === 'ok') {
        const v = deser(r.value);
        vc.append(el('span', { class: v === Infinity ? 'v-inf' : null }, fmtNum(v)), dot);
        vc.title = fmtFull(v) + (stale ? ' (outdated: the knowledge base or the parameters changed since this value was computed)' : '');
        mc.textContent = fmtMs(r.ms);
      } else if (r.status === 'timeout') {
        vc.append(el('span', { class: 'v-to' }, 'timeout'), dot);
        vc.title = 'Exceeded the time limit; raise the timeout and compute again.';
        if (r.limit) mc.textContent = '> ' + fmtMs(r.limit);
      } else if (r.status === 'cancelled') {
        vc.append(el('span', { class: 'v-to' }, 'cancelled'));
      } else {
        vc.append(el('span', { class: 'v-err' }, r.msg || 'error'), dot);
      }
    }
    renderRunNote();
  }
  function renderRunNote() {
    const note = $('#run-note');
    if (!S.lastRun) { note.replaceChildren(); return; }
    note.replaceChildren(
      el('span', null, 'Values for φ1…φ' + S.lastRun.size + (S.lastRun.size === 0 ? ' (empty knowledge base)' : '') + '.'),
      el('span', { class: 'legend-dot' }, el('span', { class: 'vdot fresh' }), 'up to date'),
      el('span', { class: 'legend-dot' }, el('span', { class: 'vdot old' }), 'outdated'),
      el('span', null, 'Ctrl/⌘ + Enter in the editor recomputes.'));
    const prog = $('#run-progress');
    if (!S.running) {
      prog.className = 'run-progress' + (S.parsed && S.parsed.errors.length ? ' warn' : '');
      prog.textContent = S.parsed && S.parsed.errors.length ? 'Fix the syntax errors to recompute.' : '';
    }
  }
  function timeoutMs() { return Math.max(1, parseFloat($('#timeout-input').value) || 10) * 1000; }
  $('#timeout-input').value = store.get('timeout', 10);
  $('#timeout-input').addEventListener('change', () => store.set('timeout', parseFloat($('#timeout-input').value) || 10));

  async function computeSelected() {
    if (S.running) return;
    if (!S.parsed || S.parsed.errors.length) { toast('Fix the syntax errors first'); return; }
    const insts = selectedInstances();
    if (!insts.length) { toast('Select at least one measure'); return; }
    S.running = true; S.cancelled = false;
    S.lastRun = { size: S.parsed.kb.size };
    $('#btn-compute').disabled = true; $('#btn-cancel').hidden = false;
    const text = S.text, key = kbKey();
    for (const x of insts) S.results[x.key] = { status: 'queued', key, pkey: paramKey(x) };
    renderMeasureValues();
    const prog = $('#run-progress');
    prog.className = 'run-progress';
    let i = 0;
    for (const x of insts) {
      i++;
      const pkey = paramKey(x);
      if (S.cancelled) { S.results[x.key] = { status: 'cancelled', key, pkey }; continue; }
      S.results[x.key] = { status: 'running', key, pkey };
      prog.textContent = 'Computing ' + instLabel(x) + ' (' + i + ' of ' + insts.length + ')…';
      renderMeasureValues();
      const t0 = Date.now();
      try {
        const r = await main.call({ op: 'measure', text, id: x.id, params: Object.assign({}, x.params) }, { timeout: timeoutMs() });
        S.results[x.key] = { status: 'ok', value: r.value, ms: r.ms, key, pkey };
      } catch (e) {
        const st = e.name === 'TimeoutError' ? 'timeout' : e.name === 'CancelError' ? 'cancelled' : 'error';
        S.results[x.key] = { status: st, msg: e.message, ms: Date.now() - t0, limit: timeoutMs(), key, pkey };
      }
      renderMeasureValues();
    }
    S.running = false;
    prog.textContent = '';
    $('#btn-cancel').hidden = true;
    syncSelection();
    renderMeasureValues();
  }
  $('#btn-compute').addEventListener('click', computeSelected);
  $('#btn-cancel').addEventListener('click', () => { S.cancelled = true; main.cancelAll(); });

  // export
  const exportMenu = $('#export-menu');
  $('#btn-export').addEventListener('click', (e) => { e.stopPropagation(); exportMenu.hidden = !exportMenu.hidden; $('#btn-export').setAttribute('aria-expanded', String(!exportMenu.hidden)); });
  document.addEventListener('click', () => { exportMenu.hidden = true; $('#btn-export').setAttribute('aria-expanded', 'false'); });
  function resultRows() {
    const key = kbKey();
    return orderedInstances().filter(x => S.results[x.key] && S.results[x.key].key === key && S.results[x.key].pkey === paramKey(x)).map(x => {
      const r = S.results[x.key];
      return { id: x.id, label: instLabel(x), status: r.status, value: r.status === 'ok' ? deser(r.value) : null, ms: r.ms, params: x.params };
    });
  }
  exportMenu.addEventListener('click', (e) => {
    const b = e.target.closest('button[data-export]');
    if (!b) return;
    const rows = resultRows();
    if (!rows.length) { toast('Compute the measures for the current knowledge base first'); return; }
    const kind = b.dataset.export;
    const valStr = (r) => r.status === 'ok' ? fmtFull(r.value) : r.status;
    if (kind === 'csv') {
      const q = (s) => '"' + String(s).replace(/"/g, '""') + '"';
      download('inconsistency-values.csv', 'measure,id,value,time_ms\n' + rows.map(r => [q(r.label), r.id, valStr(r), r.ms == null ? '' : r.ms].join(',')).join('\n') + '\n', 'text/csv');
    } else if (kind === 'json') {
      download('inconsistency-values.json', JSON.stringify({ knowledgeBase: S.parsed.kb.formulas.map(f => IMC.toTweetyString(f)), measures: rows.map(r => ({ id: r.id, measure: r.label, parameters: r.params, value: r.status === 'ok' ? IMC.serializeValue(r.value) : null, status: r.status, timeMs: r.ms })) }, null, 2), 'application/json');
    } else if (kind === 'tsv') {
      copyText(rows.map(r => r.label + '\t' + valStr(r)).join('\n'), 'Table');
    } else if (kind === 'latex') {
      const tex = (v) => v === Infinity ? '$\\infty$' : Number.isNaN(v) ? 'n/a' : fmtNum(v);
      const lines = ['\\begin{tabular}{lr}', '\\toprule', 'Measure & Value \\\\', '\\midrule']
        .concat(rows.map(r => r.label.replace(/[&%_#]/g, m => '\\' + m) + ' & ' + (r.status === 'ok' ? tex(r.value) : r.status) + ' \\\\'))
        .concat(['\\bottomrule', '\\end{tabular}']);
      copyText(lines.join('\n'), 'LaTeX table');
    }
    exportMenu.hidden = true;
  });

  // ---------------------------------------------------------------- formula chips
  function fchip(i, kb) {
    kb = kb || S.parsed.kb;
    return el('span', { class: 'fchip', 'data-tip': esc('φ' + (i + 1) + ': ' + kb.texts[i]) }, el('b', null, 'φ' + (i + 1)), truncate(kb.texts[i], 40));
  }
  function setList(sets, prefix, limit) {
    limit = limit || 200;
    if (!sets.length) return el('p', { class: 'empty' }, 'None.');
    const ul = el('ul', { class: 'set-list' });
    sets.slice(0, limit).forEach((s, j) => ul.append(el('li', null, el('span', { class: 'set-idx' }, prefix + (j + 1)), s.length ? s.map(i => fchip(i)) : el('span', { class: 'fine' }, '∅ (empty set)'))));
    if (sets.length > limit) ul.append(el('li', { class: 'fine' }, '… and ' + (sets.length - limit) + ' more'));
    return ul;
  }

  // ---------------------------------------------------------------- conflicts tab
  function renderStructure() {
    const out = $('#structure-out');
    if (!S.parsed) return;
    if (S.parsed.errors.length) { out.replaceChildren(el('p', { class: 'err-box' }, 'Fix the syntax errors in the knowledge base first.')); return; }
    if (S.structureKey !== kbKey() || (!S.structure && !S.structureErr)) { out.replaceChildren(el('p', { class: 'empty' }, el('span', { class: 'spinner' }), 'Enumerating minimal inconsistent subsets…')); return; }
    if (S.structureErr) { out.replaceChildren(el('p', { class: 'err-box' }, 'The conflict analysis did not finish: ' + S.structureErr)); return; }
    const st = S.structure, kb = S.parsed.kb;
    const tiles = el('div', { class: 'tiles' },
      tile(kb.size, 'formulas'), tile(st.atoms.length, 'atoms'), tile(st.muses.length, 'minimal inconsistent subsets'),
      tile(st.consistent ? 0 : st.mcses.length, 'minimal correction sets'), tile(st.free.length, 'free formulas'), tile(st.selfContradictory.length, 'self-contradictory'));
    const parts = [tiles];
    if (st.consistent) parts.push(el('p', { class: 'lede' }, 'The knowledge base is consistent: it has a model, no minimal inconsistent subsets, and every inconsistency measure is 0.'));
    else {
      parts.push(el('div', { class: 'card' },
        el('div', { class: 'card-head' }, el('h3', null, 'Minimal inconsistent subsets'), el('span', { class: 'fine' }, 'MI(K): inconsistent, but every proper subset is consistent')),
        setList(st.muses, 'M')));
      parts.push(conflictMatrixCard(st, kb));
      parts.push(el('div', { class: 'two-col' },
        el('div', { class: 'card' },
          el('div', { class: 'card-head' }, el('h3', null, 'Minimal correction sets'), el('span', { class: 'fine' }, 'remove one set to restore consistency')),
          setList(st.mcses, 'C')),
        el('div', { class: 'card' },
          el('div', { class: 'card-head' }, el('h3', null, 'Maximal consistent subsets'), el('span', { class: 'fine' }, 'complements of the correction sets')),
          setList(st.msses, 'S'))));
      parts.push(el('div', { class: 'two-col' },
        el('div', { class: 'card' },
          el('div', { class: 'card-head' }, el('h3', null, 'Free formulas'), el('span', { class: 'fine' }, 'in no minimal inconsistent subset')),
          st.free.length ? el('div', null, st.free.map(i => fchip(i))) : el('p', { class: 'empty' }, 'None.')),
        el('div', { class: 'card' },
          el('div', { class: 'card-head' }, el('h3', null, 'Conflict components'), el('span', { class: 'fine' }, 'groups of overlapping minimal inconsistent subsets')),
          setList(st.components, 'G'))));
      if (st.selfContradictory.length) parts.push(el('div', { class: 'card' }, el('h3', null, 'Self-contradictory formulas'),
        el('p', { class: 'lede' }, 'These formulas have no model. Several measures (hitting set, Dalal-Sum/Max, MCSC) are infinite as a consequence.'),
        el('div', null, st.selfContradictory.map(i => fchip(i)))));
    }
    parts.push(el('p', { class: 'fine' }, 'Enumerated in ' + fmtMs(st.ms) + ' (' + st.satCalls + ' SAT calls).'));
    out.replaceChildren(...parts);
  }
  function tile(v, label) { return el('div', { class: 'tile' }, el('span', { class: 't-val' }, String(v)), el('span', { class: 't-lbl' }, label)); }

  const SERIES = ['--series-1', '--series-2', '--series-3', '--series-4', '--series-5', '--series-6', '--series-7', '--series-8'];
  function conflictMatrixCard(st, kb) {
    const card = el('div', { class: 'card' }, el('div', { class: 'card-head' }, el('h3', null, 'Formulas × minimal inconsistent subsets'),
      el('span', { class: 'fine' }, 'filled cell: the formula belongs to the subset; hover for details')));
    const k = st.muses.length, n = kb.size;
    if (k > 150 || n > 150) { card.append(el('p', { class: 'empty' }, 'Too many sets to draw.')); return card; }
    const cell = 18, gap = 2, top = 34;
    const maxLen = Math.min(26, Math.max(...kb.texts.map(t => t.length), 1));
    const labelW = 44 + 7.2 * maxLen;
    const W = labelW + k * (cell + gap) + 10, H = top + n * (cell + gap) + 6;
    const color = (j) => j < 8 ? `var(${SERIES[j]})` : 'var(--ink-3)';
    let svg = `<svg viewBox="0 0 ${W} ${H}" width="${W}" height="${H}" role="img" aria-label="Incidence matrix of formulas and minimal inconsistent subsets">`;
    for (let j = 0; j < k; j++) svg += `<text x="${labelW + j * (cell + gap) + cell / 2}" y="${top - 10}" text-anchor="middle" font-size="11" class="mono-t">M${j + 1}</text>`;
    const inMus = st.muses.map(m => new Set(m));
    for (let i = 0; i < n; i++) {
      const y = top + i * (cell + gap);
      svg += `<text x="${labelW - 8}" y="${y + cell / 2 + 4}" text-anchor="end" font-size="11.5" class="mono-t"><tspan style="fill:var(--accent);font-weight:600">φ${i + 1}</tspan> ${esc(truncate(kb.texts[i], 26))}</text>`;
      for (let j = 0; j < k; j++) {
        const x = labelW + j * (cell + gap);
        const on = inMus[j].has(i);
        svg += `<rect x="${x}" y="${y}" width="${cell}" height="${cell}" rx="3" style="fill:${on ? color(j) : 'var(--surface-2)'}" data-tip="${esc('φ' + (i + 1) + ' ' + (on ? '∈' : '∉') + ' M' + (j + 1) + ' (size ' + st.muses[j].length + ')')}"/>`;
      }
    }
    svg += '</svg>';
    const box = el('div', { class: 'chart', html: svg });
    bindTips(box);
    const row = el('div', { class: 'viz-row' }, box);
    if (k <= 40 && n <= 40) row.append(conflictGraph(st, kb));
    card.append(row);
    return card;
  }
  function conflictGraph(st, kb) {
    const n = kb.size, R = Math.max(90, Math.min(190, 18 * n)), cx = R + 70, cy = R + 30, W = 2 * R + 140, H = 2 * R + 60;
    const pos = [];
    for (let i = 0; i < n; i++) { const a = -Math.PI / 2 + 2 * Math.PI * i / n; pos.push([cx + R * Math.cos(a), cy + R * Math.sin(a)]); }
    const free = new Set(st.free), selfc = new Set(st.selfContradictory);
    let svg = `<svg viewBox="0 0 ${W} ${H}" width="${W}" height="${H}" role="img" aria-label="Conflict graph: formulas on a circle, each minimal inconsistent subset drawn as a polygon">`;
    st.muses.forEach((m, j) => {
      const color = j < 8 ? `var(${SERIES[j]})` : 'var(--ink-3)';
      const pts = m.map(i => pos[i]);
      const label = esc('M' + (j + 1) + ' = {' + m.map(i => 'φ' + (i + 1)).join(', ') + '}');
      if (m.length === 1) svg += `<circle cx="${pts[0][0]}" cy="${pts[0][1]}" r="15" style="fill:none;stroke:${color};stroke-width:2" data-tip="${label}"/>`;
      else if (m.length === 2) svg += `<line x1="${pts[0][0]}" y1="${pts[0][1]}" x2="${pts[1][0]}" y2="${pts[1][1]}" style="stroke:${color};stroke-width:2.5;stroke-linecap:round" data-tip="${label}"/>`;
      else svg += `<polygon points="${pts.map(p => p.join(',')).join(' ')}" style="fill:${color};fill-opacity:0.10;stroke:${color};stroke-width:2;stroke-linejoin:round" data-tip="${label}"/>`;
    });
    for (let i = 0; i < n; i++) {
      const [x, y] = pos[i];
      const fill = free.has(i) ? 'var(--surface-2)' : 'var(--surface)';
      const stroke = selfc.has(i) ? 'var(--bad)' : free.has(i) ? 'var(--line-strong)' : 'var(--ink-2)';
      svg += `<g data-tip="${esc('φ' + (i + 1) + ': ' + kb.texts[i] + (free.has(i) ? ' (free)' : '') + (selfc.has(i) ? ' (self-contradictory)' : ''))}"><circle cx="${x}" cy="${y}" r="11" style="fill:${fill};stroke:${stroke};stroke-width:${selfc.has(i) ? 2.5 : 1.5}"/>`;
      svg += `<text x="${x}" y="${y + 4}" text-anchor="middle" font-size="10.5" font-weight="600" class="mono-t" style="fill:var(--ink)">${i + 1}</text></g>`;
    }
    svg += '</svg>';
    const box = el('div', { class: 'chart', html: svg });
    bindTips(box);
    const legend = el('div', { class: 'legend' },
      st.muses.slice(0, 8).map((m, j) => el('span', null, el('span', { class: 'sw', style: `background:var(${SERIES[j]})` }), 'M' + (j + 1))),
      st.muses.length > 8 ? el('span', null, el('span', { class: 'sw', style: 'background:var(--ink-3)' }), 'M9…M' + st.muses.length) : null,
      el('span', null, 'nodes: formulas φi'));
    return el('div', { class: 'stack', style: 'gap:8px' }, box, legend);
  }

  // ---------------------------------------------------------------- Shapley value tab
  const culpSel = $('#culp-measure');
  function renderCulpSelect() {
    const cur = culpSel.value || store.get('culp', 'mi');
    culpSel.replaceChildren(...orderedInstances().map(x => el('option', { value: x.key }, instLabel(x))));
    culpSel.value = instByKey(cur) ? cur : 'mi';
    renderCulpParams();
  }
  function renderCulpParams() {
    const inst = instByKey(culpSel.value);
    $('#culp-params').replaceChildren(paramControls(inst, () => { renderCulpSelectLabels(); renderMeasureValues(); renderSelectionLines(); renderPostPickers(); }) || '');
  }
  function renderCulpSelectLabels() { for (const o of culpSel.options) { const x = instByKey(o.value); if (x) o.textContent = instLabel(x); } }
  culpSel.addEventListener('change', () => { store.set('culp', culpSel.value); renderCulpParams(); });
  let lastCulp = null;
  $('#btn-culp').addEventListener('click', async () => {
    if (!S.parsed || S.parsed.errors.length) { toast('Fix the syntax errors first'); return; }
    const out = $('#culp-out');
    const n = S.parsed.kb.size;
    if (n > 14) { out.replaceChildren(el('p', { class: 'err-box' }, 'Shapley values evaluate all 2ⁿ sub-bases; this knowledge base has ' + n + ' formulas (maximum 14).')); return; }
    const inst = instByKey(culpSel.value);
    const params = Object.assign({}, inst.params);
    const bar = el('div', { class: 'progress' }, el('div'));
    out.replaceChildren(el('p', { class: 'empty' }, el('span', { class: 'spinner' }), 'Evaluating ' + (1 << n) + ' sub-bases…'), bar);
    const btn = $('#btn-culp'); btn.disabled = true;
    try {
      const timeout = Math.max(60000, timeoutMs() * 6);
      const sh = await main.call({ op: 'shapley', text: S.text, id: inst.id, params }, { timeout, onProgress: (p) => { bar.firstChild.style.width = Math.round(p * 100) + '%'; } });
      const rm = await main.call({ op: 'removal', text: S.text, id: inst.id, params }, { timeout });
      lastCulp = { label: instLabel(inst), sh, rm, kb: S.parsed.kb };
      renderCulp();
    } catch (e) {
      out.replaceChildren(el('p', { class: 'err-box' }, e.name === 'TimeoutError' ? 'The computation timed out. Choose a faster measure or a smaller knowledge base.' : e.message));
    } finally { btn.disabled = false; }
  });
  function renderCulp() {
    if (!lastCulp) return;
    const { label, sh, rm, kb } = lastCulp;
    const out = $('#culp-out');
    const vals = sh.values.map(deser);
    const total = deser(sh.total);
    const sum = vals.reduce((a, b) => a + b, 0);
    const chart = barChart(vals.map((v, i) => ({ label: 'φ' + (i + 1), text: kb.texts[i], value: v })), label);
    const table = el('table', null,
      el('thead', null, el('tr', null, el('th', null, 'Formula'), el('th', { class: 'c-val' }, 'Shapley value'), el('th', { class: 'c-val' }, 'Removal impact'), el('th', { class: 'c-val' }, 'I(K ∖ {φ})'))),
      el('tbody', null, vals.map((v, i) => el('tr', null,
        el('td', null, fchip(i, kb)),
        el('td', { class: 'c-val', title: fmtFull(v) }, fmtNum(v)),
        el('td', { class: 'c-val', title: fmtFull(rm.values[i].impact) }, fmtNum(rm.values[i].impact)),
        el('td', { class: 'c-val' }, fmtNum(rm.values[i].without))))));
    out.replaceChildren(
      el('div', { class: 'card' },
        el('div', { class: 'card-head' }, el('h3', null, 'Shapley inconsistency values for ' + label),
          el('span', { class: 'fine' }, 'I(K) = ' + fmtNum(total) + ' · Σ values = ' + fmtNum(sum))),
        chart),
      el('div', { class: 'table-wrap' }, table));
  }
  function barChart(rows, title) {
    const finite = rows.filter(r => isFinite(r.value));
    let max = Math.max(0, ...finite.map(r => r.value)), min = Math.min(0, ...finite.map(r => r.value));
    if (max === min) max = min + 1;
    const ticks = niceTicks(min, max, 4);
    min = Math.min(min, ticks[0]); max = Math.max(max, ticks[ticks.length - 1]);
    const labelW = 250, plotW = 360, rowH = 22, top = 8, bottom = 26, W = labelW + plotW + 60, H = top + rows.length * rowH + bottom;
    const x = (v) => labelW + (v - min) / (max - min) * plotW;
    let svg = `<svg viewBox="0 0 ${W} ${H}" width="${W}" height="${H}" role="img" aria-label="${esc('Bar chart: ' + title)}">`;
    for (const t of ticks) svg += `<line class="gridline" x1="${x(t)}" x2="${x(t)}" y1="${top}" y2="${H - bottom}"/><text x="${x(t)}" y="${H - 8}" text-anchor="middle" font-size="11">${fmtNum(t, 3)}</text>`;
    svg += `<line class="baseline" x1="${x(0)}" x2="${x(0)}" y1="${top}" y2="${H - bottom}"/>`;
    rows.forEach((r, i) => {
      const y = top + i * rowH;
      svg += `<text x="${labelW - 8}" y="${y + rowH / 2 + 4}" text-anchor="end" font-size="11.5" class="mono-t"><tspan style="fill:var(--accent);font-weight:600">${r.label}</tspan> ${esc(truncate(r.text, 26))}</text>`;
      const tipText = esc(r.label + ': ' + r.text + ' → ' + fmtFull(r.value));
      if (!isFinite(r.value)) { svg += `<text x="${x(0) + 6}" y="${y + rowH / 2 + 4}" font-size="12" class="mono-t" data-tip="${tipText}">${fmtNum(r.value)}</text>`; return; }
      const x0 = x(Math.min(0, r.value)), x1 = x(Math.max(0, r.value)), w = Math.max(1, x1 - x0), h = 13, yy = y + (rowH - h) / 2;
      const rr = Math.min(4, w / 2);
      // rounded data-end, square at the baseline
      const path = r.value >= 0
        ? `M${x0},${yy} H${x1 - rr} Q${x1},${yy} ${x1},${yy + rr} V${yy + h - rr} Q${x1},${yy + h} ${x1 - rr},${yy + h} H${x0} Z`
        : `M${x1},${yy} H${x0 + rr} Q${x0},${yy} ${x0},${yy + rr} V${yy + h - rr} Q${x0},${yy + h} ${x0 + rr},${yy + h} H${x1} Z`;
      svg += `<path d="${path}" style="fill:var(--series-1)" data-tip="${tipText}"/>`;
      svg += `<rect x="${labelW}" y="${y}" width="${plotW}" height="${rowH}" style="fill:transparent" data-tip="${tipText}"/>`;
      const lx = r.value >= 0 ? x1 + 5 : x0 - 5;
      svg += `<text x="${lx}" y="${y + rowH / 2 + 4}" text-anchor="${r.value >= 0 ? 'start' : 'end'}" font-size="11.5" class="mono-t" style="fill:var(--ink)">${fmtNum(r.value, 3)}</text>`;
    });
    svg += '</svg>';
    const box = el('div', { class: 'chart', html: svg });
    bindTips(box);
    return box;
  }
  function niceTicks(min, max, count) {
    const span = max - min || 1;
    const step0 = span / Math.max(1, count);
    const mag = Math.pow(10, Math.floor(Math.log10(step0)));
    const err = step0 / mag;
    const step = (err >= 7.5 ? 10 : err >= 3.5 ? 5 : err >= 1.5 ? 2 : 1) * mag;
    const ticks = [];
    for (let t = Math.floor(min / step) * step; t <= max + step * 0.5; t += step) ticks.push(+t.toFixed(10));
    if (ticks[ticks.length - 1] < max) ticks.push(+(ticks[ticks.length - 1] + step).toFixed(10));
    return ticks;
  }

  // ---------------------------------------------------------------- postulates tab
  const POSTS = IMC.POSTULATES;
  const postSel = { measures: new Set(store.get('postMeasures', ['drastic', 'mi', 'mic', 'eta', 'contension', 'hs', 'dalalsum', 'nc', 'mc', 'pr'])), postulates: new Set(store.get('postPostulates', POSTS.map(p => p.id))) };
  function checkList(container, items, set, storeKey, countEl) {
    container.replaceChildren();
    const tools = el('div', { class: 'tools' },
      el('button', { type: 'button', class: 'link', onclick: () => { items.forEach(it => set.add(it.id)); store.set(storeKey, Array.from(set)); checkList(container, items, set, storeKey, countEl); } }, 'All'),
      el('button', { type: 'button', class: 'link', onclick: () => { set.clear(); store.set(storeKey, []); checkList(container, items, set, storeKey, countEl); } }, 'None'));
    container.append(tools);
    for (const it of items) {
      const cb = el('input', { type: 'checkbox' });
      cb.checked = set.has(it.id);
      cb.addEventListener('change', () => { if (cb.checked) set.add(it.id); else set.delete(it.id); store.set(storeKey, Array.from(set)); countEl.textContent = items.filter(x => set.has(x.id)).length; });
      container.append(el('label', { title: it.title || '' }, cb, it.label));
    }
    countEl.textContent = items.filter(x => set.has(x.id)).length;
  }
  function renderPostPickers() {
    checkList($('#post-measures'), orderedInstances().map(x => ({ id: x.key, label: instLabel(x) })), postSel.measures, 'postMeasures', $('#post-mcount'));
  }
  checkList($('#post-postulates'), POSTS.map(p => ({ id: p.id, label: p.name, title: p.description })), postSel.postulates, 'postPostulates', $('#post-pcount'));
  const postMode = () => $('input[name=post-mode]:checked').value;
  $$('input[name=post-mode]').forEach(r => r.addEventListener('change', () => { $('#post-count-wrap').hidden = postMode() !== 'random'; renderSelectionLines(); }));
  let lastPost = null;
  $('#btn-post').addEventListener('click', async () => {
    const mode = postMode();
    if (mode === 'current' && (!S.parsed || S.parsed.errors.length)) { toast('Fix the syntax errors first'); return; }
    const insts = orderedInstances().filter(x => postSel.measures.has(x.key));
    const measures = insts.map(x => ({ key: x.key, id: x.id, params: Object.assign({}, x.params) }));
    const posts = POSTS.filter(p => postSel.postulates.has(p.id)).map(p => p.id);
    if (!measures.length || !posts.length) { toast('Select at least one measure and one postulate'); return; }
    const out = $('#post-out');
    const bar = el('div', { class: 'progress' }, el('div'));
    out.replaceChildren(el('p', { class: 'empty' }, el('span', { class: 'spinner' }), 'Checking ' + posts.length + ' postulates for ' + measures.length + ' measures…'), bar);
    const btn = $('#btn-post'); btn.disabled = true;
    const count = Math.max(1, Math.min(2000, parseInt($('#post-count').value, 10) || 100));
    try {
      const req = mode === 'random'
        ? { op: 'postulates', mode, measures, postulates: posts, sampler: samplerSettings(), count }
        : { op: 'postulates', mode, text: S.text, measures, postulates: posts };
      const res = await main.call(req, { timeout: Math.max(120000, timeoutMs() * 20), onProgress: (p) => { bar.firstChild.style.width = Math.round(p * 100) + '%'; } });
      lastPost = { mode, res, measures: insts.map(x => ({ key: x.key, label: instLabel(x) })), posts, count };
      renderPost();
    } catch (e) {
      out.replaceChildren(el('p', { class: 'err-box' }, e.name === 'TimeoutError' ? 'The check timed out. Use fewer measures, fewer random bases, or a smaller knowledge base.' : e.message));
    } finally { btn.disabled = false; }
  });
  function renderPost(selected) {
    if (!lastPost) return;
    const { mode, res, measures, posts } = lastPost;
    const out = $('#post-out');
    const detail = el('div', { class: 'card', id: 'post-detail' }, el('p', { class: 'empty' }, 'Select a cell to see the counterexamples.'));
    const head = el('tr', null, el('th', null, 'Measure'), posts.map(pid => { const p = IMC.POSTULATE_BY_ID.get(pid); return el('th', { class: 'rot', title: p.name + ': ' + p.description }, p.short); }));
    const body = el('tbody');
    for (const ms of measures) {
      const tr = el('tr', null, el('td', null, ms.label));
      for (const pid of posts) {
        const r = res[ms.key][pid];
        let cls, txt, tipT;
        const p = IMC.POSTULATE_BY_ID.get(pid);
        if (mode === 'random') {
          if (!r.applicable) { cls = 'na'; txt = '–'; tipT = 'Not applicable on any generated base'; }
          else if (!r.violatedKbs) { cls = 'ok'; txt = '✓'; tipT = 'No violation on ' + r.applicable + ' applicable bases'; }
          else { cls = 'no'; txt = Math.round(100 * r.violatedKbs / r.applicable) + '%'; tipT = 'Violated on ' + r.violatedKbs + ' of ' + r.applicable + ' applicable bases'; }
        } else {
          if (!r.instances) { cls = 'na'; txt = '–'; tipT = 'Not applicable to this knowledge base'; }
          else if (!r.violations.length) { cls = 'ok'; txt = '✓'; tipT = 'Satisfied on ' + r.instances + ' instance' + (r.instances === 1 ? '' : 's'); }
          else { cls = 'no'; txt = '✗'; tipT = (r.violations.length + (r.more || 0)) + ' of ' + r.instances + ' instances violated'; }
        }
        const isSel = selected && selected[0] === ms.key && selected[1] === pid;
        const b = el('button', { type: 'button', class: 'pc ' + cls + (isSel ? ' sel' : ''), title: p.name + ' · ' + ms.label + ': ' + tipT, 'aria-label': p.name + ', ' + ms.label + ': ' + tipT }, txt);
        if (cls !== 'na') b.addEventListener('click', () => renderPost([ms.key, pid]));
        tr.append(el('td', null, b));
      }
      body.append(tr);
    }
    if (selected) {
      const [mkey, pid] = selected;
      const ms = measures.find(x => x.key === mkey);
      const r = res[mkey][pid];
      const p = IMC.POSTULATE_BY_ID.get(pid);
      const kids = [el('div', { class: 'card-head' }, el('h3', null, p.name + ' · ' + ms.label), el('span', { class: 'fine' }, p.description))];
      if (mode === 'random') {
        kids.push(el('p', null, r.violatedKbs ? 'Violated on ' + r.violatedKbs + ' of ' + r.applicable + ' applicable random bases (' + r.kbs + ' generated).' : 'No violation found on ' + r.applicable + ' applicable random bases.'));
        if (r.example) {
          const exText = r.example.kb.map(t => inNotation(t)).join('\n');
          kids.push(el('p', { class: 'fine' }, 'First counterexample knowledge base:'));
          kids.push(el('pre', { class: 'fchip', style: 'white-space:pre-wrap;display:block;padding:6px 8px' }, exText));
          kids.push(el('p', null, inNotation(r.example.violation.text) + ': ', el('span', { class: 'mono' }, r.example.violation.values)));
          kids.push(el('button', { type: 'button', class: 'compact', onclick: () => { setText('% counterexample: ' + p.name + ' / ' + ms.label + '\n' + r.example.kb.join('\n'), { immediate: true }); toast('Loaded the counterexample into the editor'); } }, 'Load into editor'));
        }
      } else {
        kids.push(el('p', null, r.violations.length ? (r.violations.length + (r.more || 0)) + ' of ' + r.instances + ' checked instances violate the postulate.' : 'All ' + r.instances + ' checked instances satisfy the postulate.'));
        const ul = el('ul', { class: 'set-list' });
        r.violations.forEach(v => ul.append(el('li', null, el('span', null, v.text), el('span', { class: 'mono fine' }, v.values))));
        if (r.more) ul.append(el('li', { class: 'fine' }, '… ' + r.more + ' more'));
        if (r.violations.length) kids.push(ul);
      }
      detail.replaceChildren(...kids);
    }
    const legend = el('p', { class: 'fine' }, mode === 'random'
      ? '✓ no counterexample · percentage: share of applicable random bases with a violation · – not applicable. Values are compared with a tolerance of 10⁻⁹.'
      : '✓ satisfied on all derived instances · ✗ violated · – no applicable instance. Values are compared with a tolerance of 10⁻⁹.');
    out.replaceChildren(el('div', { class: 'table-wrap' }, el('table', { class: 'post-table' }, el('thead', null, head), body)), legend, detail);
  }

  // ---------------------------------------------------------------- incremental tab
  let lastIncr = null;
  $('#btn-incr').addEventListener('click', async () => {
    if (!S.parsed || S.parsed.errors.length) { toast('Fix the syntax errors first'); return; }
    const insts = selectedInstances();
    if (!insts.length) { toast('Select measures on the Measures tab'); return; }
    const out = $('#incr-out');
    const bar = el('div', { class: 'progress' }, el('div'));
    out.replaceChildren(el('p', { class: 'empty' }, el('span', { class: 'spinner' }), 'Computing ' + insts.length + ' measures on ' + S.parsed.kb.size + ' growing bases…'), bar);
    const btn = $('#btn-incr'); btn.disabled = true;
    try {
      const r = await main.call({ op: 'incremental', text: S.text, measures: insts.map(x => ({ id: x.id, params: Object.assign({}, x.params) })) },
        { timeout: Math.max(60000, timeoutMs() * S.parsed.kb.size * 2), onProgress: (p) => { bar.firstChild.style.width = Math.round(p * 100) + '%'; } });
      lastIncr = { labels: insts.map(instLabel), series: r.series.map(s => s.map(deser)), kb: S.parsed.kb };
      renderIncr();
    } catch (e) {
      out.replaceChildren(el('p', { class: 'err-box' }, e.name === 'TimeoutError' ? 'Timed out. Select fewer or faster measures.' : e.message));
    } finally { btn.disabled = false; }
  });
  function renderIncr() {
    if (!lastIncr) return;
    const { labels, series, kb } = lastIncr;
    const grid = el('div', { class: 'mult-grid' });
    labels.forEach((label, t) => grid.append(sparkPanel(label, series[t], kb)));
    $('#incr-out').replaceChildren(grid);
  }
  function sparkPanel(label, vals, kb) {
    const n = vals.length, W = 240, H = 104, l = 30, r = 12, top = 10, b = 22;
    const finite = vals.filter(v => v != null && isFinite(v));
    let lo = Math.min(0, ...finite), hi = Math.max(...finite, lo + 1e-9);
    if (!finite.length) hi = 1;
    if (hi - lo < 1e-9) hi = lo + 1;
    const x = (i) => n <= 1 ? l + (W - l - r) / 2 : l + i * (W - l - r) / (n - 1);
    const y = (v) => top + (1 - (v - lo) / (hi - lo)) * (H - top - b);
    let svg = `<svg viewBox="0 0 ${W} ${H}" width="100%" role="img" aria-label="${esc(label + ' as formulas are added')}">`;
    svg += `<line class="gridline" x1="${l}" x2="${W - r}" y1="${y(hi)}" y2="${y(hi)}"/><line class="baseline" x1="${l}" x2="${W - r}" y1="${y(lo)}" y2="${y(lo)}"/>`;
    svg += `<text x="${l - 5}" y="${y(hi) + 4}" text-anchor="end" font-size="10" class="mono-t">${fmtNum(hi, 2)}</text><text x="${l - 5}" y="${y(lo) + 4}" text-anchor="end" font-size="10" class="mono-t">${fmtNum(lo, 2)}</text>`;
    svg += `<text x="${x(0)}" y="${H - 6}" text-anchor="middle" font-size="10" class="mono-t">φ1</text>`;
    if (n > 1) svg += `<text x="${x(n - 1)}" y="${H - 6}" text-anchor="middle" font-size="10" class="mono-t">φ${n}</text>`;
    let d = '', pen = false;
    vals.forEach((v, i) => {
      if (v == null || !isFinite(v)) { pen = false; return; }
      d += (pen ? 'L' : 'M') + x(i).toFixed(1) + ',' + y(v).toFixed(1) + ' '; pen = true;
    });
    svg += `<path d="${d}" style="fill:none;stroke:var(--series-1);stroke-width:2;stroke-linejoin:round;stroke-linecap:round"/>`;
    vals.forEach((v, i) => {
      const tipT = esc('K' + (i + 1) + ' = {φ1…φ' + (i + 1) + '}, adding ' + kb.texts[i] + ': ' + fmtFull(v == null ? 'error' : v));
      const last = i === n - 1;
      if (v == null || !isFinite(v)) svg += `<text x="${x(i)}" y="${top + 8}" text-anchor="middle" font-size="11" style="fill:var(--warn)" data-tip="${tipT}">${v == null ? '!' : fmtNum(v)}</text>`;
      else svg += `<circle cx="${x(i)}" cy="${y(v)}" r="${last ? 4 : 2.5}" style="fill:${last ? 'var(--series-1)' : 'var(--surface)'};stroke:var(--series-1);stroke-width:1.5"/>`;
      svg += `<rect x="${x(i) - 8}" y="${top}" width="16" height="${H - top - b}" style="fill:transparent" data-tip="${tipT}"/>`;
    });
    svg += '</svg>';
    const last = vals[n - 1];
    const box = el('div', { class: 'mult' }, el('div', { class: 'mult-title' }, el('b', null, label), el('span', null, 'I(K) = ' + fmtNum(last == null ? NaN : last))), el('div', { class: 'chart', html: svg }));
    bindTips(box);
    return box;
  }

  // ---------------------------------------------------------------- compare tab
  let lastCmp = null;
  $('#btn-cmp').addEventListener('click', async () => {
    const insts = selectedInstances();
    if (insts.length < 2) { toast('Select at least two measures on the Measures tab'); return; }
    const count = Math.max(5, Math.min(2000, parseInt($('#cmp-count').value, 10) || 150));
    const out = $('#cmp-out');
    const bar = el('div', { class: 'progress' }, el('div'));
    out.replaceChildren(el('p', { class: 'empty' }, el('span', { class: 'spinner' }), 'Computing ' + insts.length + ' measures on ' + count + ' random bases…'), bar);
    const btn = $('#btn-cmp'); btn.disabled = true;
    try {
      const r = await main.call({ op: 'compare', measures: insts.map(x => ({ id: x.id, params: Object.assign({}, x.params) })), sampler: samplerSettings(), count },
        { timeout: Math.max(120000, timeoutMs() * 30), onProgress: (p) => { bar.firstChild.style.width = Math.round(p * 100) + '%'; } });
      lastCmp = { labels: insts.map(instLabel), tau: r.tau.map(row => row.map(deser)), values: r.values.map(s => s.map(deser)), kbs: r.kbs, sel: null };
      renderCmp();
    } catch (e) {
      out.replaceChildren(el('p', { class: 'err-box' }, e.name === 'TimeoutError' ? 'Timed out. Use fewer bases or faster measures.' : e.message));
    } finally { btn.disabled = false; }
  });
  function hexToRgb(h) { h = h.replace('#', ''); if (h.length === 3) h = h.split('').map(c => c + c).join(''); const v = parseInt(h, 16); return [(v >> 16) & 255, (v >> 8) & 255, v & 255]; }
  function mix(a, b, t) { return a.map((x, i) => Math.round(x + (b[i] - x) * t)); }
  function divColor(t) {
    const lo = hexToRgb(cssVar('--div-low')), mid = hexToRgb(cssVar('--div-mid')), hi = hexToRgb(cssVar('--div-high'));
    return t < 0 ? mix(mid, lo, Math.min(1, -t)) : mix(mid, hi, Math.min(1, t));
  }
  function lum([r, g, b]) { const f = (c) => { c /= 255; return c <= 0.03928 ? c / 12.92 : Math.pow((c + 0.055) / 1.055, 2.4); }; return 0.2126 * f(r) + 0.7152 * f(g) + 0.0722 * f(b); }
  function renderCmp() {
    if (!lastCmp) return;
    const { labels, tau, kbs } = lastCmp;
    const k = labels.length, cell = k > 16 ? 30 : 40, gap = 2, labelW = 170, top = 130, W = labelW + k * (cell + gap) + 10, H = top + k * (cell + gap) + 10;
    let svg = `<svg viewBox="0 0 ${W} ${H}" width="${W}" height="${H}" role="img" aria-label="Heatmap of Kendall tau between measures">`;
    labels.forEach((lab, j) => {
      const xx = labelW + j * (cell + gap) + cell / 2;
      svg += `<text transform="translate(${xx + 4},${top - 8}) rotate(-50)" font-size="11.5">${esc(truncate(lab, 30))}</text>`;
    });
    labels.forEach((lab, i) => {
      const yy = top + i * (cell + gap);
      svg += `<text x="${labelW - 8}" y="${yy + cell / 2 + 4}" text-anchor="end" font-size="11.5">${esc(truncate(lab, 26))}</text>`;
      labels.forEach((lab2, j) => {
        const t = tau[i][j];
        const xx = labelW + j * (cell + gap);
        const ok = !Number.isNaN(t);
        const c = ok ? divColor(t) : hexToRgb(cssVar('--div-mid'));
        const fill = `rgb(${c.join(',')})`;
        const ink = lum(c) > 0.35 ? '#141920' : '#ffffff';
        const sel = lastCmp.sel && lastCmp.sel[0] === i && lastCmp.sel[1] === j;
        svg += `<rect x="${xx}" y="${yy}" width="${cell}" height="${cell}" rx="3" style="fill:${fill};${sel ? 'stroke:var(--ink);stroke-width:2' : ''};cursor:pointer" data-i="${i}" data-j="${j}" data-tip="${esc(lab + ' vs. ' + lab2 + ': τ = ' + (ok ? t.toFixed(3) : 'undefined (a measure is constant)'))}"/>`;
        svg += `<text x="${xx + cell / 2}" y="${yy + cell / 2 + 4}" text-anchor="middle" font-size="11" class="mono-t" style="fill:${ink};pointer-events:none">${ok ? (i === j ? '1' : t.toFixed(2).replace('0.', '.').replace('-.', '−.')) : '–'}</text>`;
      });
    });
    svg += '</svg>';
    const box = el('div', { class: 'chart', html: svg });
    bindTips(box);
    box.addEventListener('click', (e) => { const r = e.target.closest('rect[data-i]'); if (!r) return; lastCmp.sel = [+r.dataset.i, +r.dataset.j]; renderCmp(); });
    const lowC = cssVar('--div-low'), midC = cssVar('--div-mid'), hiC = cssVar('--div-high');
    const legend = el('div', { class: 'legend' },
      el('span', null, el('span', { class: 'sw', style: `background:${lowC}` }), 'τ = −1 opposite order'),
      el('span', null, el('span', { class: 'sw', style: `background:${midC};outline:1px solid var(--line)` }), 'τ = 0 no agreement'),
      el('span', null, el('span', { class: 'sw', style: `background:${hiC}` }), 'τ = +1 same order'),
      el('span', null, kbs.length + ' bases used; select a cell for the scatter plot'));
    const parts = [el('div', { class: 'card' }, el('div', { class: 'card-head' }, el('h3', null, 'Rank correlation (Kendall τ_b)')), legend, box)];
    if (lastCmp.sel) parts.push(scatterCard(lastCmp.sel[0], lastCmp.sel[1]));
    $('#cmp-out').replaceChildren(...parts);
  }
  function scatterCard(i, j) {
    const { labels, values } = lastCmp;
    const a = labels[j], b = labels[i];
    const xs = values[j], ys = values[i];
    const pts = xs.map((v, t) => [v, ys[t], t]).filter(p => isFinite(p[0]) && isFinite(p[1]));
    const W = 460, H = 300, l = 52, r = 16, top = 14, bt = 40;
    let x0 = Math.min(...pts.map(p => p[0]), 0), x1 = Math.max(...pts.map(p => p[0]), x0 + 1);
    let y0 = Math.min(...pts.map(p => p[1]), 0), y1 = Math.max(...pts.map(p => p[1]), y0 + 1);
    const xt = niceTicks(x0, x1, 5), yt = niceTicks(y0, y1, 4);
    x0 = xt[0]; x1 = xt[xt.length - 1]; y0 = yt[0]; y1 = yt[yt.length - 1];
    const X = (v) => l + (v - x0) / (x1 - x0 || 1) * (W - l - r), Y = (v) => top + (1 - (v - y0) / (y1 - y0 || 1)) * (H - top - bt);
    let svg = `<svg viewBox="0 0 ${W} ${H}" width="${W}" height="${H}" role="img" aria-label="${esc('Scatter plot of ' + a + ' against ' + b)}">`;
    for (const t of xt) svg += `<line class="gridline" x1="${X(t)}" x2="${X(t)}" y1="${top}" y2="${H - bt}"/><text x="${X(t)}" y="${H - bt + 15}" text-anchor="middle" font-size="10.5" class="mono-t">${fmtNum(t, 2)}</text>`;
    for (const t of yt) svg += `<line class="gridline" x1="${l}" x2="${W - r}" y1="${Y(t)}" y2="${Y(t)}"/><text x="${l - 6}" y="${Y(t) + 4}" text-anchor="end" font-size="10.5" class="mono-t">${fmtNum(t, 2)}</text>`;
    svg += `<text x="${(l + W - r) / 2}" y="${H - 6}" text-anchor="middle" font-size="11.5">${esc(a)}</text>`;
    svg += `<text transform="translate(12,${(top + H - bt) / 2}) rotate(-90)" text-anchor="middle" font-size="11.5">${esc(b)}</text>`;
    const count = new Map();
    for (const [px, py, t] of pts) {
      const k = fmtNum(px, 6) + '|' + fmtNum(py, 6);
      const c = count.get(k) || { px, py, n: 0, t };
      c.n++; count.set(k, c);
    }
    for (const c of count.values()) {
      const rad = Math.min(14, 4 + 2 * Math.sqrt(c.n - 1));
      svg += `<circle cx="${X(c.px)}" cy="${Y(c.py)}" r="${rad}" style="fill:var(--series-1);fill-opacity:0.55;stroke:var(--surface);stroke-width:1.5" data-tip="${esc(a + ' = ' + fmtNum(c.px) + ', ' + b + ' = ' + fmtNum(c.py) + ' · ' + c.n + ' base' + (c.n === 1 ? '' : 's'))}"/>`;
    }
    svg += '</svg>';
    const box = el('div', { class: 'chart', html: svg });
    bindTips(box);
    const skipped = xs.length - pts.length;
    return el('div', { class: 'card' }, el('div', { class: 'card-head' }, el('h3', null, a + ' vs. ' + b),
      el('span', { class: 'fine' }, 'larger dots: several bases with equal values' + (skipped ? ' · ' + skipped + ' bases with infinite values not shown' : ''))), box);
  }

  // ---------------------------------------------------------------- worlds tab
  let worldsKey = null;
  $('#worlds-best').addEventListener('change', () => { worldsKey = null; renderWorlds(); });
  async function renderWorlds() {
    const out = $('#worlds-out');
    if (!S.parsed) return;
    if (S.parsed.errors.length) { out.replaceChildren(el('p', { class: 'err-box' }, 'Fix the syntax errors in the knowledge base first.')); return; }
    const key = kbKey() + '|' + $('#worlds-best').checked + '|' + S.notation;
    if (worldsKey === key) return;
    worldsKey = key;
    const kb = S.parsed.kb;
    if (kb.atoms.length > 12) { out.replaceChildren(el('p', { class: 'err-box' }, 'This knowledge base has ' + kb.atoms.length + ' atoms; the table is limited to 12 atoms (4096 worlds).')); return; }
    out.replaceChildren(el('p', { class: 'empty' }, el('span', { class: 'spinner' }), 'Enumerating worlds…'));
    try {
      const r = await bg.call({ op: 'worlds', text: S.text, maxAtoms: 12 }, { timeout: 20000 });
      if (worldsKey !== key) return;
      const worlds = r.worlds.map(w => ({ w: w.w, sat: w.sat, dist: w.dist.map(deser), nsat: w.sat.filter(Boolean).length }));
      const best = Math.max(...worlds.map(w => w.nsat));
      let rows = worlds;
      if ($('#worlds-best').checked) rows = worlds.filter(w => w.nsat === best);
      const limit = 1024;
      const thead = el('tr', null, r.atoms.map(a => el('th', { class: 'fhead', title: a }, a)),
        kb.formulas.map((_, i) => el('th', { class: 'fhead', 'data-tip': esc('φ' + (i + 1) + ': ' + kb.texts[i]) }, 'φ' + (i + 1))),
        el('th', { title: 'Number of satisfied formulas' }, '#sat'), el('th', { title: 'Sum of Dalal distances to the models of each formula' }, 'Σ dist'), el('th', { title: 'Maximum Dalal distance' }, 'max dist'));
      const tb = el('tbody');
      for (const w of rows.slice(0, limit)) {
        const sum = w.dist.reduce((a, b) => a + b, 0), mx = Math.max(0, ...w.dist);
        tb.append(el('tr', { class: w.nsat === best ? 'best' : null },
          r.atoms.map((_, j) => el('td', { class: 'atomv' }, (w.w >> j) & 1 ? '1' : '0')),
          w.sat.map((s, i) => el('td', { class: s ? 'sat' : 'unsat', 'data-tip': esc('φ' + (i + 1) + (s ? ' satisfied' : ' violated, distance ' + fmtNum(w.dist[i]))) }, s ? '✓' : String(fmtNum(w.dist[i])))),
          el('td', null, String(w.nsat)), el('td', null, fmtNum(sum)), el('td', null, fmtNum(mx))));
      }
      const parts = [el('p', { class: 'fine' }, worlds.length + ' worlds · at most ' + best + ' of ' + kb.size + ' formulas can be satisfied together (Dalal-Hit = ' + (kb.size - best) + ') · cells of violated formulas show the Dalal distance to that formula\'s models.'),
        el('div', { class: 'table-wrap' }, el('table', { class: 'worlds' }, el('thead', null, thead), tb))];
      if (rows.length > limit) parts.push(el('p', { class: 'fine' }, 'Showing the first ' + limit + ' of ' + rows.length + ' worlds.'));
      out.replaceChildren(...parts);
    } catch (e) {
      if (e.name === 'CancelError') { worldsKey = null; return; }
      out.replaceChildren(el('p', { class: 'err-box' }, e.message));
    }
  }

  // ---------------------------------------------------------------- reference tab
  let helpDone = false;
  function renderHelp() {
    if (helpDone) return;
    helpDone = true;
    const out = $('#help-out');
    const dl = el('dl');
    for (const m of ORDERED) {
      dl.append(el('dt', null, m.label, el('span', { class: 'm-sub' }, symbolNode(m.symbol), ' · ' + m.family)),
        el('dd', null, m.description, el('span', { class: 'fine' }, m.reference), el('span', { class: 'fine' }, 'TweetyProject: ', javaRef(m.java))));
    }
    const pdl = el('dl');
    for (const p of POSTS) pdl.append(el('dt', null, p.name, el('span', { class: 'm-sub' }, p.short)), el('dd', null, p.description));
    out.replaceChildren(
      el('h3', null, 'Writing knowledge bases'),
      el('p', null, 'Enter one propositional formula per line in TweetyProject syntax or with logical symbols (switch the notation above the editor). Atom names may contain letters, digits and characters other than ', el('code', null, '| & ! ( ) < > = ^'), '. Operators, from strongest to weakest binding: ', el('code', null, '!'), ' / ¬ (not), ', el('code', null, '&&'), ' / ∧ (and), ', el('code', null, '||'), ' / ∨ (or), ', el('code', null, '^^'), ' / ⊕ (exclusive or), ', el('code', null, '=>'), ' / → (implies), ', el('code', null, '<=>'), ' / ↔ (equivalent). ', el('code', null, '+'), ' / ⊤ and ', el('code', null, '-'), ' / ⊥ denote tautology and contradiction. Chains of ', el('code', null, '=>'), ' associate to the right. Lines starting with ', el('code', null, '%'), ' or ', el('code', null, '#'), ' are comments.'),
      el('p', null, 'You can also upload a text file in this syntax or a DIMACS CNF file (each clause becomes one formula). A knowledge base is a set: identical lines are merged, but syntactic variants such as ', el('code', null, 'a && b'), ' and ', el('code', null, 'b && a'), ' are different formulas, as in TweetyProject. Downloads always use TweetyProject syntax.'),
      el('p', null, 'Measures with parameters (Fuzzy, Iceberg) can be added several times with different settings: use the + button next to their parameters, and − to remove a copy.'),
      el('h3', null, 'Measures'),
      el('p', null, 'All measures follow the implementations in TweetyProject (packages ', el('code', null, 'org.tweetyproject.logics.commons.analysis'), ' and ', el('code', null, 'org.tweetyproject.logics.pl.analysis'), '), including their conventions for special cases: ∞ for the hitting-set, Dalal-Sum/Max and MCSC measures when a formula is unsatisfiable and for the contension measure when there is no paraconsistent model, the natural logarithm in the independent-set measure, and NaN where the Java code divides 0 by 0. Some algorithms differ from the Java code (MARCO instead of naive MUS enumeration, SAT encodings instead of enumerating interpretations, exact search instead of an ILP solver) without changing the values.'),
      dl,
      el('h3', null, 'Rationality postulates'),
      pdl,
      el('h3', null, 'About'),
      el('p', null, 'Everything runs locally in your browser using JavaScript. The computations run in a background worker with a per-measure time limit. Measures are exponential in the worst case; keep knowledge bases small for the MUS-based, Iceberg and Shapley analyses.'),
      el('p', null, 'TweetyProject and this website are developed by Matthias Thimm and contributors under the ', el('a', { href: 'https://www.gnu.org/licenses/lgpl-3.0.html', target: '_blank', rel: 'noopener' }, 'GNU Lesser General Public License v3'), ': ', el('a', { href: 'https://tweetyproject.org', target: '_blank', rel: 'noopener' }, 'tweetyproject.org'), '.'));
  }

  function rerenderCharts() {
    if (lastCmp) renderCmp();
    if (lastCulp) renderCulp();
  }

  // ---------------------------------------------------------------- init
  applyTheme(store.get('theme', 'system'));
  applyNotation(S.notation, false);
  buildMeasureTable();
  renderPostPickers();
  renderCulpSelect();
  const initial = store.get('text', null);
  input.value = initial != null && initial.trim() !== '' ? initial : inNotation(window.IM_EXAMPLES[0].text);
  onTextChange({ immediate: true });
  selectTab(location.hash === '#reference' ? 'help' : S.tab);
  computeSelected();
})();
