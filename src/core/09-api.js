// ---------------------------------------------------------------------------
// Request API used by the Web Worker (and usable directly).
// handleRequest(req, progress) -> result; throws on errors / timeouts.
// Analysis contexts are cached per knowledge base so that MUS enumeration is
// shared between measures.
// ---------------------------------------------------------------------------

const ctxCache = new Map();
function contextFor(text) {
  let ctx = ctxCache.get(text);
  if (ctx) { ctxCache.delete(text); ctxCache.set(text, ctx); return ctx; }
  const { kb, errors } = parseKB(text);
  if (errors.length) throw new Error('Knowledge base contains syntax errors (line ' + errors[0].line + ': ' + errors[0].message + ')');
  ctx = makeContext(kb);
  ctxCache.set(text, ctx);
  while (ctxCache.size > 8) ctxCache.delete(ctxCache.keys().next().value);
  return ctx;
}

function serializeValue(v) {
  if (typeof v !== 'number') return v;
  if (Number.isNaN(v)) return 'NaN';
  if (v === Infinity) return 'Infinity';
  if (v === -Infinity) return '-Infinity';
  return v;
}
function deserializeValue(v) {
  if (v === 'NaN') return NaN;
  if (v === 'Infinity') return Infinity;
  if (v === '-Infinity') return -Infinity;
  return v;
}

function measureInfo() {
  return MEASURES.map(m => ({ id: m.id, label: m.label, symbol: m.symbol, family: m.family, description: m.description, reference: m.reference, java: m.java, params: m.params || [], approximate: !!m.approximate }));
}

function handleRequest(req, progress) {
  progress = progress || (() => {});
  switch (req.op) {
    case 'info':
      return { measures: measureInfo(), postulates: POSTULATES };
    case 'measure': {
      const ctx = contextFor(req.text);
      const m = MEASURE_BY_ID.get(req.id);
      if (!m) throw new Error('Unknown measure ' + req.id);
      const t0 = Date.now();
      const v = m.compute(ctx, Object.assign(defaultParams(m), req.params || {}));
      return { value: serializeValue(v), ms: Date.now() - t0 };
    }
    case 'structure': {
      const ctx = contextFor(req.text);
      const t0 = Date.now();
      const s = structure(ctx);
      s.ms = Date.now() - t0;
      s.satCalls = ctx.an.satCalls;
      return s;
    }
    case 'shapley': {
      const ctx = contextFor(req.text);
      const r = shapleyValues(ctx, req.id, req.params, progress);
      return { values: r.values.map(serializeValue), total: serializeValue(r.total) };
    }
    case 'removal': {
      const ctx = contextFor(req.text);
      const r = removalImpact(ctx, req.id, req.params);
      return { total: serializeValue(r.total), values: r.values.map(x => ({ without: serializeValue(x.without), impact: serializeValue(x.impact) })) };
    }
    case 'postulates': {
      if (req.mode === 'random') {
        const out = {};
        req.measures.forEach((ms, i) => {
          out[ms.key || ms.id] = postulatesOnRandom(ms.id, ms.params, req.postulates, req.sampler, req.count,
            (f) => progress((i + f) / req.measures.length));
        });
        return out;
      }
      const ctx = contextFor(req.text);
      const out = {};
      req.measures.forEach((ms, i) => {
        out[ms.key || ms.id] = checkPostulates(ctx.kb, ms.id, ms.params, req.postulates, { maxInstances: req.maxInstances || 128 });
        progress((i + 1) / req.measures.length);
      });
      return out;
    }
    case 'incremental': {
      const ctx = contextFor(req.text);
      const series = incrementalValues(ctx.kb, req.measures, progress);
      return { series: series.map(s => s.map(serializeValue)) };
    }
    case 'compare': {
      const r = compareMeasures(req.measures, req.sampler, req.count, progress);
      return { tau: r.tau.map(row => row.map(serializeValue)), values: r.values.map(s => s.map(serializeValue)), kbs: r.kbs };
    }
    case 'worlds': {
      const ctx = contextFor(req.text);
      const r = possibleWorlds(ctx.kb, req.maxAtoms || 12);
      return { atoms: r.atoms, worlds: r.worlds.map(w => ({ w: w.w, sat: w.sat, dist: w.dist.map(serializeValue) })) };
    }
    case 'sample': {
      const kb = sampleKB(req.sampler, req.seed);
      return { text: kb.formulas.map(f => toPretty(f)).join('\n') };
    }
    default:
      throw new Error('Unknown request ' + req.op);
  }
}

IM.handleRequest = handleRequest;
IM.serializeValue = serializeValue;
IM.deserializeValue = deserializeValue;
IM.measureInfo = measureInfo;
