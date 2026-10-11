import java.io.*;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.*;

import org.tweetyproject.commons.ParserException;
import org.tweetyproject.logics.commons.analysis.*;
import org.tweetyproject.logics.pl.analysis.*;
import org.tweetyproject.logics.pl.parser.PlParser;
import org.tweetyproject.logics.pl.sat.*;
import org.tweetyproject.logics.pl.semantics.*;
import org.tweetyproject.logics.pl.syntax.*;
import org.tweetyproject.math.func.FracAggrFunction;
import org.tweetyproject.math.func.fuzzy.MinimumNorm;
import org.tweetyproject.math.func.fuzzy.ProductNorm;
import org.tweetyproject.math.opt.solver.*;

/**
 * Validation harness: computes TweetyProject's inconsistency measures for a
 * file of knowledge bases and prints one JSON line per (kb, measure).
 *
 * Usage:
 *   java ImHarness measures <kbFile> <measureIdsCsv> <startKb> <startMeasure> <timeoutMs>
 *   java ImHarness sat <cnfFile>
 *
 * On a timeout the JVM exits with code 3 (naive Java implementations cannot be
 * interrupted); the driver restarts it at the next position.
 */
public class ImHarness {

	static List<String[]> readKbs(String file) throws IOException {
		List<String[]> kbs = new ArrayList<>();
		List<String> cur = null;
		for (String line : Files.readAllLines(Paths.get(file))) {
			if (line.startsWith("# kb")) {
				if (cur != null) kbs.add(cur.toArray(new String[0]));
				cur = new ArrayList<>();
			} else if (!line.trim().isEmpty()) {
				cur.add(line.trim());
			}
		}
		if (cur != null) kbs.add(cur.toArray(new String[0]));
		return kbs;
	}

	static PlBeliefSet parse(String[] lines, List<PlFormula> order) throws ParserException, IOException {
		PlParser p = new PlParser();
		PlBeliefSet bs = new PlBeliefSet();
		for (String l : lines) {
			PlFormula f = (PlFormula) p.parseFormula(l);
			bs.add(f);
			if (order != null) order.add(f);
		}
		return bs;
	}

	@SuppressWarnings({ "unchecked", "rawtypes" })
	static BeliefSetInconsistencyMeasure<PlFormula> make(String id) {
		AbstractMusEnumerator<PlFormula> en = PlMusEnumerator.getDefaultEnumerator();
		switch (id) {
		case "drastic": return new DrasticInconsistencyMeasure<PlFormula>(SatSolver.getDefaultSolver());
		case "mi": return new MiInconsistencyMeasure<PlFormula>(en);
		case "mic": return new MicInconsistencyMeasure<PlFormula>(en);
		case "nmi": return new NormalizedMiInconsistencyMeasure<PlFormula>(en);
		case "nmic": return new NormalizedMicInconsistencyMeasure<PlFormula>(en);
		case "pr": return new PrInconsistencyMeasure<PlFormula>(en);
		case "mc": return new MaInconsistencyMeasure<PlFormula>(en);
		case "nc": return new NConsInconsistencyMeasure<PlFormula>(en);
		case "mv": return new MusVarInconsistencyMeasure();
		case "df": return new DfInconsistencyMeasure<PlFormula>(new FracAggrFunction(), en);
		case "is": return new IsInconsistencyMeasure<PlFormula>(en);
		case "mcsc": return new McscInconsistencyMeasure<PlFormula>(en);
		case "cc": return new CcInconsistencyMeasure<PlFormula>(en, Solver.getDefaultIntegerLinearSolver());
		case "csp": return new CspInconsistencyMeasure<PlFormula>(en, Solver.getDefaultIntegerLinearSolver());
		case "eta": return (BeliefSetInconsistencyMeasure) new EtaInconsistencyMeasure<PlBeliefSet, PlFormula>(new PossibleWorldIterator());
		case "contension": return new ContensionInconsistencyMeasure();
		case "hs": return (BeliefSetInconsistencyMeasure) new HsInconsistencyMeasure<PlBeliefSet, PlFormula>(new PossibleWorldIterator());
		case "dalalsum": return (BeliefSetInconsistencyMeasure) new DSumInconsistencyMeasure<PossibleWorld, PlBeliefSet, PlFormula>(new DalalDistance(), new PossibleWorldIterator());
		case "dalalmax": return (BeliefSetInconsistencyMeasure) new DMaxInconsistencyMeasure<PossibleWorld, PlBeliefSet, PlFormula>(new DalalDistance(), new PossibleWorldIterator());
		case "dalalhit": return (BeliefSetInconsistencyMeasure) new DHitInconsistencyMeasure<PossibleWorld, PlBeliefSet, PlFormula>(new DalalDistance(), new PossibleWorldIterator());
		case "pm": return new PmInconsistencyMeasure();
		case "fb": return new FbInconsistencyMeasure();
		case "pib": return new PrimeImplicantBasedInconsistencyMeasure();
		case "contension_sat": return new ContensionSatInconsistencyMeasure();
		case "hs_sat": return new HsSatInconsistencyMeasure();
		case "dalalsum_sat": return new DSumSatInconsistencyMeasure();
		case "dalalmax_sat": return new DMaxSatInconsistencyMeasure();
		case "dalalhit_sat": return new DHitSatInconsistencyMeasure();
		case "fuzzy:product:t": return new FuzzyInconsistencyMeasure(new ProductNorm(), FuzzyInconsistencyMeasure.TFUZZY_MEASURE);
		case "fuzzy:product:sum": return new FuzzyInconsistencyMeasure(new ProductNorm(), FuzzyInconsistencyMeasure.SUMFUZZY_MEASURE);
		case "fuzzy:min:t": return new FuzzyInconsistencyMeasure(new MinimumNorm(), FuzzyInconsistencyMeasure.TFUZZY_MEASURE);
		case "fuzzy:min:sum": return new FuzzyInconsistencyMeasure(new MinimumNorm(), FuzzyInconsistencyMeasure.SUMFUZZY_MEASURE);
		}
		if (id.startsWith("iceberg:")) {
			String[] parts = id.split(":");
			IcebergInconsistencyMeasure.ConsequenceOperation op;
			switch (parts[1]) {
			case "identity": op = IcebergInconsistencyMeasure.ConsequenceOperation.IDENTITY; break;
			case "conjuncts": op = IcebergInconsistencyMeasure.ConsequenceOperation.CONJUNCTS; break;
			case "smallest_conjuncts": op = IcebergInconsistencyMeasure.ConsequenceOperation.SMALLEST_CONJUNCTS; break;
			case "classical": op = IcebergInconsistencyMeasure.ConsequenceOperation.MODULAR_CLASSICAL_CONSEQUENCE; break;
			case "modus_ponens": op = IcebergInconsistencyMeasure.ConsequenceOperation.MODUS_PONENS; break;
			case "prime_implicants": op = IcebergInconsistencyMeasure.ConsequenceOperation.PRIME_IMPLICATE; break;
			case "opposite_literals": op = IcebergInconsistencyMeasure.ConsequenceOperation.OPPOSITE_LITERALS; break;
			default: throw new IllegalArgumentException(id);
			}
			return new IcebergInconsistencyMeasure(op, parts.length > 2 && parts[2].equals("sum"));
		}
		throw new IllegalArgumentException("unknown measure " + id);
	}

	static String fmt(double d) {
		if (Double.isNaN(d)) return "\"NaN\"";
		if (Double.isInfinite(d)) return d > 0 ? "\"Infinity\"" : "\"-Infinity\"";
		return Double.toString(d);
	}

	static String esc(String s) {
		if (s == null) return "";
		return s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", " ").replace("\r", " ").replace("\t", " ");
	}

	static String compute(String id, String[] lines) throws Exception {
		if (id.startsWith("shapley:")) {
			String base = id.substring(8);
			List<PlFormula> order = new ArrayList<>();
			PlBeliefSet bs = parse(lines, order);
			ShapleyCulpabilityMeasure<PlFormula, PlBeliefSet> sh = new ShapleyCulpabilityMeasure<>(make(base));
			StringBuilder sb = new StringBuilder("[");
			for (int i = 0; i < order.size(); i++) {
				if (i > 0) sb.append(",");
				sb.append(fmt(sh.culpabilityMeasure(bs, order.get(i))));
			}
			return sb.append("]").toString();
		}
		// fresh parse for every measure: some implementations mutate formulas
		PlBeliefSet bs = parse(lines, null);
		BeliefSetInconsistencyMeasure<PlFormula> m = make(id);
		return fmt(m.inconsistencyMeasure((Collection<PlFormula>) bs));
	}

	static void setup() {
		SatSolver.setDefaultSolver(new Sat4jSolver());
		PlMusEnumerator.setDefaultEnumerator(new NaiveMusEnumerator<PlFormula>(new Sat4jSolver()));
		Solver.setDefaultLinearSolver(new ApacheCommonsSimplex());
		GlpkSolver.setBinary("/opt/homebrew/bin/glpsol");
		Solver.setDefaultIntegerLinearSolver(new GlpkSolver());
		Solver.setDefaultGeneralSolver(new ApacheCommonsCMAESOptimizer(200, 20000, 0, true, 200, 200, 0.00000001));
	}

	public static void main(String[] args) throws Exception {
		// silence Tweety's warnings / debug output on System.err and stray prints
		PrintStream out = new PrintStream(new FileOutputStream(FileDescriptor.out), true, "UTF-8");
		System.setErr(new PrintStream(OutputStream.nullOutputStream()));
		System.setOut(new PrintStream(OutputStream.nullOutputStream()));
		setup();
		if (args[0].equals("sat")) { runSat(args[1], out); return; }
		List<String[]> kbs = readKbs(args[1]);
		String[] measures = args[2].split(",");
		int startKb = Integer.parseInt(args[3]);
		int startM = Integer.parseInt(args[4]);
		long timeout = Long.parseLong(args[5]);
		ExecutorService ex = Executors.newSingleThreadExecutor(r -> { Thread t = new Thread(r); t.setDaemon(true); return t; });
		for (int k = startKb; k < kbs.size(); k++) {
			for (int mi = (k == startKb ? startM : 0); mi < measures.length; mi++) {
				final String id = measures[mi];
				final String[] lines = kbs.get(k);
				long t0 = System.nanoTime();
				Future<String> fut = ex.submit(() -> compute(id, lines));
				String line;
				try {
					String v = fut.get(timeout, TimeUnit.MILLISECONDS);
					long ms = (System.nanoTime() - t0) / 1000000;
					line = "{\"kb\":" + k + ",\"m\":\"" + id + "\",\"v\":" + v + ",\"ms\":" + ms + "}";
				} catch (TimeoutException e) {
					out.println("{\"kb\":" + k + ",\"m\":\"" + id + "\",\"status\":\"timeout\",\"ms\":" + timeout + "}");
					out.flush();
					System.exit(3);
					return;
				} catch (ExecutionException e) {
					Throwable c = e.getCause();
					line = "{\"kb\":" + k + ",\"m\":\"" + id + "\",\"status\":\"error\",\"msg\":\"" + esc(c.getClass().getSimpleName() + ": " + c.getMessage()) + "\"}";
				} catch (Throwable e) {
					line = "{\"kb\":" + k + ",\"m\":\"" + id + "\",\"status\":\"error\",\"msg\":\"" + esc(e.toString()) + "\"}";
				}
				out.println(line);
			}
		}
		out.flush();
		System.exit(0);
	}

	// SAT mode: instances separated by lines "c instance <id>"; prints SAT/UNSAT per instance (Sat4j).
	static void runSat(String file, PrintStream out) throws Exception {
		List<String> lines = Files.readAllLines(Paths.get(file));
		int id = -1;
		List<int[]> clauses = new ArrayList<>();
		int nvars = 0;
		List<Object[]> instances = new ArrayList<>();
		for (String l : lines) {
			l = l.trim();
			if (l.startsWith("c instance")) {
				if (id >= 0) instances.add(new Object[] { id, nvars, clauses });
				id = Integer.parseInt(l.substring(10).trim());
				clauses = new ArrayList<>();
				nvars = 0;
			} else if (l.startsWith("p cnf")) {
				nvars = Integer.parseInt(l.split("\\s+")[2]);
			} else if (!l.isEmpty() && !l.startsWith("c")) {
				String[] toks = l.split("\\s+");
				int[] c = new int[toks.length - 1];
				for (int i = 0; i < toks.length - 1; i++) c[i] = Integer.parseInt(toks[i]);
				clauses.add(c);
			}
		}
		if (id >= 0) instances.add(new Object[] { id, nvars, clauses });
		for (Object[] inst : instances) {
			@SuppressWarnings("unchecked")
			List<int[]> cls = (List<int[]>) inst[2];
			long t0 = System.nanoTime();
			org.sat4j.specs.ISolver s = org.sat4j.minisat.SolverFactory.newDefault();
			s.newVar((Integer) inst[1]);
			boolean sat;
			try {
				for (int[] c : cls) s.addClause(new org.sat4j.core.VecInt(c));
				sat = s.isSatisfiable();
			} catch (org.sat4j.specs.ContradictionException e) {
				sat = false;
			}
			long ms = (System.nanoTime() - t0) / 1000000;
			out.println("{\"id\":" + inst[0] + ",\"sat\":" + sat + ",\"ms\":" + ms + "}");
		}
	}
}
