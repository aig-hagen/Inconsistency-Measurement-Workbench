import java.util.*;

import org.tweetyproject.commons.util.MathTools;
import org.tweetyproject.logics.commons.analysis.*;
import org.tweetyproject.logics.pl.analysis.*;
import org.tweetyproject.logics.pl.parser.PlParser;
import org.tweetyproject.logics.pl.postulates.ImPostulate;
import org.tweetyproject.logics.pl.sat.*;
import org.tweetyproject.logics.pl.syntax.*;
import org.tweetyproject.math.func.fuzzy.MinimumNorm;
import org.tweetyproject.math.func.fuzzy.ProductNorm;
import org.tweetyproject.math.opt.solver.ApacheCommonsCMAESOptimizer;
import org.tweetyproject.math.opt.solver.Solver;

/**
 * Checks of the bug fixes in TweetyProject that the comparison on random knowledge
 * bases does not cover. Compile and run it against the fixed sources (TWEETY = the
 * TweetyProject working tree, SP = its source folders as in compile.sh):
 *   CP=$(sed 's#:[^:]*/build-fixed$##' validation/java/build-fixed/classpath.txt)
 *   javac -proc:none -cp "$CP" -sourcepath "$SP" -d validation/java/build-checks validation/java/FixChecks.java
 *   java -cp "$CP:validation/java/build-checks" FixChecks
 * For the original sources, put a folder with the original versions of the changed
 * files (git show HEAD:...) in front of SP. Every line starts with "ok" or "FAIL".
 * Three checks are controls that also pass with the original sources (equivalence
 * of the CNF, applicability of safe-formula independence, the postulate for MI).
 */
public class FixChecks {
	static int failures = 0;
	static PlParser parser = new PlParser();

	interface Check { Object run() throws Exception; }

	static void check(String what, Check check, Object expected) {
		check(what, check, expected, 120);
	}

	static void check(String what, Check check, Object expected, int seconds) {
		Object actual;
		java.util.concurrent.ExecutorService ex = java.util.concurrent.Executors.newSingleThreadExecutor(r -> { Thread t = new Thread(r); t.setDaemon(true); return t; });
		try {
			actual = ex.submit(() -> check.run()).get(seconds, java.util.concurrent.TimeUnit.SECONDS);
		} catch (java.util.concurrent.TimeoutException e) {
			actual = "no result within " + seconds + " s";
		} catch (java.util.concurrent.ExecutionException e) {
			actual = e.getCause().getClass().getSimpleName() + ": " + e.getCause().getMessage();
		} catch (Throwable e) {
			actual = e.getClass().getSimpleName() + ": " + e.getMessage();
		} finally {
			ex.shutdownNow();
		}
		boolean ok = Objects.equals(String.valueOf(actual), String.valueOf(expected))
				|| (actual instanceof Double && expected instanceof Double && Math.abs((Double) actual - (Double) expected) < 1e-9);
		if (!ok) failures++;
		System.out.println((ok ? "ok    " : "FAIL  ") + what + ": " + actual + (ok ? "" : " (expected " + expected + ")"));
	}

	static PlFormula f(String s) throws Exception { return parser.parseFormula(s); }

	static PlBeliefSet kb(String... fs) throws Exception {
		PlBeliefSet kb = new PlBeliefSet();
		for (String s : fs) kb.add(f(s));
		return kb;
	}

	public static void main(String[] args) throws Exception {
		SatSolver.setDefaultSolver(new Sat4jSolver());
		PlMusEnumerator.setDefaultEnumerator(new NaiveMusEnumerator<PlFormula>(SatSolver.getDefaultSolver()));
		Solver.setDefaultGeneralSolver(new ApacheCommonsCMAESOptimizer(200, 20000, 0, true, 200, 200, 0.00000001));

		// PlParser: chains of => and <=> associate to the right
		check("PlParser a=>b=>c", () -> f("a => b => c"), "(a=>(b=>c))");
		check("PlParser a<=>b<=>c", () -> f("a <=> b <=> c"), "(a<=>(b<=>c))");

		// Implication.clone() / Equivalence.clone() copy their operands
		Implication imp = (Implication) f("a => b");
		imp.replace(new Proposition("a"), new Tautology(), 1);
		check("Implication.replace() leaves the original unchanged", () -> imp, "(a=>b)");
		Equivalence eq = (Equivalence) f("a <=> b");
		eq.clone().getFormulas().setFirst(new Proposition("z"));
		check("Equivalence.clone() is independent of the original", () -> eq, "(a<=>b)");

		// ExclusiveDisjunction: not a clause, toCnf() is a CNF, accepted by Sat4jSolver
		check("ExclusiveDisjunction.isClause() for a^^b", () -> f("a ^^ b").isClause(), false);
		Conjunction cnf = f("(a && b) ^^ c").toCnf();
		check("toCnf() of (a&&b)^^c is a conjunction of clauses", () -> {
			for (PlFormula clause : cnf)
				if (!(clause instanceof Disjunction) || !((Disjunction) clause).isClause())
					return false;
			return true;
		}, true);
		check("toCnf() of (a&&b)^^c is equivalent to (a&&b)^^c", () -> new org.tweetyproject.logics.pl.reasoner.SimplePlReasoner().query(new PlBeliefSet(Collections.singleton(cnf)), f("(a && b) ^^ c"))
				&& new org.tweetyproject.logics.pl.reasoner.SimplePlReasoner().query(kb("(a && b) ^^ c"), cnf), true);
		check("Sat4jSolver on a^^b", () -> SatSolver.getDefaultSolver().isSatisfiable(kb("a ^^ b")), true);
		check("Sat4jSolver on (-^^a)||b", () -> SatSolver.getDefaultSolver().isSatisfiable(kb("(- ^^ a) || b")), true);
		check("Sat4jSolver on a^^a", () -> SatSolver.getDefaultSolver().isSatisfiable(kb("a ^^ a")), false);

		// SAT-based measures
		PlBeliefSet chain = kb("a", "a => b", "b => c", "!c");
		check("HsSatInconsistencyMeasure on a ; a=>b ; b=>c ; !c", () -> new HsSatInconsistencyMeasure().inconsistencyMeasure(chain), 1.0);
		check("DSumSatInconsistencyMeasure on a ; a=>b ; b=>c ; !c", () -> new DSumSatInconsistencyMeasure().inconsistencyMeasure(chain), 1.0);
		check("ContensionSatInconsistencyMeasure on a ; a=>b ; b=>c ; !c", () -> new ContensionSatInconsistencyMeasure().inconsistencyMeasure(chain), 1.0);
		check("ContensionSatInconsistencyMeasure on a ; !+", () -> new ContensionSatInconsistencyMeasure().inconsistencyMeasure(kb("a", "!+")), Double.POSITIVE_INFINITY);
		check("ContensionInconsistencyMeasure on a ; !+", () -> new ContensionInconsistencyMeasure().inconsistencyMeasure(kb("a", "!+")), Double.POSITIVE_INFINITY);
		check("ContensionSatInconsistencyMeasure on a ; !a ; b ; (b=>c)&&!c (nested implication)", () -> new ContensionSatInconsistencyMeasure().inconsistencyMeasure(kb("a", "!a", "b", "(b => c) && !c")), 2.0);
		check("HsSatInconsistencyMeasure on a ^^ b ; a ; b", () -> new HsSatInconsistencyMeasure().inconsistencyMeasure(kb("a ^^ b", "a", "b")), 1.0);
		// atoms x1 and x11 in 12 formulas: with the renaming name+index, the copy of x1 for
		// formula 10 and the copy of x11 for formula 0 are both "x110" (whatever the order)
		String[] xs = new String[12];
		for (int k = 0; k < 12; k++) xs[k] = "x1 && !x11 && z" + k + " && " + (k % 2 == 0 ? "y" : "!y");
		PlBeliefSet kbx = kb(xs);
		check("DSumSatInconsistencyMeasure on x1&&!x11&&z_k&&(!)y, k=0..11", () -> new DSumSatInconsistencyMeasure().inconsistencyMeasure(kbx), 6.0);
		check("DMaxSatInconsistencyMeasure on x1&&!x11&&z_k&&(!)y, k=0..11", () -> new DMaxSatInconsistencyMeasure().inconsistencyMeasure(kbx), 1.0);

		// MathTools.faculty() and Shapley values for 13 formulas
		check("MathTools.faculty(13)", () -> MathTools.faculty(13), 6227020800L);
		String[] k13 = new String[13];
		k13[0] = "a"; k13[1] = "!a";
		for (int i = 2; i < 13; i++) k13[i] = "b" + i;
		PlBeliefSet kb13 = kb(k13);
		ShapleyCulpabilityMeasure<PlFormula, PlBeliefSet> shapley = new ShapleyCulpabilityMeasure<PlFormula, PlBeliefSet>(new DrasticInconsistencyMeasure<PlFormula>(SatSolver.getDefaultSolver()));
		check("Shapley value (drastic) of a in a ; !a ; b2 ; ... ; b12", () -> shapley.culpabilityMeasure(kb13, f("a")), 0.5, 1800);

		// Safe-formula independence: the safe formula is removed, not added again
		PlBeliefSet safe = kb("b", "!b", "a");
		check("Safe-formula independence applicable to " + safe.getCanonicalOrdering(), () -> ImPostulate.SAFEFORMULAINDEPENDENCE.isApplicable(safe), true);
		check("Safe-formula independence for MI", () -> ImPostulate.SAFEFORMULAINDEPENDENCE.isSatisfied(safe, new MiInconsistencyMeasure<PlFormula>(PlMusEnumerator.getDefaultEnumerator())), true);
		check("Safe-formula independence for normalized MI (violated)", () -> ImPostulate.SAFEFORMULAINDEPENDENCE.isSatisfied(safe, new NormalizedMiInconsistencyMeasure<PlFormula>(PlMusEnumerator.getDefaultEnumerator())), false);

		// Prime implicants of formulas with + and -
		check("prime implicants of a&&(+=>a)", () -> f("a && (+ => a)").getPrimeImplicants(), "[a]");
		check("prime implicants of (e||!e||d)&&+&&!d", () -> f("(e || !e || d) && + && !d").getPrimeImplicants(), "[!d]");
		check("prime implicants of !+", () -> f("!+").getPrimeImplicants(), "[]");

		// Fuzzy measures on knowledge bases without propositions
		check("FuzzyInconsistencyMeasure (product, T) on +", () -> new FuzzyInconsistencyMeasure(new ProductNorm(), FuzzyInconsistencyMeasure.TFUZZY_MEASURE).inconsistencyMeasure(kb("+")), 0.0);
		check("FuzzyInconsistencyMeasure (minimum, sum) on !+", () -> new FuzzyInconsistencyMeasure(new MinimumNorm(), FuzzyInconsistencyMeasure.SUMFUZZY_MEASURE).inconsistencyMeasure(kb("!+")), 1.0);

		// Iceberg
		PlBeliefSet mp = kb("a", "c && (a => b)", "!b");
		check("Iceberg (modus ponens) on a ; c&&(a=>b) ; !b terminates", () -> new IcebergInconsistencyMeasure(IcebergInconsistencyMeasure.ConsequenceOperation.MODUS_PONENS).inconsistencyMeasure(mp), 1.0);
		check("Iceberg (opposite literals) on a ; !a", () -> new IcebergInconsistencyMeasure(IcebergInconsistencyMeasure.ConsequenceOperation.OPPOSITE_LITERALS).inconsistencyMeasure(kb("a", "!a")), 1.0);
		check("Iceberg (conjuncts) on (a&&b)&&c ; !b: a formula is its own conjunct", () -> new IcebergInconsistencyMeasure(IcebergInconsistencyMeasure.ConsequenceOperation.CONJUNCTS).inconsistencyMeasure(kb("(a && b) && c", "!b")), 1.0);

		System.out.println(failures == 0 ? "all checks passed" : failures + " checks failed");
		System.exit(failures == 0 ? 0 : 1);
	}
}
