#!/bin/sh
# Compiles the validation harness against the TweetyProject sources (read-only)
# into validation/java/build (or $OUT). Requires the dependency jars in ~/.m2.
set -e
TWEETY=${TWEETY:-/Users/mthimm/Shared/GIT/github-tweetyproject}
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${OUT:-$HERE/build}
M2=$HOME/.m2/repository
CP="$M2/org/ow2/sat4j/org.ow2.sat4j.core/2.3.5/org.ow2.sat4j.core-2.3.5.jar"
CP="$CP:$M2/org/apache/commons/commons-math/2.1/commons-math-2.1.jar"
CP="$CP:$M2/org/apache/commons/commons-math3/3.2/commons-math3-3.2.jar"
CP="$CP:$M2/org/ojalgo/ojalgo/35.0/ojalgo-35.0.jar"
CP="$CP:$M2/gov/nist/math/jama/1.0.3/jama-1.0.3.jar"
CP="$CP:$M2/isula/isula/1.1.1/isula-1.1.1.jar"
CP="$CP:$M2/jspf/core/1.0.2/core-1.0.2.jar"
CP="$CP:$M2/gurobi/gurobi/9.1.0/gurobi-9.1.0.jar"
SP="$TWEETY/org-tweetyproject-commons/src/main/java"
for m in math logics-commons logics-pl logics-fol graphs plugin; do
  SP="$SP:$TWEETY/org-tweetyproject-$m/src/main/java"
done
mkdir -p "$OUT"
javac -nowarn -encoding UTF-8 -proc:none -d "$OUT" -cp "$CP" -sourcepath "$SP" "$HERE/ImHarness.java" 2>&1 | grep -v '^Note:' || true
echo "$CP:$OUT" > "$OUT/classpath.txt"
echo "compiled; classpath in $OUT/classpath.txt"
