#!/bin/sh
# Like compile.sh, but with patched/ (fixed Implication.clone) first on the sourcepath.
set -e
TWEETY=${TWEETY:-/Users/mthimm/Shared/GIT/github-tweetyproject}
HERE=$(cd "$(dirname "$0")" && pwd)
CP=$(sed 's#:[^:]*/build$##' "$HERE/build/classpath.txt")
SP="$HERE/patched:$TWEETY/org-tweetyproject-commons/src/main/java"
for m in math logics-commons logics-pl logics-fol graphs plugin; do SP="$SP:$TWEETY/org-tweetyproject-$m/src/main/java"; done
mkdir -p "$HERE/build-patched"
javac -nowarn -encoding UTF-8 -proc:none -d "$HERE/build-patched" -cp "$CP" -sourcepath "$SP" "$HERE/ImHarness.java" 2>&1 | grep -v '^Note:' || true
echo "$CP:$HERE/build-patched" > "$HERE/build-patched/classpath.txt"
echo compiled patched harness
