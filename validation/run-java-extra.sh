#!/bin/sh
# Runs after run-all-java.sh: (1) FB with patched Implication.clone, (2) Shapley values.
cd "$(dirname "$0")"
until grep -q "ALL DONE" data/java-run.log 2>/dev/null; do sleep 30; done
# (1) patched FB
cp java/build/classpath.txt java/build/classpath.orig.txt
cp java/build-patched/classpath.txt java/build/classpath.txt
MEASURES="fb" OUT=data/java-results-fb-patched.jsonl TIMEOUT=60000 ./run-java-parallel.sh
mv data/chunks data/chunks-C
cp java/build/classpath.orig.txt java/build/classpath.txt
# (2) Shapley on small KBs (original Java)
MEASURES="shapley:mi,shapley:mic,shapley:drastic,shapley:contension,shapley:eta,shapley:dalalsum,shapley:hs" IN=data/kbs-shapley.txt OUT=data/java-results-shapley.jsonl TIMEOUT=60000 ./run-java-parallel.sh
mv data/chunks data/chunks-D
echo EXTRA DONE
