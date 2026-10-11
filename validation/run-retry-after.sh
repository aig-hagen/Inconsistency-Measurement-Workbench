#!/bin/sh
cd "$(dirname "$0")"
until grep -q "EXTRA DONE" data/java-extra.log 2>/dev/null; do sleep 30; done
node retry-java.cjs 60000 7 > data/java-retry.log 2>&1
