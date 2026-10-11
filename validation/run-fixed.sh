#!/bin/sh
# Validation against the TweetyProject sources with the bugs fixed (compiled with
# OUT=validation/java/build-fixed validation/java/compile.sh): the 1000 knowledge
# bases of data/kbs.txt and the 300 bases with exclusive or of data/kbs-xor.txt.
cd "$(dirname "$0")"
export CP_FILE=java/build-fixed/classpath.txt
MAIN="drastic,mi,mic,nmi,nmic,pr,mc,nc,mv,df,is,mcsc,cc,csp,eta,contension,hs,dalalsum,dalalmax,dalalhit,pm,fb,pib,fuzzy:product:t,fuzzy:product:sum,fuzzy:min:t,fuzzy:min:sum,contension_sat,hs_sat,dalalsum_sat,dalalmax_sat,dalalhit_sat"
ICE="iceberg:identity,iceberg:conjuncts,iceberg:smallest_conjuncts,iceberg:classical,iceberg:classical:sum,iceberg:prime_implicants,iceberg:opposite_literals,iceberg:modus_ponens"
MEASURES=$MAIN OUT=data/java-results-fixed.jsonl TIMEOUT=10000 CHUNKDIR=data/chunks-fixed ./run-java-parallel.sh
MEASURES=$ICE OUT=data/java-results-fixed-iceberg.jsonl TIMEOUT=5000 CHUNKDIR=data/chunks-fixed-ice ./run-java-parallel.sh
IN=data/kbs-xor.txt MEASURES="$MAIN,$ICE" OUT=data/java-results-fixed-xor.jsonl TIMEOUT=10000 CHUNKDIR=data/chunks-fixed-xor ./run-java-parallel.sh
echo ALL DONE
