#!/bin/sh
# Pass A: all measures except Iceberg (timeout 10s); Pass B: Iceberg variants (timeout 5s)
cd "$(dirname "$0")"
MEASURES="drastic,mi,mic,nmi,nmic,pr,mc,nc,mv,df,is,mcsc,cc,csp,eta,contension,hs,dalalsum,dalalmax,dalalhit,pm,fb,pib,fuzzy:product:t,fuzzy:product:sum,fuzzy:min:t,fuzzy:min:sum,contension_sat,hs_sat,dalalsum_sat,dalalmax_sat,dalalhit_sat" \
  OUT=data/java-results.jsonl TIMEOUT=10000 ./run-java-parallel.sh
mv data/chunks data/chunks-A
MEASURES="iceberg:identity,iceberg:conjuncts,iceberg:smallest_conjuncts,iceberg:classical,iceberg:classical:sum,iceberg:prime_implicants,iceberg:opposite_literals" \
  OUT=data/java-results-iceberg.jsonl TIMEOUT=5000 ./run-java-parallel.sh
mv data/chunks data/chunks-B
echo ALL DONE
