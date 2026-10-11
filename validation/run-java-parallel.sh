#!/bin/sh
# Runs the Java harness on data/kbs.txt in parallel chunks; merges into data/java-results.jsonl
# (environment: MEASURES, CHUNKS, IN, OUT, TIMEOUT, CHUNKDIR, and CP_FILE for another build)
cd "$(dirname "$0")"
M=${MEASURES:-"drastic,mi,mic,nmi,nmic,pr,mc,nc,mv,df,is,mcsc,cc,csp,eta,contension,hs,dalalsum,dalalmax,dalalhit,pm,fb,pib,fuzzy:product:t,fuzzy:product:sum,fuzzy:min:t,fuzzy:min:sum,iceberg:identity,iceberg:conjuncts,iceberg:smallest_conjuncts,iceberg:classical,iceberg:classical:sum,iceberg:prime_implicants,iceberg:opposite_literals,contension_sat,hs_sat,dalalsum_sat,dalalmax_sat,dalalhit_sat"}
CHUNKS=${CHUNKS:-7}
IN=${IN:-data/kbs.txt}
OUT=${OUT:-data/java-results.jsonl}
TIMEOUT=${TIMEOUT:-10000}
CD=${CHUNKDIR:-data/chunks}
mkdir -p $CD
N=$(grep -c '^# kb' $IN)
SIZE=$(( (N + CHUNKS - 1) / CHUNKS ))
i=0
while [ $i -lt $CHUNKS ]; do
  S=$(( i * SIZE )); E=$(( S + SIZE ))
  awk -v s=$S -v e=$E '/^# kb/{k++} k>s && k<=e' $IN > $CD/kb-$i.txt
  node run-java.cjs $CD/kb-$i.txt $CD/out-$i.jsonl "$M" $TIMEOUT $S > $CD/log-$i.txt 2>&1 &
  i=$((i+1))
done
wait
cat $CD/out-*.jsonl > $OUT
echo "merged into $OUT"
