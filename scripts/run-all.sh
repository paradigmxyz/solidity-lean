#!/usr/bin/env bash
# Orchestrator: run box-v4.sh steps in the admitted order; admit no step after 1h30 from box creation.
set -u
CUT=$(date -d 2026-11-18T08:20:00Z +%s)   # box created 2026-11-18T06:50:00Z
mkdir -p /home/ubuntu/rcpt
L=/home/ubuntu/rcpt/orchestrator.tsv
for v in CERTIFY_ALLOW_UNPINNED CERTIFY_REPLAY_TRUST_UPSTREAM CERTIFY_SKIP_BUILD CERTIFY_ALLOW_FOREIGN_SOLAR; do unset $v; done
export MEM_MAX=40G
while IFS= read -r st; do
  now=$(date +%s)
  if [ $now -ge $CUT ]; then
    printf '%s\t%s\tOPEN\tnot admitted by 1h30\n' "$(date -u +%FT%TZ)" "$st" >> $L
    echo "{\"step\":\"$st\",\"status\":\"OPEN\",\"reason\":\"not admitted by 1h30 from box creation\"}" >> /home/ubuntu/rcpt/steps-open.json
    continue
  fi
  printf '%s\t%s\tSTART\tbash box-v4.sh %s\n' "$(date -u +%FT%TZ)" "$st" "$st" >> $L
  bash /home/ubuntu/box-v4.sh $st > /home/ubuntu/rcpt/orch-$(echo $st | tr ' .' '__').log 2>&1
  rc=$?
  printf '%s\t%s\tEXIT\t%s\n' "$(date -u +%FT%TZ)" "$st" "$rc" >> $L
done <<'EOF'
0
3d
1
3
4 Verify.LoopSource.Equiv.Counter.Resources Verify.LoopSource.Equiv.Counter.Neg
6
6c
7
8
2
4 CounterRun.Lifecycle
5
EOF
printf '%s\tALL\tDONE\n' "$(date -u +%FT%TZ)" >> $L
