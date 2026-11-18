#!/usr/bin/env bash
# Orchestrator for box-v5: admits no step at or after box creation + 1h30 (created_at 2026-11-18T09:10:15.761Z).
set -u
CUT=$(date -d 2026-11-18T10:40:15Z +%s)
mkdir -p /home/ubuntu/rcpt
L=/home/ubuntu/rcpt/orchestrator.tsv
for v in CERTIFY_ALLOW_UNPINNED CERTIFY_REPLAY_TRUST_UPSTREAM CERTIFY_SKIP_BUILD CERTIFY_ALLOW_FOREIGN_SOLAR; do unset $v; done
export MEM_MAX=40G
[ "$(sha256sum /home/ubuntu/box-v5.sh | cut -d' ' -f1)" = 589e333c7b25e61e312a0c3c5d89af1ce9bbc04b3a8849100d1b8b50981cc174 ] || { echo script sha >> $L; exit 99; }
while IFS= read -r st; do
  if [ $(date +%s) -ge $CUT ]; then
    printf '%s\t%s\tOPEN\tnot admitted by creation+1h30\n' "$(date -u +%FT%TZ)" "$st" >> $L
    echo "{\"step\":\"$st\",\"status\":\"OPEN\",\"reason\":\"not admitted by box creation + 1h30\"}" >> /home/ubuntu/rcpt/steps-open.json
    continue
  fi
  printf '%s\t%s\tSTART\tbash box-v5.sh %s\n' "$(date -u +%FT%TZ)" "$st" "$st" >> $L
  bash /home/ubuntu/box-v5.sh $st > /home/ubuntu/rcpt/orch-$(echo $st | tr ' .' '__').log 2>&1
  printf '%s\t%s\tEXIT\t%s\n' "$(date -u +%FT%TZ)" "$st" "$?" >> $L
done <<'EOF'
0
6c
7
8
1
2
4 CounterRun.Lifecycle
EOF
printf '%s\tALL\tDONE\n' "$(date -u +%FT%TZ)" >> $L
