#!/usr/bin/env bash
# Orchestrator for a T4 box session: runs SCRIPT's steps in order and starts no step at or after
# box creation + 1h30. The EXIT column is each step's own exit.
# Usage: CREATED_AT=<box created_at, ISO 8601> SCRIPT=/home/ubuntu/box-v6.sh SCRIPT_SHA=<sha256> run-all.sh STEP...
#   Each STEP argument is one step with its modules, such as "4 CounterRun.Lifecycle".
set -u
: "${CREATED_AT:?}" "${SCRIPT:?}" "${SCRIPT_SHA:?}"
CUT=$(( $(date -d "$CREATED_AT" +%s) + 5400 ))
R=/home/ubuntu/rcpt; L=$R/orchestrator.tsv
mkdir -p $R
for v in $(env | sed -n 's/^\(CERTIFY_ALLOW_[A-Za-z0-9_]*\)=.*/\1/p'); do unset "$v"; done
export MEM_MAX=40G
printf 'created_at\t%s\tcut\t%s\n' "$CREATED_AT" "$(date -u -d @$CUT +%FT%TZ)" >> $L
[ "$(sha256sum "$SCRIPT" | cut -d' ' -f1)" = "$SCRIPT_SHA" ] || { printf 'script sha mismatch\n' >> $L; exit 99; }
for st in "$@"; do
  if [ "$(date +%s)" -ge $CUT ]; then
    printf '%s\t%s\tOPEN\tnot admitted by box creation + 1h30\n' "$(date -u +%FT%TZ)" "$st" >> $L
    printf '{"step":"%s","status":"OPEN","reason":"not admitted by box creation + 1h30"}\n' "$st" >> $R/steps-open.json
    continue
  fi
  printf '%s\t%s\tSTART\tbash %s %s\n' "$(date -u +%FT%TZ)" "$st" "$SCRIPT" "$st" >> $L
  # shellcheck disable=SC2086 # a step and its modules are separate arguments
  bash "$SCRIPT" $st > "$R/orch-$(printf '%s' "$st" | tr ' .' '__').log" 2>&1
  rc=$?
  printf '%s\t%s\tEXIT\t%s\n' "$(date -u +%FT%TZ)" "$st" "$rc" >> $L
done
printf '%s\tALL\tDONE\n' "$(date -u +%FT%TZ)" >> $L
