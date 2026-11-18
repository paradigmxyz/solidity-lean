#!/usr/bin/env bash
# Dispatcher installed at the admitted switch: steps after 6 run from box-v4-fix.sh (f337f161).
# 6c runs a full step 1 under the fix first, then 6c; both exits go to rcpt/switch-steps.tsv.
L=/home/ubuntu/rcpt/switch-steps.tsv
F=/home/ubuntu/box-v4-fix.sh
[ "$(sha256sum $F | cut -d' ' -f1)" = f337f1617141c4d1d987b6b2a0710cf17bd9414ede500961f00113e1d4792f4a ] || { echo "fix sha"; exit 99; }
run() { printf '%s\t%s\tSTART\tbash box-v4-fix.sh %s\n' "$(date -u +%FT%TZ)" "$*" "$*" >> $L
  bash $F "$@"; rc=$?; printf '%s\t%s\tEXIT\t%s\n' "$(date -u +%FT%TZ)" "$*" "$rc" >> $L; return $rc; }
if [ "$1" = 6c ]; then run 1 > /home/ubuntu/rcpt/orch-1-fix.log 2>&1; run 6c; exit $?; fi
run "$@"
