#!/usr/bin/env bash
# T6 heavy slot: at most one heavy job on this Hand at a time (flock), LEAN_NUM_THREADS=1.
#   slot.sh LABEL CMD...   -> logs to ~/t6/logs/LABEL.log, receipt to ~/t6/logs/LABEL.slot.json
set -uo pipefail
label=$1; shift
mkdir -p ~/t6/logs
export LEAN_NUM_THREADS=1 CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-2}
exec 9>~/t6/.heavy.lock
echo "slot: waiting for heavy slot ($label)" >&2
flock 9
echo "slot: acquired ($label) $(date -u +%FT%TZ)" >&2
exec python3 -I ~/t6/meter.py ~/t6/logs/$label "$@"
