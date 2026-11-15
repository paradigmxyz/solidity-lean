#!/usr/bin/env bash
# Compile lane E's shared modules (Measure, Toy, Stats) into ~/evalE/olean for Verify/Eval/E/run.sh.
set -euo pipefail
repo="$(cd "$(dirname "$0")/../../.." && pwd)"; cd "$repo"
[ -f "$HOME/env.sh" ] && source "$HOME/env.sh"
o="$HOME/evalE/olean"; mkdir -p "$o/Verify/Eval/Common" "$o/Verify/Eval/E"
export LEAN_PATH="$o:$(lake env printenv LEAN_PATH)"
for m in Common/Measure E/Toy E/Stats; do lean -o "$o/Verify/Eval/$m.olean" "Verify/Eval/$m.lean"; done
echo "lane E modules compiled into $o"
