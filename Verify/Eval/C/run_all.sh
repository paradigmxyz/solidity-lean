#!/usr/bin/env bash
# Lane C: everything after the stepper, one check.sh slot at a time.
cd "$(dirname "$0")/../../.."
log="$HOME/eval-c-master.log"
echo "=== start $(date -u)" >> "$log"
scripts/eval/check.sh C Verify/Eval/C/Stepper.lean -o .lake/build/lib/lean/Verify/Eval/C/Stepper.olean 2>&1 | grep -A8 error >> "$log"
scripts/eval/check.sh C Verify/Eval/C/Isolation.lean 2>&1 | grep -v '^\s\s*[a-z].*s$' >> "$log"
scripts/eval/check.sh C Verify/Eval/C/GenC1.lean -Dverify.eval.c.stats=true -Dverify.eval.c.debug=true 2>&1 | grep -v '^\s\s*[a-z].*s$' >> "$log"
SIZES="64 128 256" Verify/Eval/C/run_fixtures.sh Branch >> "$log" 2>&1
SIZES="32" Verify/Eval/C/run_fixtures.sh Branch >> "$log" 2>&1
echo "=== done $(date -u)" >> "$log"
