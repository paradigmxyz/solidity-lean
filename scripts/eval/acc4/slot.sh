#!/usr/bin/env bash
# One heavy Lean job at a time on this Hand: flock on a single lock, LEAN_NUM_THREADS=1.
export LEAN_NUM_THREADS=1
exec flock ~/bench/heavy.lock "$@"
