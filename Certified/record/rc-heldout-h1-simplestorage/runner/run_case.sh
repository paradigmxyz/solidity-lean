#!/usr/bin/env bash
# run_case.sh ID REL_SOURCE CONTRACT [extra certify args...]  (run inside slot.sh)
set -uo pipefail
export PATH=~/.elan/bin:$PATH
id=$1; src=~/t6/heldout/$2; contract=$3; shift 3
cd ~/t6/solar
PIN=${T6_PIN:-800d78a98b9e64612c742d5038e7e2ec35dd52b4}
if [ "$(git rev-parse HEAD)" != "$PIN" ]; then git checkout -q "$PIN" || exit 99; cargo build --locked --bin solar || exit 98; fi
test -z "$(git status --porcelain)" || { echo DIRTY; exit 97; }
echo "driver $(git rev-parse HEAD) tree $(git rev-parse HEAD^{tree}) dirty=[$(git status --porcelain -- crates scripts tools/certify Cargo.toml Cargo.lock)]"
echo "source $(sha256sum "$src")"
rm -rf ~/t6/runs/$id ~/t6/runs/$id-work; mkdir -p ~/t6/runs
tools/certify/certify "$src" natspec --contract "$contract" --solidity-lean ~/t6/solidity-lean \
  --base 44572c150176365fa5e0d56ae6c59a7a443f8122 --work ~/t6/runs/$id-work --record-dir ~/t6/runs/$id \
  --packages-from ~/t6/solidity-lean --probe-cache ~/t6/solidity-lean "$@"
rc=$?; echo "CERTIFY_EXIT $rc"; exit $rc
