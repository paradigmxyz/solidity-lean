#!/usr/bin/env bash
# Assemble Flag's certified modules (rc2-acc5-flag) into Certified/flag_4ce5cf9a from the
# immutable record commit, and check every file against FLAG_RECORD.sha256 and against the
# record's own MANIFEST.sha256 at that commit. Fails closed: exit 3 on any mismatch, extra or
# missing file. Never builds, never regenerates, never runs certify.
#
# usage: Verify/SourceText/flag_record.sh [REMOTE]   (REMOTE defaults to origin)
set -euo pipefail
cd "$(dirname "$0")/../.."
remote=${1:-origin}
commit=abcd096127559797224a4fdf330dd3476c65b79c   # chore(certified): record rc2-acc5-flag on solar 0479b90a
record=Certified/record/rc2-acc5-flag
pins=Verify/SourceText/FLAG_RECORD.sha256
dest=Certified/flag_4ce5cf9a

git cat-file -e "$commit^{commit}" 2>/dev/null || git fetch -q "$remote" "$commit"
[ "$(git rev-parse "$commit^{commit}")" = "$commit" ] || { echo "record commit $commit not found" >&2; exit 3; }

# The record's own manifest at the commit must list exactly the pinned files and hashes.
diff <(git show "$commit:$record/MANIFEST.sha256" | grep '  generated/Certified/flag_4ce5cf9a/' | sed 's#  generated/#  #' | sort -k2) \
     <(sort -k2 "$pins") >/dev/null || { echo "the record's MANIFEST.sha256 differs from $pins" >&2; exit 3; }

if [ ! -e "$dest" ]; then
  tmp=$(mktemp -d)
  git archive "$commit" "$record/generated/$dest" | tar -x -C "$tmp"
  mv "$tmp/$record/generated/$dest" "$dest"
  rm -rf "$tmp"
fi
# Exactly the pinned files, each with its pinned hash.
diff <(find "$dest" -type f | sort) <(awk '{print $2}' "$pins" | sort) >/dev/null || { echo "$dest's file set differs from $pins" >&2; exit 3; }
sha256sum -c --quiet "$pins" || exit 3
echo "assembled $dest from $commit: $(wc -l < "$pins") files match"
