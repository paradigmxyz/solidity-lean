#!/usr/bin/env bash
# Undo the publish-time home-path rewrite and check each file against its original sha256.
set -u
cd "$(dirname "$0")"
bad=0
while IFS=$'\t' read -r path orig committed writer transform; do
  case "$path" in ''|'#'*|path) continue;; esac
  got_c=$(sha256sum < "$path" | cut -c1-64)
  if [ "$transform" = home ]; then got_o=$(sed 's#~/#/home/hand/#g' "$path" | sha256sum | cut -c1-64); else got_o=$got_c; fi
  if [ "$got_c" = "$committed" ] && [ "$got_o" = "$orig" ]; then echo "ok   $path"; else echo "FAIL $path committed=$got_c original=$got_o"; bad=1; fi
done < MANIFEST.tsv
exit $bad
