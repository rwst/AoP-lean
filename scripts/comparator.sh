#!/usr/bin/env bash
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# Released under CC0 1.0 Universal (public-domain dedication).
# See https://creativecommons.org/publicdomain/zero/1.0/
#
# Run `lake comparator` on every brief's lane, or on the named briefs only, one after another.
# A rejection does not stop the run: every lane reports, and the exit code is 1 if any failed.
#
#   scripts/comparator.sh                     every briefs/*/comparator/comparator.json
#   scripts/comparator.sh BornRuleEntropy     one lane
#
# `LEAN_NUM_THREADS` defaults to 3. See COMPARATOR.md.

set -uo pipefail

cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-3}"

if [ $# -gt 0 ]; then
  configs=()
  for b in "$@"; do configs+=("briefs/$b/comparator/comparator.json"); done
else
  configs=(briefs/*/comparator/comparator.json)
fi

failed=()
for cfg in "${configs[@]}"; do
  echo "=== lake comparator --config $cfg"
  if [ ! -f "$cfg" ]; then
    echo "comparator.sh: no such config: $cfg" >&2
    failed+=("$cfg")
  elif ! lake comparator --config "$cfg"; then
    failed+=("$cfg")
  fi
done

if [ ${#failed[@]} -gt 0 ]; then
  echo "comparator.sh: rejected: ${failed[*]}" >&2
  exit 1
fi
echo "comparator.sh: accepted ${#configs[@]} of ${#configs[@]} lane(s)"
