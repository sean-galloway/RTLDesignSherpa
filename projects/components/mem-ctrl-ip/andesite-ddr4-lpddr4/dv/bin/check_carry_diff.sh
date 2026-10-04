#!/usr/bin/env bash
# Carry-diff gate: a carried andesite file may differ from its scoria source
# ONLY in the permitted body differences -- module name, package import,
# endmodule label, in-set instantiation renames, and (recorded) exceptions.
# The header comment block (everything before the `timescale line) is
# free-form provenance and is not diffed.
# A fourth argument "additive" relaxes the +side: every added line is
# permitted (a declared growth), but every REMOVED line must still match
# the carry permits -- carry fidelity is "nothing scoria had was lost or
# altered"; the growth direction is the declared exception.
# Usage: check_carry_diff.sh <andesite_file> <scoria_source> [exception_regex] [additive]
set -u
A="$1"; S="$2"; EXC="${3:-^$}"; ADDITIVE="${4:-}"

body_of() {
    # everything from the first `timescale line onward
    awk '/`timescale/{f=1} f' "$1"
}

fail=0
while IFS= read -r line; do
  case "$line" in
    ---* | +++*) continue ;;
  esac
  content="${line:1}"
  if [[ "$line" == +* && -n "$ADDITIVE" ]]; then
    continue
  fi
  if [[ "$line" == +* || "$line" == -* ]]; then
    if grep -qE "andesite_pkg|scoria_pkg|module (andesite|scoria)_|endmodule" <<<"$content"; then
      continue
    fi
    # comment lines document logic but cannot change it; the fidelity
    # contract is about behavior, so comment deltas are permitted
    if grep -qE "^\\s*//" <<<"$content"; then
      continue
    fi
    # in-set instantiation renames: a bare module instantiation header
    if grep -qE "^\s*(andesite|scoria)_[a-z0-9_]+\s*#" <<<"$content"; then
      continue
    fi
    if grep -qE "$EXC" <<<"$content"; then
      continue
    fi
    echo "UNPERMITTED (${line:0:1}): $content"
    fail=1
  fi
done < <(diff -u -w <(body_of "$S") <(body_of "$A") || true)
if [[ "$fail" -ne 0 ]]; then
  echo "CARRY-DIFF GATE FAILED: $A"
  exit 1
fi
echo "carry-diff OK: $A"
