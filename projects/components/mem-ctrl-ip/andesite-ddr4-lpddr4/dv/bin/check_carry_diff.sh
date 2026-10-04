#!/usr/bin/env bash
# Carry-diff gate: a carried andesite file may differ from its scoria source
# ONLY in the permitted carry lines -- module name, package import, header
# comments, and (Task-3 exception) explicitly added parameter ports.
# Usage: check_carry_diff.sh <andesite_file> <scoria_source> [exception_regex]
set -u
A="$1"; S="$2"; EXC="${3:-^$}"
fail=0
while IFS= read -r line; do
  case "$line" in
    ---* | +++*) continue ;;
  esac
  content="${line:1}"
  case "$content" in
    *scoria_pkg*|*andesite_pkg*) continue ;;
  esac
  if [[ "$line" == +* ]]; then
    if grep -qE "module andesite_|endmodule|Carried unchanged from scoria|Documentation:|andesite_pkg|Author:|Created:" <<<"$content"; then
      continue
    fi
    if grep -qE "$EXC" <<<"$content"; then
      continue
    fi
    echo "UNPERMITTED (+): $content"
    fail=1
  elif [[ "$line" == -* ]]; then
    if grep -qE "module scoria_|scoria_pkg|Documentation:|Author:|Created:" <<<"$content"; then
      continue
    fi
    echo "UNPERMITTED (-): $content"
    fail=1
  fi
done < <(diff -w "$S" "$A" || true)
if [[ "$fail" -ne 0 ]]; then
  echo "CARRY-DIFF GATE FAILED: $A"
  exit 1
fi
echo "carry-diff OK: $A"
