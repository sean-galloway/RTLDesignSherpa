#!/usr/bin/env bash
set -euo pipefail

# ------------------------------------------------------------
# RAPIDS Beats HAS + MAS PDF Generator (convenience wrapper)
# ------------------------------------------------------------
# Usage:
#   ./generate_pdf.sh [--rev <version>] [--help]
#
# Example:
#   ./generate_pdf.sh --rev 0.6
#
# This is a convenience wrapper that runs both generate_has_pdf.sh
# and generate_mas_pdf.sh. Each per-document script applies the
# shared corporate styling (rapids_beats_*/rapids_beats_*_styles.yaml)
# so the RAPIDS docs render consistently with the STREAM HAS/MAS.
# Run the individual scripts directly to build a single document.
# ------------------------------------------------------------

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

show_help() {
  cat <<EOF
Usage: $0 [OPTIONS]

Options:
  -r, --rev <version>    Set document revision (passed to both scripts)
  -h, --help             Show this help message and exit

Example:
  $0 --rev 0.6

Description:
  Convenience wrapper that builds both the RAPIDS Beats HAS and MAS
  by invoking generate_has_pdf.sh and generate_mas_pdf.sh in turn.
EOF
}

# Handle --help locally; forward all other args verbatim to the per-doc scripts.
for arg in "$@"; do
  case "$arg" in
    -h|--help)
      show_help
      exit 0
      ;;
  esac
done

"${SCRIPT_DIR}/generate_has_pdf.sh" "$@"
"${SCRIPT_DIR}/generate_mas_pdf.sh" "$@"

echo "============================================================"
echo " PDF Generation Complete (HAS + MAS)"
echo "============================================================"
