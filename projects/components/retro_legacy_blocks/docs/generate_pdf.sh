#!/usr/bin/env bash
set -euo pipefail

# ------------------------------------------------------------
# RLB Spec PDF Generator
# ------------------------------------------------------------
# Usage:
#   ./generate_pdf.sh [--component <name>] [--rev <version>] [--help]
#
# Example:
#   ./generate_pdf.sh --component hpet --rev 0.27
#   ./generate_pdf.sh --component pit_8254 --rev 1.0
#   ./generate_pdf.sh --component all
#
# This script builds RLB component specification documents
# (DOCX and PDF) from Markdown sources using md_to_docx.py.
# ------------------------------------------------------------

# Default values
COMPONENT="hpet"
REV=""

# ------------------------------------------------------------
# Parse command line arguments
# ------------------------------------------------------------
show_help() {
  cat <<EOF
Usage: $0 [OPTIONS]

Options:
  -c, --component <name> Component to build (hpet, pit_8254, all)
  -r, --rev <version>    Set document revision (component-specific defaults used if not specified)
  -h, --help             Show this help message and exit

Examples:
  $0 --component hpet --rev 0.27
  $0 --component pit_8254 --rev 1.0
  $0 --component all

Description:
  This script generates DOCX and PDF versions of RLB component specifications
  by invoking the md_to_docx.py converter. It stitches together the Markdown
  chapters, applies page breaks, and includes assets for images and diagrams.

Available Components:
  - hpet      : High Precision Event Timer
  - pit_8254  : Programmable Interval Timer 8254
  - all       : Generate all component specifications
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -c|--component)
      COMPONENT="${2:-}"
      if [[ -z "$COMPONENT" ]]; then
        echo "Error: Missing value for --component" >&2
        exit 1
      fi
      shift 2
      ;;
    -r|--rev)
      REV="${2:-}"
      if [[ -z "$REV" ]]; then
        echo "Error: Missing value for --rev" >&2
        exit 1
      fi
      shift 2
      ;;
    -h|--help)
      show_help
      exit 0
      ;;
    *)
      echo "Error: Unknown argument '$1'" >&2
      echo "Use '$0 --help' for usage."
      exit 1
      ;;
  esac
done

# ------------------------------------------------------------
# Component-specific configuration
# ------------------------------------------------------------
generate_component() {
  local component=$1
  local version=$2
  local assets=""
  local spec_index=""
  local component_name=""

  case "$component" in
    hpet)
      assets="hpet_spec/assets"
      spec_index="hpet_spec/hpet_index.md"
      component_name="APB_HPET"
      [[ -z "$version" ]] && version="0.25"
      ;;
    pit_8254)
      assets="pit_8254_spec/assets"
      spec_index="pit_8254_spec/pit_8254_index.md"
      component_name="APB_PIT_8254"
      [[ -z "$version" ]] && version="1.0"
      ;;
    *)
      echo "Error: Unknown component '$component'" >&2
      echo "Supported components: hpet, pit_8254, all" >&2
      exit 1
      ;;
  esac

  # Build filenames
  local output_basename="${component_name}_Specification_v${version}"
  local output_docx="${output_basename}.docx"
  local output_pdf="${output_basename}.pdf"

  # Run converter
  echo "------------------------------------------------------------"
  echo " Generating ${component_name} Specification"
  echo "------------------------------------------------------------"
  echo "  Version: ${version}"
  echo "  Input:   ${spec_index}"
  echo "  Assets:  ${assets}"
  echo "  Output:  ${output_docx} (and ${output_pdf})"
  echo "------------------------------------------------------------"

  python3 "$REPO_ROOT/bin/md_to_docx.py" \
    --expand-index --toc --pagebreak --title-page --pdf \
    --pdf-engine=lualatex \
    --mainfont "Noto Serif" \
    --monofont "Noto Sans Mono" \
    --sansfont "Noto Sans" \
    --mathfont "Noto Serif" \
    --assets-dir "${assets}" \
    "${spec_index}" "${output_docx}"

  echo
  echo "✅ Done: Generated ${output_docx} and ${output_pdf}"
  echo
}

# ------------------------------------------------------------
# Main execution
# ------------------------------------------------------------
if [[ "$COMPONENT" == "all" ]]; then
  generate_component "hpet" "${REV}"
  generate_component "pit_8254" "${REV}"
else
  generate_component "$COMPONENT" "${REV}"
fi

