#!/usr/bin/env bash
set -euo pipefail

# ============================================================
# RLB (Retro Legacy Blocks) Specification PDF Generator
# ============================================================
# Usage:
#   ./generate_pdf.sh [--rev <version>] [--help]
#
# Examples:
#   ./generate_pdf.sh --rev 0.90
#   ./generate_pdf.sh --rev 1.0
#
# This script builds RLB component specification documents
# (DOCX and PDF) from Markdown sources using md_to_docx.py.
# ============================================================

# Default revision
REV="0.90"

# Detect repository root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="${REPO_ROOT:-$(cd "$SCRIPT_DIR/../../../.." && pwd)}"

# ============================================================
# Parse command line arguments
# ============================================================
show_help() {
  cat <<EOF
Usage: $0 [OPTIONS]

Options:
  -r, --rev <version>    Set document revision (default: ${REV})
  -h, --help             Show this help message and exit

Examples:
  $0 --rev 0.90
  $0 --rev 1.0

Description:
  This script generates DOCX and PDF versions of RLB component specifications
  by invoking the md_to_docx.py converter. It processes all enabled components
  and stitches together Markdown chapters with proper asset references.

Enabled Components:
  Edit the COMPONENTS array below to enable/disable specific components.
  Currently enabled: hpet, pit_8254

Available Components (see COMPONENTS array for full list):
  - hpet      : High Precision Event Timer
  - pit_8254  : Programmable Interval Timer 8254
  - ioapic    : I/O Advanced Programmable Interrupt Controller
  - pic_8259  : Programmable Interrupt Controller 8259
  - rtc       : Real-Time Clock
  - pm_acpi   : ACPI Power Management
  - smbus     : SMBus/I2C Controller
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
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

# ============================================================
# Component Configuration
# ============================================================
# Format: "component_key:spec_dir:index_file:display_name:default_version"
#
# ACTIVE COMPONENTS (uncommented):
COMPONENTS=(
  "hpet:hpet_spec:hpet_index.md:APB_HPET:0.90"
  "pit_8254:pit_8254_spec:pit_8254_index.md:APB_PIT_8254:0.90"
)

# AVAILABLE COMPONENTS (commented out - uncomment to enable):
# COMPONENTS+=(
#   "ioapic:ioapic_spec:ioapic_index.md:APB_IOAPIC:0.90"
#   "pic_8259:pic_8259_spec:pic_8259_index.md:APB_PIC_8259:0.90"
#   "rtc:rtc_spec:rtc_index.md:APB_RTC:0.90"
#   "pm_acpi:pm_acpi_spec:pm_acpi_index.md:APB_PM_ACPI:0.90"
#   "smbus:smbus_spec:smbus_index.md:APB_SMBUS:0.90"
# )

# ============================================================
# Generate single component
# ============================================================
generate_component() {
  local component_key=$1
  local spec_dir=$2
  local index_file=$3
  local display_name=$4
  local default_version=$5

  # Use provided revision or component default
  local version="${REV:-${default_version}}"

  # Build paths
  local spec_index="${spec_dir}/${index_file}"
  local assets="${spec_dir}/assets"
  local output_basename="${display_name}_Specification_v${version}"
  local output_docx="${output_basename}.docx"
  local output_pdf="${output_basename}.pdf"

  # Check if spec index exists
  if [[ ! -f "$spec_index" ]]; then
    echo "⚠️  WARNING: Spec index not found: $spec_index (skipping ${display_name})"
    echo
    return 0
  fi

  # Print header
  echo "============================================================"
  echo " Generating ${display_name} Specification"
  echo "============================================================"
  echo "  Component:   ${component_key}"
  echo "  Version:     ${version}"
  echo "  Input:       ${spec_index}"
  echo "  Assets:      ${assets}"
  echo "  Output:      ${output_docx}"
  echo "              ${output_pdf}"
  echo "  Repo Root:   ${REPO_ROOT}"
  echo "============================================================"
  echo

  # Build asset directory arguments
  # Check which asset subdirectories exist and add them
  local asset_args=()

  if [[ -d "${assets}" ]]; then
    asset_args+=("--assets-dir" "${assets}")

    # Add subdirectories if they exist
    for subdir in svg graphviz puml wavedrom waves diagrams images draw.io; do
      if [[ -d "${assets}/${subdir}" ]]; then
        asset_args+=("--assets-dir" "${assets}/${subdir}")
      fi
    done
  else
    echo "⚠️  WARNING: Assets directory not found: ${assets}"
    echo "   Continuing without assets..."
    echo
  fi

  # Run converter
  if python3 "$REPO_ROOT/bin/md_to_docx.py" \
    --expand-index \
    --toc \
    --pagebreak \
    --title-page \
    --pdf \
    --pdf-engine=lualatex \
    --mainfont "Noto Serif" \
    --monofont "Noto Sans Mono" \
    --sansfont "Noto Sans" \
    --mathfont "Noto Serif" \
    "${asset_args[@]}" \
    "${spec_index}" \
    "${output_docx}" 2>&1 | grep -v "Missing required argument: input" | grep -v "^Options:$" | grep -v "^  -" | grep -v "^      --" || true
  then
    echo
    echo "✅ Done: Generated ${output_docx} and ${output_pdf}"
    echo
  else
    echo
    echo "❌ ERROR: Failed to generate ${display_name} specification"
    echo
    return 1
  fi
}

# ============================================================
# Main execution
# ============================================================
echo
echo "============================================================"
echo " RLB Specification PDF Generator"
echo "============================================================"
echo "  Revision:    ${REV}"
echo "  Components:  ${#COMPONENTS[@]} enabled"
echo "============================================================"
echo

# Track statistics
total_components=${#COMPONENTS[@]}
success_count=0
error_count=0

# Process each component
for component_spec in "${COMPONENTS[@]}"; do
  # Parse component specification
  IFS=':' read -r component_key spec_dir index_file display_name default_version <<< "$component_spec"

  if generate_component "$component_key" "$spec_dir" "$index_file" "$display_name" "$default_version"; then
    success_count=$((success_count + 1))
  else
    error_count=$((error_count + 1))
  fi
done

# Print summary
echo "============================================================"
echo " Generation Summary"
echo "============================================================"
echo "  Total components:  ${total_components}"
echo "  Successful:        ${success_count}"
echo "  Failed:            ${error_count}"
echo "============================================================"
echo

if [[ $error_count -eq 0 ]]; then
  echo "✅ All specifications generated successfully!"
  exit 0
else
  echo "⚠️  Some specifications failed to generate (see errors above)"
  exit 1
fi
