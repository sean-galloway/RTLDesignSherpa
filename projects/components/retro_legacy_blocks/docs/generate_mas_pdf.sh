#!/usr/bin/env bash
set -euo pipefail

# ============================================================
# RLB (Retro Legacy Blocks) MAS PDF Generator
# ============================================================
# Usage:
#   ./generate_mas_pdf.sh [--component <name>] [--help]
#
# Examples:
#   ./generate_mas_pdf.sh                     # All MAS documents
#   ./generate_mas_pdf.sh --component gpio    # Only GPIO MAS
#
# This script builds RLB component MAS documents
# (DOCX and PDF) from Markdown sources using md_to_docx.py.
# ============================================================

# Component filter (empty = all)
COMPONENT_FILTER=""

# Detect repository root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="${REPO_ROOT:-$(cd "$SCRIPT_DIR/../../../.." && pwd)}"
SHARED_ASSETS="$SCRIPT_DIR/shared_assets"

# ============================================================
# Parse command line arguments
# ============================================================
show_help() {
  cat <<EOF
Usage: $0 [OPTIONS]

Options:
  -c, --component <name>    Generate only specified component (default: all)
  -h, --help                Show this help message and exit

Examples:
  $0                        # Generate all MAS documents
  $0 -c gpio                # Only GPIO MAS

MAS Components:
  - gpio        : General Purpose I/O Controller
  - hpet        : High Precision Event Timer
  - ioapic      : I/O Advanced Programmable Interrupt Controller
  - pic_8259    : Programmable Interrupt Controller 8259
  - pit_8254    : Programmable Interval Timer 8254
  - pm_acpi     : ACPI Power Management
  - rtc         : Real-Time Clock
  - smbus       : SMBus/I2C Controller
  - uart_16550  : 16550-Compatible UART

Output Files:
  For each component, generates:
    - <NAME>_MAS_v1.0.docx
    - <NAME>_MAS_v1.0.pdf
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -c|--component)
      COMPONENT_FILTER="${2:-}"
      if [[ -z "$COMPONENT_FILTER" ]]; then
        echo "Error: Missing value for --component" >&2
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
# Format: "component_key:mas_dir:index_file:display_name"
# ============================================================
COMPONENTS=(
  "gpio:gpio_mas:gpio_mas_index.md:GPIO"
  "hpet:hpet_mas:hpet_mas_index.md:HPET"
  "ioapic:ioapic_mas:ioapic_mas_index.md:IOAPIC"
  "pic_8259:pic_8259_mas:pic_8259_mas_index.md:PIC_8259"
  "pit_8254:pit_8254_mas:pit_8254_mas_index.md:PIT_8254"
  "pm_acpi:pm_acpi_mas:pm_acpi_mas_index.md:PM_ACPI"
  "rtc:rtc_mas:rtc_mas_index.md:RTC"
  "smbus:smbus_mas:smbus_mas_index.md:SMBUS"
  "uart_16550:uart_16550_mas:uart_16550_mas_index.md:UART_16550"
)

# ============================================================
# Generate single component
# ============================================================
generate_component() {
  local component_key=$1
  local mas_dir=$2
  local index_file=$3
  local display_name=$4

  # Build paths
  local mas_index="${mas_dir}/${index_file}"
  local styles_file="${mas_dir}/${component_key}_mas_styles.yaml"
  local assets="${mas_dir}/assets"
  local output_basename="${display_name}_MAS_v1.0"
  local output_docx="${output_basename}.docx"
  local output_pdf="${output_basename}.pdf"

  # Check if MAS directory exists
  if [[ ! -d "$mas_dir" ]]; then
    echo "WARNING: MAS directory not found: $mas_dir (skipping ${display_name})"
    echo
    return 0
  fi

  # Check if spec index exists
  if [[ ! -f "$mas_index" ]]; then
    echo "WARNING: MAS index not found: $mas_index (skipping ${display_name})"
    echo
    return 0
  fi

  # Check for styles file
  if [[ ! -f "$styles_file" ]]; then
    echo "ERROR: Styles file not found: $styles_file"
    echo "Copy from: shared_assets/rlb_mas_styles_template.yaml"
    return 1
  fi

  # Check for logo
  if [[ ! -f "$assets/images/logo.png" ]]; then
    echo "ERROR: Logo not found: $assets/images/logo.png"
    echo "Copy from: shared_assets/images/logo.png"
    return 1
  fi

  # Print header
  echo "============================================================"
  echo " Generating ${display_name} MAS"
  echo "============================================================"
  echo "  Component:   ${component_key}"
  echo "  Input:       ${mas_index}"
  echo "  Styles:      ${styles_file}"
  echo "  Assets:      ${assets}"
  echo "  Output:      ${output_docx}"
  echo "============================================================"
  echo

  # Run converter with ALL mandatory options
  if python3 "$REPO_ROOT/bin/md_to_docx.py" \
    "$mas_index" \
    "$output_docx" \
    --style "$styles_file" \
    --expand-index \
    --skip-index-content \
    --toc \
    --number-sections \
    --title-page \
    --pdf \
    --lof \
    --lot \
    --low \
    --pagebreak \
    --narrow-margins \
    --pdf-engine=lualatex \
    --mainfont "Noto Serif" \
    --monofont "Noto Sans Mono" \
    --sansfont "Noto Sans" \
    --mathfont "Noto Serif" \
    --assets-dir "$assets" \
    --assets-dir "$assets/images" \
    --assets-dir "$assets/mermaid" \
    --assets-dir "$assets/wavedrom" \
    --quiet 2>&1
  then
    echo
    echo "Done: Generated ${output_docx} and ${output_pdf}"
    echo
  else
    echo
    echo "ERROR: Failed to generate ${display_name} MAS"
    echo
    return 1
  fi
}

# ============================================================
# Main execution
# ============================================================
echo
echo "============================================================"
echo " RLB MAS PDF Generator"
echo "============================================================"
if [[ -n "$COMPONENT_FILTER" ]]; then
  echo "  Component:   ${COMPONENT_FILTER} (filtered)"
else
  echo "  Components:  ${#COMPONENTS[@]} available"
fi
echo "============================================================"
echo

# Track statistics
total_components=0
success_count=0
error_count=0
skipped_count=0

# Process each component
for component_spec in "${COMPONENTS[@]}"; do
  # Parse component specification
  IFS=':' read -r component_key mas_dir index_file display_name <<< "$component_spec"

  # Check if we should process this component
  if [[ -n "$COMPONENT_FILTER" && "$component_key" != "$COMPONENT_FILTER" ]]; then
    skipped_count=$((skipped_count + 1))
    continue
  fi

  total_components=$((total_components + 1))

  if generate_component "$component_key" "$mas_dir" "$index_file" "$display_name"; then
    success_count=$((success_count + 1))
  else
    error_count=$((error_count + 1))
  fi
done

# Check if component filter didn't match anything
if [[ -n "$COMPONENT_FILTER" && $total_components -eq 0 ]]; then
  echo "ERROR: Component '${COMPONENT_FILTER}' not found."
  echo
  echo "Available components:"
  for component_spec in "${COMPONENTS[@]}"; do
    IFS=':' read -r component_key _ _ display_name <<< "$component_spec"
    echo "  - ${component_key} (${display_name})"
  done
  exit 1
fi

# Print summary
echo "============================================================"
echo " Generation Summary"
echo "============================================================"
echo "  Total components:  ${total_components}"
echo "  Successful:        ${success_count}"
echo "  Failed:            ${error_count}"
echo "============================================================"
echo

if [[ $error_count -eq 0 && $success_count -gt 0 ]]; then
  echo "All MAS documents generated successfully!"
  exit 0
elif [[ $success_count -eq 0 ]]; then
  echo "No MAS documents generated (directories may not exist yet)"
  exit 0
else
  echo "Some MAS documents failed to generate (see errors above)"
  exit 1
fi
