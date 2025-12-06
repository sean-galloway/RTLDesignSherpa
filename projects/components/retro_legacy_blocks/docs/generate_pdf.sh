#!/usr/bin/env bash
set -euo pipefail

# ============================================================
# RLB (Retro Legacy Blocks) Specification PDF Generator
# ============================================================
# Usage:
#   ./generate_pdf.sh [--rev <version>] [--component <name>] [--help]
#
# Examples:
#   ./generate_pdf.sh                     # All components, default version
#   ./generate_pdf.sh --rev 1.0           # All components, version 1.0
#   ./generate_pdf.sh --component gpio    # Only GPIO spec
#   ./generate_pdf.sh --component uart_16550 --rev 1.0
#
# This script builds RLB component specification documents
# (DOCX and PDF) from Markdown sources using md_to_docx.py.
# ============================================================

# Default revision
REV="1.0"

# Component filter (empty = all)
COMPONENT_FILTER=""

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
  -r, --rev <version>       Set document revision (default: ${REV})
  -c, --component <name>    Generate only specified component (default: all)
  -h, --help                Show this help message and exit

Examples:
  $0                        # Generate all components
  $0 --rev 1.0              # All components with version 1.0
  $0 -c gpio                # Only GPIO specification
  $0 -c uart_16550 -r 1.0   # UART 16550 spec, version 1.0

Description:
  This script generates DOCX and PDF versions of RLB component specifications
  by invoking the md_to_docx.py converter. It processes all enabled components
  and stitches together Markdown chapters with proper asset references.

Components (all enabled by default):
  Timers:
    - hpet        : High Precision Event Timer
    - pit_8254    : Programmable Interval Timer 8254

  Interrupt Controllers:
    - ioapic      : I/O Advanced Programmable Interrupt Controller
    - pic_8259    : Programmable Interrupt Controller 8259

  Peripherals:
    - gpio        : General Purpose I/O Controller
    - uart_16550  : 16550-Compatible UART
    - rtc         : Real-Time Clock
    - smbus       : SMBus/I2C Controller
    - pm_acpi     : ACPI Power Management

Output Files:
  For each component, generates:
    - APB_<NAME>_Specification_v<REV>.docx
    - APB_<NAME>_Specification_v<REV>.pdf
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
# ============================================================
# Format: "component_key:spec_dir:index_file:display_name:default_version"
#
# ALL RLB COMPONENTS:
COMPONENTS=(
  # Timers
  "hpet:hpet_spec:hpet_index.md:APB_HPET:1.0"
  "pit_8254:pit_8254_spec:pit_8254_index.md:APB_PIT_8254:1.0"

  # Interrupt Controllers
  "ioapic:ioapic_spec:ioapic_index.md:APB_IOAPIC:1.0"
  "pic_8259:pic_8259_spec:pic_8259_index.md:APB_PIC_8259:1.0"

  # Peripherals
  "gpio:gpio_spec:gpio_index.md:APB_GPIO:1.0"
  "uart_16550:uart_16550_spec:uart_16550_index.md:APB_UART_16550:1.0"
  "rtc:rtc_spec:rtc_index.md:APB_RTC:1.0"
  "smbus:smbus_spec:smbus_index.md:APB_SMBUS:1.0"
  "pm_acpi:pm_acpi_spec:pm_acpi_index.md:APB_PM_ACPI:1.0"
)

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
  IFS=':' read -r component_key spec_dir index_file display_name default_version <<< "$component_spec"

  # Check if we should process this component
  if [[ -n "$COMPONENT_FILTER" && "$component_key" != "$COMPONENT_FILTER" ]]; then
    skipped_count=$((skipped_count + 1))
    continue
  fi

  total_components=$((total_components + 1))

  if generate_component "$component_key" "$spec_dir" "$index_file" "$display_name" "$default_version"; then
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
    IFS=':' read -r component_key _ _ display_name _ <<< "$component_spec"
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

if [[ $error_count -eq 0 ]]; then
  echo "✅ All specifications generated successfully!"
  exit 0
else
  echo "⚠️  Some specifications failed to generate (see errors above)"
  exit 1
fi
