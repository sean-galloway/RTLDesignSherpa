#!/usr/bin/env python3
"""
yosys_to_nand_equiv.py - Convert Yosys netlist statistics to NAND-equivalent gate count

This script parses Yosys synthesis output (from 'stat' command) and converts
the cell counts to approximate NAND-2 gate equivalents for standardized
area comparison.

Usage:
    # Pipe Yosys output directly:
    yosys -p "read_verilog design.v; synth; stat" | python3 yosys_to_nand_equiv.py

    # Or from a log file:
    python3 yosys_to_nand_equiv.py yosys_output.log

    # Run Yosys synthesis and convert in one command:
    python3 yosys_to_nand_equiv.py --run "read_verilog design.v; synth; stat"

Author: seang
Date: 2025-12-28
"""

import sys
import re
import argparse
import subprocess
from typing import Dict, Tuple

# NAND-2 equivalent gate counts for common Yosys cell types
# These are approximate values based on standard cell library implementations
NAND_EQUIVALENTS = {
    # Basic gates
    '$_NOT_': 1,           # Inverter = 1 NAND (with tied inputs)
    '$_BUF_': 2,           # Buffer = 2 inverters
    '$_AND_': 2,           # AND = NAND + NOT
    '$_NAND_': 1,          # NAND = 1 NAND
    '$_OR_': 3,            # OR = 2 NOTs + NAND (DeMorgan)
    '$_NOR_': 2,           # NOR = OR + NOT, but direct impl ~2
    '$_XOR_': 4,           # XOR = 4 NAND gates
    '$_XNOR_': 5,          # XNOR = XOR + NOT
    '$_ANDNOT_': 2,        # AND-NOT = ~2 NAND
    '$_ORNOT_': 3,         # OR-NOT = ~3 NAND

    # Complex gates (AND-OR-Invert, OR-AND-Invert)
    '$_AOI3_': 3,          # 2-input AND into 2-input NOR
    '$_OAI3_': 3,          # 2-input OR into 2-input NAND
    '$_AOI4_': 4,          # 2x 2-input AND into 2-input NOR
    '$_OAI4_': 4,          # 2x 2-input OR into 2-input NAND

    # Multiplexers
    '$_MUX_': 4,           # 2:1 MUX = ~4 NAND
    '$_NMUX_': 4,          # Inverted MUX = ~4 NAND
    '$_MUX4_': 12,         # 4:1 MUX = ~12 NAND
    '$_MUX8_': 28,         # 8:1 MUX = ~28 NAND
    '$_MUX16_': 60,        # 16:1 MUX = ~60 NAND

    # Flip-flops and latches
    '$_DFF_P_': 6,         # D flip-flop (pos edge) = ~6 NAND
    '$_DFF_N_': 6,         # D flip-flop (neg edge) = ~6 NAND
    '$_DFF_PP0_': 8,       # DFF with async reset = ~8 NAND
    '$_DFF_PP1_': 8,       # DFF with async set = ~8 NAND
    '$_DFF_PN0_': 8,       # DFF variants
    '$_DFF_PN1_': 8,
    '$_DFF_NP0_': 8,
    '$_DFF_NP1_': 8,
    '$_DFF_NN0_': 8,
    '$_DFF_NN1_': 8,
    '$_DFFE_PP_': 8,       # DFF with enable = ~8 NAND
    '$_DFFE_PN_': 8,
    '$_DFFE_NP_': 8,
    '$_DFFE_NN_': 8,
    '$_DLATCH_P_': 4,      # D latch = ~4 NAND
    '$_DLATCH_N_': 4,
    '$_SR_PP_': 4,         # SR latch = ~4 NAND
    '$_SR_PN_': 4,
    '$_SR_NP_': 4,
    '$_SR_NN_': 4,

    # Tri-state
    '$_TBUF_': 4,          # Tri-state buffer = ~4 NAND equiv

    # Arithmetic (these are rough estimates)
    '$_SDFF_PP0_': 10,     # Sync DFF with reset
    '$_SDFF_PP1_': 10,
    '$_SDFFCE_PP0P_': 12,  # Sync DFF with clock enable and reset
    '$_ALDFF_PP_': 10,     # Async load DFF
}

# Alternative names (some Yosys versions use different naming)
CELL_ALIASES = {
    'NOT': '$_NOT_',
    'BUF': '$_BUF_',
    'AND': '$_AND_',
    'NAND': '$_NAND_',
    'OR': '$_OR_',
    'NOR': '$_NOR_',
    'XOR': '$_XOR_',
    'XNOR': '$_XNOR_',
    'ANDNOT': '$_ANDNOT_',
    'ORNOT': '$_ORNOT_',
    'MUX': '$_MUX_',
    'NMUX': '$_NMUX_',
    'AOI3': '$_AOI3_',
    'OAI3': '$_OAI3_',
    'AOI4': '$_AOI4_',
    'OAI4': '$_OAI4_',
    'DFF_P': '$_DFF_P_',
    'DFF_N': '$_DFF_N_',
}


def parse_yosys_stat(text: str) -> Dict[str, int]:
    """
    Parse Yosys 'stat' output and extract cell counts.

    Args:
        text: Raw Yosys output containing stat results

    Returns:
        Dictionary mapping cell type to count
    """
    cells = {}

    # Pattern for Yosys stat output lines like:
    #    $_AND_                         123
    #    $_MUX_                          45
    cell_pattern = re.compile(r'^\s+(\$_\w+_|\w+)\s+(\d+)\s*$')

    # Also match "ABC RESULTS" format:
    #    ABC RESULTS:              NAND cells:        4
    abc_pattern = re.compile(r'ABC RESULTS:\s+(\w+)\s+cells:\s+(\d+)')

    for line in text.split('\n'):
        # Try standard stat format
        match = cell_pattern.match(line)
        if match:
            cell_type = match.group(1)
            count = int(match.group(2))
            cells[cell_type] = cells.get(cell_type, 0) + count
            continue

        # Try ABC results format
        match = abc_pattern.search(line)
        if match:
            cell_type = match.group(1)
            count = int(match.group(2))
            # Convert ABC cell names to Yosys format
            yosys_name = f'$_{cell_type.upper()}_'
            cells[yosys_name] = cells.get(yosys_name, 0) + count

    return cells


def cells_to_nand_equiv(cells: Dict[str, int], verbose: bool = False) -> Tuple[int, Dict[str, Tuple[int, int]]]:
    """
    Convert cell counts to NAND-2 equivalent gate count.

    Args:
        cells: Dictionary mapping cell type to count
        verbose: If True, return detailed breakdown

    Returns:
        Tuple of (total_nand_equiv, breakdown_dict)
        breakdown_dict maps cell_type to (count, nand_equiv)
    """
    total = 0
    breakdown = {}
    unknown_cells = {}

    for cell_type, count in cells.items():
        # Normalize cell name
        normalized = cell_type
        if cell_type in CELL_ALIASES:
            normalized = CELL_ALIASES[cell_type]

        # Look up NAND equivalent
        if normalized in NAND_EQUIVALENTS:
            nand_equiv = NAND_EQUIVALENTS[normalized] * count
            breakdown[cell_type] = (count, nand_equiv)
            total += nand_equiv
        else:
            # Unknown cell type - estimate based on name
            if 'MUX' in cell_type.upper():
                est = 4 * count  # Assume 2:1 MUX
            elif 'DFF' in cell_type.upper() or 'FF' in cell_type.upper():
                est = 6 * count  # Assume basic DFF
            elif 'LATCH' in cell_type.upper():
                est = 4 * count
            else:
                est = 2 * count  # Default: assume 2-input gate

            unknown_cells[cell_type] = (count, est)
            breakdown[cell_type] = (count, est)
            total += est

    return total, breakdown, unknown_cells


def format_report(cells: Dict[str, int], total_nand: int,
                  breakdown: Dict[str, Tuple[int, int]],
                  unknown_cells: Dict[str, Tuple[int, int]],
                  verbose: bool = False) -> str:
    """Format the conversion report."""

    lines = []
    lines.append("=" * 60)
    lines.append("Yosys to NAND-2 Equivalent Gate Count Conversion")
    lines.append("=" * 60)
    lines.append("")

    # Summary
    total_cells = sum(cells.values())
    lines.append(f"Total Yosys cells:     {total_cells:,}")
    lines.append(f"NAND-2 equivalent:     {total_nand:,}")
    lines.append(f"Avg NAND/cell ratio:   {total_nand/total_cells:.2f}" if total_cells > 0 else "")
    lines.append("")

    if verbose:
        lines.append("-" * 60)
        lines.append("Cell Type Breakdown:")
        lines.append("-" * 60)
        lines.append(f"{'Cell Type':<25} {'Count':>8} {'NAND Eq':>10} {'Ratio':>8}")
        lines.append("-" * 60)

        # Sort by NAND equivalent contribution (descending)
        sorted_cells = sorted(breakdown.items(),
                             key=lambda x: x[1][1], reverse=True)

        for cell_type, (count, nand_eq) in sorted_cells:
            ratio = nand_eq / count if count > 0 else 0
            marker = " *" if cell_type in unknown_cells else ""
            lines.append(f"{cell_type:<25} {count:>8,} {nand_eq:>10,} {ratio:>8.1f}{marker}")

        if unknown_cells:
            lines.append("")
            lines.append("* Unknown cell types - using estimated NAND equivalents")

    lines.append("")
    lines.append("=" * 60)

    return "\n".join(lines)


def run_yosys(commands: str) -> str:
    """Run Yosys with given commands and return output."""
    try:
        result = subprocess.run(
            ['yosys', '-p', commands],
            capture_output=True,
            text=True,
            timeout=300
        )
        return result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        return "ERROR: Yosys timed out after 300 seconds"
    except FileNotFoundError:
        return "ERROR: Yosys not found in PATH"


def main():
    parser = argparse.ArgumentParser(
        description='Convert Yosys netlist statistics to NAND-equivalent gate count',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Pipe from Yosys:
  yosys -p "read_verilog design.v; synth; stat" | %(prog)s

  # From log file:
  %(prog)s yosys.log

  # Run Yosys directly:
  %(prog)s --run "read_verilog design.v; synth; stat"

  # Verbose output:
  %(prog)s -v yosys.log
        """
    )

    parser.add_argument('input', nargs='?',
                        help='Input file (Yosys log). If not provided, reads from stdin.')
    parser.add_argument('-v', '--verbose', action='store_true',
                        help='Show detailed cell breakdown')
    parser.add_argument('--run', metavar='COMMANDS',
                        help='Run Yosys with these commands and convert the output')
    parser.add_argument('--json', action='store_true',
                        help='Output results in JSON format')

    args = parser.parse_args()

    # Get input text
    if args.run:
        text = run_yosys(args.run)
        if text.startswith("ERROR:"):
            print(text, file=sys.stderr)
            sys.exit(1)
    elif args.input:
        with open(args.input, 'r') as f:
            text = f.read()
    else:
        # Read from stdin
        if sys.stdin.isatty():
            parser.print_help()
            sys.exit(1)
        text = sys.stdin.read()

    # Parse and convert
    cells = parse_yosys_stat(text)

    if not cells:
        print("No cell statistics found in input.", file=sys.stderr)
        print("Make sure Yosys 'stat' command was run.", file=sys.stderr)
        sys.exit(1)

    total_nand, breakdown, unknown_cells = cells_to_nand_equiv(cells)

    # Output results
    if args.json:
        import json
        result = {
            'total_cells': sum(cells.values()),
            'total_nand_equiv': total_nand,
            'breakdown': {k: {'count': v[0], 'nand_equiv': v[1]}
                         for k, v in breakdown.items()},
            'unknown_cells': list(unknown_cells.keys())
        }
        print(json.dumps(result, indent=2))
    else:
        report = format_report(cells, total_nand, breakdown, unknown_cells, args.verbose)
        print(report)


if __name__ == '__main__':
    main()
