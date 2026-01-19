#!/usr/bin/env python3
"""
Extract coverage points from Verilator annotated files.

This script parses Verilator coverage-annotated SystemVerilog files and
extracts coverage points with their line numbers, types, and hit counts.

Usage:
    python extract_coverage_points.py <annotated_sv_file> [--yaml]
    python extract_coverage_points.py <coverage.dat> --annotate-dir <dir> [--yaml]
"""

import os
import re
import sys
import argparse
import subprocess
import tempfile
from pathlib import Path


def extract_from_annotated_file(filepath):
    """
    Extract coverage points from an annotated .sv file.

    Returns list of dicts with:
    - line: line number
    - hit_count: number of times hit
    - covered: True if hit_count > 0
    - content: line content (stripped)
    - type: inferred type (port, always_comb, case, case_branch, assign, etc.)
    """
    coverage_points = []

    with open(filepath, 'r') as f:
        lines = f.readlines()

    for i, line in enumerate(lines, 1):
        # Match Verilator annotation: %NNNNNN or  NNNNNN (space prefix)
        match = re.match(r'^([% ])(\d{6})\s+(.*)$', line)
        if match:
            prefix = match.group(1)
            count = int(match.group(2))
            content = match.group(3).strip()

            # Determine if covered (space prefix means >0 hits, or count > 0)
            covered = (prefix == ' ') or (count > 0)

            # Infer type from content
            point_type = infer_coverage_type(content)

            coverage_points.append({
                'line': i,
                'hit_count': count,
                'covered': covered,
                'content': content,
                'type': point_type
            })

    return coverage_points


def infer_coverage_type(content):
    """Infer the type of coverage point from line content."""
    content_lower = content.lower()

    # Port declarations
    if content_lower.startswith('input ') or content_lower.startswith('input\t'):
        return 'input_port'
    if content_lower.startswith('output ') or content_lower.startswith('output\t'):
        return 'output_port'
    if content_lower.startswith('inout '):
        return 'inout_port'

    # Always blocks
    if 'always_ff' in content_lower:
        return 'always_ff'
    if 'always_comb' in content_lower:
        return 'always_comb'
    if 'always @' in content_lower:
        return 'always'

    # Case statements
    if content_lower.startswith('case') or content_lower.startswith('casez') or content_lower.startswith('casex'):
        return 'case_statement'
    if re.match(r"^\d+'[bhd]", content) or re.match(r"^default\s*:", content_lower):
        return 'case_branch'

    # Assignments
    if content_lower.startswith('assign '):
        return 'continuous_assign'
    if '=' in content and 'assign' not in content_lower:
        return 'procedural_assign'

    # Logic declarations
    if content_lower.startswith('logic ') or content_lower.startswith('reg '):
        return 'signal_decl'
    if content_lower.startswith('wire '):
        return 'wire_decl'

    # Control flow
    if content_lower.startswith('if ') or content_lower.startswith('if('):
        return 'if_statement'
    if content_lower.startswith('else'):
        return 'else_branch'
    if content_lower.startswith('for ') or content_lower.startswith('for('):
        return 'for_loop'

    return 'other'


def annotate_coverage_dat(coverage_dat_path, output_dir=None):
    """
    Run verilator_coverage --annotate on a .dat file.

    Returns path to annotated directory.
    """
    if output_dir is None:
        output_dir = tempfile.mkdtemp(prefix='cov_annotate_')

    cmd = ['verilator_coverage', '--annotate', output_dir, coverage_dat_path]
    result = subprocess.run(cmd, capture_output=True, text=True)

    if result.returncode != 0:
        raise RuntimeError(f"verilator_coverage failed: {result.stderr}")

    return output_dir


def generate_yaml_testplan_skeleton(module_name, coverage_points, rtl_file=None):
    """Generate a YAML testplan skeleton from coverage points."""
    # Group points by type
    by_type = {}
    for pt in coverage_points:
        t = pt['type']
        if t not in by_type:
            by_type[t] = []
        by_type[t].append(pt)

    # Calculate coverage stats
    total = len(coverage_points)
    covered = sum(1 for pt in coverage_points if pt['covered'])
    pct = (covered / total * 100) if total > 0 else 0

    yaml_lines = [
        f"# Testplan for {module_name}",
        f"# Auto-generated - edit functional_scenarios section",
        f"",
        f"module: {module_name}",
        f"rtl_file: {rtl_file or f'rtl/common/{module_name}.sv'}",
        f"",
        f"# Raw Verilator coverage: {covered}/{total} ({pct:.1f}%)",
        f"",
        f"# Coverage points extracted from annotated file",
        f"coverage_points:",
    ]

    # Group consecutive case branches
    for pt in coverage_points:
        yaml_lines.append(f"  - line: {pt['line']}")
        yaml_lines.append(f"    type: {pt['type']}")
        yaml_lines.append(f"    covered: {pt['covered']}")
        yaml_lines.append(f"    hit_count: {pt['hit_count']}")
        # Escape content for YAML
        content_escaped = pt['content'].replace('"', '\\"')
        yaml_lines.append(f'    content: "{content_escaped}"')
        yaml_lines.append(f"")

    # Add functional scenarios section
    yaml_lines.extend([
        "",
        "# Functional scenarios - EDIT THIS SECTION",
        "# Map test scenarios to coverage points",
        "functional_scenarios:",
        "  - id: S1",
        "    name: \"Basic functionality\"",
        "    description: \"Test basic module operation\"",
        "    test_function: \"<test_function_name>\"",
        "    covers_lines: []  # Add line numbers this scenario covers",
        "    status: not_tested  # verified, partial, not_tested, not_applicable",
        "",
        "# Implied coverage calculation (auto-computed by tracker)",
        "implied_coverage:",
        "  total_points: {}".format(total),
        "  covered_by_verilator: {}".format(covered),
        "  covered_by_scenarios: 0  # Updated by tracker",
        "  implied_percentage: 0.0  # Updated by tracker",
    ])

    return '\n'.join(yaml_lines)


def main():
    parser = argparse.ArgumentParser(description='Extract coverage points from Verilator output')
    parser.add_argument('input_file', help='Annotated .sv file or coverage.dat file')
    parser.add_argument('--annotate-dir', help='Directory for annotation output (if input is .dat)')
    parser.add_argument('--yaml', action='store_true', help='Output as YAML testplan skeleton')
    parser.add_argument('--module', help='Module name (for YAML output)')
    parser.add_argument('--rtl-file', help='RTL file path (for YAML output)')
    args = parser.parse_args()

    input_path = args.input_file

    # If input is .dat file, annotate it first
    if input_path.endswith('.dat'):
        annotate_dir = args.annotate_dir or tempfile.mkdtemp(prefix='cov_')
        annotate_dir = annotate_coverage_dat(input_path, annotate_dir)

        # Find .sv files in annotated directory
        sv_files = list(Path(annotate_dir).glob('*.sv'))
        if not sv_files:
            print(f"No .sv files found in {annotate_dir}", file=sys.stderr)
            sys.exit(1)

        for sv_file in sv_files:
            module_name = sv_file.stem
            coverage_points = extract_from_annotated_file(sv_file)

            if args.yaml:
                print(generate_yaml_testplan_skeleton(
                    args.module or module_name,
                    coverage_points,
                    args.rtl_file
                ))
            else:
                print(f"\n=== {module_name} ===")
                for pt in coverage_points:
                    status = "COVERED" if pt['covered'] else "NOT COVERED"
                    print(f"  L{pt['line']:4d} [{pt['type']:20s}] {status:12s} {pt['hit_count']:6d}  {pt['content'][:60]}")

    else:
        # Direct annotated file
        coverage_points = extract_from_annotated_file(input_path)
        module_name = Path(input_path).stem

        if args.yaml:
            print(generate_yaml_testplan_skeleton(
                args.module or module_name,
                coverage_points,
                args.rtl_file
            ))
        else:
            total = len(coverage_points)
            covered = sum(1 for pt in coverage_points if pt['covered'])
            print(f"Module: {module_name}")
            print(f"Coverage: {covered}/{total} ({covered/total*100:.1f}%)")
            print()
            for pt in coverage_points:
                status = "COVERED" if pt['covered'] else "NOT COVERED"
                print(f"  L{pt['line']:4d} [{pt['type']:20s}] {status:12s} {pt['hit_count']:6d}  {pt['content'][:60]}")


if __name__ == '__main__':
    main()
