#!/usr/bin/env python3
"""
Batch generate testplan skeletons for modules with low coverage.

This script:
1. Finds modules with coverage below threshold
2. Generates YAML testplan skeletons with coverage points extracted
3. Places them in the testplans directory for manual editing

Usage:
    python generate_testplan_batch.py --coverage-dir <dir> --threshold 95 --output-dir <dir>
"""

import os
import re
import sys
import argparse
import subprocess
import tempfile
from pathlib import Path
from datetime import datetime


def get_modules_below_threshold(coverage_dir, threshold=95.0):
    """
    Analyze coverage files and return modules below threshold.

    Returns list of (module_name, coverage_pct, coverage_dat_path)
    """
    modules = []

    # Find all coverage.dat files
    dat_files = list(Path(coverage_dir).rglob('coverage.dat'))

    if not dat_files:
        print(f"No coverage.dat files found in {coverage_dir}", file=sys.stderr)
        return modules

    # Group by module (extract from directory name)
    module_files = {}
    for dat_file in dat_files:
        # Extract module name from test_<module>_* pattern
        dir_name = dat_file.parent.name
        match = re.match(r'test_([a-z0-9_]+?)_', dir_name)
        if match:
            module_name = match.group(1)
            if module_name not in module_files:
                module_files[module_name] = []
            module_files[module_name].append(str(dat_file))

    # Analyze each module's coverage
    for module_name, dat_paths in module_files.items():
        # Merge coverage files for this module
        with tempfile.NamedTemporaryFile(suffix='.dat', delete=False) as tmp:
            merged_path = tmp.name

        try:
            cmd = ['verilator_coverage', '--write', merged_path] + dat_paths
            subprocess.run(cmd, capture_output=True)

            # Annotate to get coverage percentage
            with tempfile.TemporaryDirectory() as annotate_dir:
                cmd = ['verilator_coverage', '--annotate', annotate_dir, merged_path]
                result = subprocess.run(cmd, capture_output=True, text=True)

                # Parse coverage percentage from output
                # Format: "Total coverage (N/M) XX.XX%"
                match = re.search(r'Total coverage \((\d+)/(\d+)\) ([\d.]+)%', result.stdout + result.stderr)
                if match:
                    covered = int(match.group(1))
                    total = int(match.group(2))
                    pct = float(match.group(3))

                    if pct < threshold:
                        modules.append((module_name, pct, dat_paths[0], merged_path))
        except Exception as e:
            print(f"Error processing {module_name}: {e}", file=sys.stderr)
        finally:
            if os.path.exists(merged_path) and module_name not in [m[0] for m in modules]:
                os.unlink(merged_path)

    # Sort by coverage percentage (lowest first)
    modules.sort(key=lambda x: x[1])

    return modules


def generate_testplan_skeleton(module_name, coverage_dat_path, rtl_dir='rtl/common'):
    """Generate a YAML testplan skeleton for a module."""

    # Annotate the coverage data
    with tempfile.TemporaryDirectory() as annotate_dir:
        cmd = ['verilator_coverage', '--annotate', annotate_dir, coverage_dat_path]
        subprocess.run(cmd, capture_output=True)

        # Find the annotated file
        sv_file = Path(annotate_dir) / f"{module_name}.sv"
        if not sv_file.exists():
            # Try to find any .sv file that matches
            sv_files = list(Path(annotate_dir).glob('*.sv'))
            for f in sv_files:
                if module_name in f.stem:
                    sv_file = f
                    break

        if not sv_file.exists():
            return None

        # Extract coverage points
        coverage_points = []
        with open(sv_file, 'r') as f:
            for i, line in enumerate(f, 1):
                match = re.match(r'^([% ])(\d{6})\s+(.*)$', line)
                if match:
                    prefix = match.group(1)
                    count = int(match.group(2))
                    content = match.group(3).strip()
                    covered = (prefix == ' ') or (count > 0)

                    # Infer type
                    point_type = infer_type(content)

                    coverage_points.append({
                        'line': i,
                        'type': point_type,
                        'covered': covered,
                        'hit_count': count,
                        'content': content[:80]  # Truncate long lines
                    })

    # Calculate coverage stats
    total = len(coverage_points)
    covered = sum(1 for pt in coverage_points if pt['covered'])
    pct = (covered / total * 100) if total > 0 else 0

    # Identify coverage gap categories
    uncovered_by_type = {}
    for pt in coverage_points:
        if not pt['covered']:
            t = pt['type']
            if t not in uncovered_by_type:
                uncovered_by_type[t] = []
            uncovered_by_type[t].append(pt['line'])

    # Generate YAML
    yaml_lines = [
        f"# Testplan for {module_name}",
        f"# Auto-generated on {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        f"# EDIT: Add functional scenarios to improve implied coverage",
        f"",
        f"module: {module_name}",
        f"rtl_file: {rtl_dir}/{module_name}.sv",
        f"test_file: val/common/test_{module_name}.py",
        f"",
        f"# Raw Verilator coverage: {covered}/{total} ({pct:.1f}%)",
        f"",
    ]

    # Add coverage gap analysis
    if uncovered_by_type:
        yaml_lines.extend([
            "# Coverage gaps by type:",
        ])
        for gap_type, lines in sorted(uncovered_by_type.items()):
            yaml_lines.append(f"#   {gap_type}: {len(lines)} uncovered lines")

    yaml_lines.extend([
        "",
        "# Coverage points",
        "coverage_points:",
    ])

    for pt in coverage_points:
        yaml_lines.extend([
            f"  - line: {pt['line']}",
            f"    type: {pt['type']}",
            f"    covered: {pt['covered']}",
            f"    hit_count: {pt['hit_count']}",
            f'    content: "{pt["content"]}"',
            f"",
        ])

    yaml_lines.extend([
        "",
        "# Functional scenarios - ADD YOUR SCENARIOS HERE",
        "# Map test scenarios to coverage points",
        "functional_scenarios:",
        "  - id: S1",
        "    name: \"Basic functionality\"",
        "    description: \"Describe what this scenario tests\"",
        "    test_function: \"test_function_name\"",
        "    covers_lines: []  # Add line numbers covered by this scenario",
        "    status: not_tested  # verified, partial, not_tested, not_applicable",
        "",
        "# TODO: Add more scenarios to cover gaps in:",
    ])

    for gap_type, lines in sorted(uncovered_by_type.items()):
        yaml_lines.append(f"#   - {gap_type}: lines {lines[:5]}{'...' if len(lines) > 5 else ''}")

    yaml_lines.extend([
        "",
        "# Implied coverage calculation (auto-computed)",
        "implied_coverage:",
        f"  total_points: {total}",
        f"  verilator_covered: {covered}",
        "  scenario_covered: 0  # Update after adding scenarios",
        "  implied_percentage: 0.0  # Update after adding scenarios",
    ])

    return '\n'.join(yaml_lines)


def infer_type(content):
    """Infer coverage point type from line content."""
    content_lower = content.lower()

    if content_lower.startswith('input '):
        return 'input_port'
    if content_lower.startswith('output '):
        return 'output_port'
    if 'always_ff' in content_lower:
        return 'always_ff'
    if 'always_comb' in content_lower:
        return 'always_comb'
    if content_lower.startswith('case') or content_lower.startswith('casez'):
        return 'case_statement'
    if re.match(r"^\d+'[bhd]", content) or 'default:' in content_lower:
        return 'case_branch'
    if content_lower.startswith('assign '):
        return 'continuous_assign'
    if content_lower.startswith('logic ') or content_lower.startswith('reg '):
        return 'signal_decl'
    if content_lower.startswith('if ') or content_lower.startswith('if('):
        return 'if_statement'
    if content_lower.startswith('else'):
        return 'else_branch'

    return 'other'


def main():
    parser = argparse.ArgumentParser(description='Batch generate testplan skeletons')
    parser.add_argument('--coverage-dir', default='val/common/local_sim_build',
                       help='Directory containing coverage.dat files')
    parser.add_argument('--threshold', type=float, default=95.0,
                       help='Coverage threshold (default: 95%%)')
    parser.add_argument('--output-dir', default='val/common/testplans',
                       help='Output directory for testplans')
    parser.add_argument('--rtl-dir', default='rtl/common',
                       help='RTL directory for module paths')
    parser.add_argument('--dry-run', action='store_true',
                       help='Show what would be generated without writing files')
    parser.add_argument('--skip-existing', action='store_true',
                       help='Skip modules that already have testplans')
    args = parser.parse_args()

    # Find modules below threshold
    print(f"Scanning {args.coverage_dir} for modules below {args.threshold}% coverage...")
    modules = get_modules_below_threshold(args.coverage_dir, args.threshold)

    if not modules:
        print("No modules found below threshold.")
        return

    print(f"Found {len(modules)} modules below {args.threshold}% coverage:\n")

    # Create output directory
    os.makedirs(args.output_dir, exist_ok=True)

    generated = 0
    skipped = 0

    for module_name, pct, dat_path, merged_path in modules:
        output_path = os.path.join(args.output_dir, f"{module_name}_testplan.yaml")

        # Check if testplan exists
        if args.skip_existing and os.path.exists(output_path):
            print(f"  SKIP {module_name} ({pct:.1f}%) - testplan exists")
            skipped += 1
            continue

        print(f"  {module_name}: {pct:.1f}%")

        if args.dry_run:
            continue

        # Generate testplan
        testplan = generate_testplan_skeleton(module_name, merged_path, args.rtl_dir)

        if testplan:
            with open(output_path, 'w') as f:
                f.write(testplan)
            print(f"    -> {output_path}")
            generated += 1
        else:
            print(f"    ERROR: Could not generate testplan")

        # Cleanup merged file
        if os.path.exists(merged_path):
            os.unlink(merged_path)

    print(f"\nGenerated {generated} testplans, skipped {skipped}")


if __name__ == '__main__':
    main()
