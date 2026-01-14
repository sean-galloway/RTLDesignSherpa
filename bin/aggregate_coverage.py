#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 Qernel AI
#
# Module: aggregate_coverage
# Purpose: Aggregate functional and RTL coverage from CocoTB tests
#
# Usage:
#   ./bin/aggregate_coverage.py --help
#   ./bin/aggregate_coverage.py --fub-only
#   ./bin/aggregate_coverage.py --macro-only
#   ./bin/aggregate_coverage.py --all --html
#   ./bin/aggregate_coverage.py --merge-verilator
#   ./bin/aggregate_coverage.py --project myproject --fub-dir design_dv/myproject/tests/fub

"""
Coverage Aggregation Tool

This script aggregates coverage data from:
1. Functional coverage (cocotb_coverage JSON files)
2. RTL coverage (Verilator .dat files)

Features:
- Merge FUB-level coverage into macro-level view
- Aggregate coverage across all test runs
- Generate HTML and text reports
- Identify coverage holes
- Project-agnostic: works with any CocoTB project

Examples:
    # Aggregate all coverage and generate HTML report
    ./bin/aggregate_coverage.py --all --html --output coverage_reports

    # Merge only FUB coverage
    ./bin/aggregate_coverage.py --fub-only --text

    # Merge Verilator RTL coverage
    ./bin/aggregate_coverage.py --merge-verilator --rtl-dir design_dv/project/tests/fub/local_sim_build

    # Specify project name for report titles
    ./bin/aggregate_coverage.py --project Q32 --all --html
"""

import argparse
import json
import os
import sys
import subprocess
from pathlib import Path
from typing import List, Dict, Optional, Any
from datetime import datetime
import logging

# Setup logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

# Add project paths
SCRIPT_DIR = Path(__file__).parent.absolute()
REPO_ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(REPO_ROOT))

# Coverage utilities are built-in - no external imports needed
COVERAGE_UTILS_AVAILABLE = True


def find_coverage_files(base_dir: str, pattern: str = "coverage_data.json") -> List[str]:
    """Find all coverage data files in a directory tree"""
    coverage_files = []
    for root, dirs, files in os.walk(base_dir):
        for file in files:
            if file == pattern or file.endswith('_coverage.json'):
                coverage_files.append(os.path.join(root, file))
    return coverage_files


def find_verilator_coverage_files(base_dir: str) -> List[str]:
    """Find all Verilator coverage .dat files"""
    dat_files = []
    for root, dirs, files in os.walk(base_dir):
        for file in files:
            if file.endswith('.dat') and 'coverage' in root.lower():
                dat_files.append(os.path.join(root, file))
    return dat_files


def merge_json_coverage(input_files: List[str], output_file: str) -> Dict:
    """Merge multiple JSON coverage files"""
    merged = {
        'version': '1.0',
        'timestamp': datetime.now().isoformat(),
        'source_files': input_files,
        'models': {}
    }

    for input_file in input_files:
        if not os.path.exists(input_file):
            logger.warning(f"Coverage file not found: {input_file}")
            continue

        try:
            with open(input_file, 'r') as f:
                data = json.load(f)
        except json.JSONDecodeError as e:
            logger.warning(f"Failed to parse {input_file}: {e}")
            continue

        for model_name, model_data in data.get('models', {}).items():
            if model_name not in merged['models']:
                merged['models'][model_name] = {
                    'name': model_name,
                    'hits': {},
                    'total_bins': model_data.get('total_bins', 0),
                    'covered_bins': 0
                }

            # Merge hits (add counts)
            for key, count in model_data.get('hits', {}).items():
                existing = merged['models'][model_name]['hits'].get(key, 0)
                merged['models'][model_name]['hits'][key] = existing + count

    # Recalculate covered bins and percentages
    for model_name, model_data in merged['models'].items():
        model_data['covered_bins'] = len([k for k, v in model_data['hits'].items() if v > 0])
        model_data['coverage_pct'] = (
            model_data['covered_bins'] / model_data['total_bins'] * 100
            if model_data['total_bins'] > 0 else 0
        )

    # Write output
    os.makedirs(os.path.dirname(output_file) or '.', exist_ok=True)
    with open(output_file, 'w') as f:
        json.dump(merged, f, indent=2)

    logger.info(f"Merged {len(input_files)} coverage files to {output_file}")
    return merged


def generate_html_report(coverage_data: Dict, output_dir: str, project_name: str = "Project") -> str:
    """Generate HTML coverage report"""
    os.makedirs(output_dir, exist_ok=True)
    output_file = os.path.join(output_dir, 'index.html')

    # Calculate totals
    total_bins = sum(m.get('total_bins', 0) for m in coverage_data.get('models', {}).values())
    covered_bins = sum(m.get('covered_bins', 0) for m in coverage_data.get('models', {}).values())
    overall_pct = (covered_bins / total_bins * 100) if total_bins > 0 else 0

    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{project_name} Coverage Report</title>
    <style>
        :root {{
            --primary: #2c3e50;
            --success: #27ae60;
            --warning: #f39c12;
            --danger: #e74c3c;
            --light: #ecf0f1;
            --dark: #34495e;
        }}
        * {{ box-sizing: border-box; margin: 0; padding: 0; }}
        body {{
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            background: var(--light);
            color: var(--primary);
            line-height: 1.6;
        }}
        .container {{ max-width: 1200px; margin: 0 auto; padding: 20px; }}
        header {{
            background: var(--primary);
            color: white;
            padding: 20px;
            margin-bottom: 20px;
            border-radius: 8px;
        }}
        header h1 {{ margin-bottom: 5px; }}
        header .timestamp {{ opacity: 0.8; font-size: 0.9em; }}
        .summary-cards {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 15px;
            margin-bottom: 20px;
        }}
        .card {{
            background: white;
            border-radius: 8px;
            padding: 20px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }}
        .card h3 {{ color: var(--dark); margin-bottom: 10px; }}
        .card .value {{ font-size: 2em; font-weight: bold; }}
        .card .value.success {{ color: var(--success); }}
        .card .value.warning {{ color: var(--warning); }}
        .card .value.danger {{ color: var(--danger); }}
        .progress-bar {{
            background: #ddd;
            border-radius: 10px;
            height: 20px;
            overflow: hidden;
            margin-top: 10px;
        }}
        .progress-fill {{
            height: 100%;
            transition: width 0.5s ease;
        }}
        .progress-fill.success {{ background: var(--success); }}
        .progress-fill.warning {{ background: var(--warning); }}
        .progress-fill.danger {{ background: var(--danger); }}
        .module {{
            background: white;
            border-radius: 8px;
            margin-bottom: 15px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
            overflow: hidden;
        }}
        .module-header {{
            background: var(--dark);
            color: white;
            padding: 15px 20px;
            display: flex;
            justify-content: space-between;
            align-items: center;
            cursor: pointer;
        }}
        .module-header:hover {{ background: var(--primary); }}
        .module-body {{ padding: 20px; display: none; }}
        .module-body.active {{ display: block; }}
        table {{
            width: 100%;
            border-collapse: collapse;
            margin-top: 10px;
        }}
        th, td {{
            padding: 10px;
            text-align: left;
            border-bottom: 1px solid #ddd;
        }}
        th {{ background: var(--light); font-weight: 600; }}
        tr:hover {{ background: #f5f5f5; }}
        .status {{ padding: 3px 8px; border-radius: 3px; font-size: 0.85em; }}
        .status.covered {{ background: #d4edda; color: #155724; }}
        .status.missed {{ background: #f8d7da; color: #721c24; }}
        .footer {{
            text-align: center;
            padding: 20px;
            color: var(--dark);
            opacity: 0.8;
        }}
    </style>
</head>
<body>
    <div class="container">
        <header>
            <h1>{project_name} Functional Coverage Report</h1>
            <div class="timestamp">Generated: {coverage_data.get('timestamp', 'N/A')}</div>
        </header>

        <div class="summary-cards">
            <div class="card">
                <h3>Overall Coverage</h3>
                <div class="value {'success' if overall_pct >= 80 else 'warning' if overall_pct >= 50 else 'danger'}">{overall_pct:.1f}%</div>
                <div class="progress-bar">
                    <div class="progress-fill {'success' if overall_pct >= 80 else 'warning' if overall_pct >= 50 else 'danger'}"
                         style="width: {overall_pct}%"></div>
                </div>
            </div>
            <div class="card">
                <h3>Total Bins</h3>
                <div class="value">{total_bins}</div>
            </div>
            <div class="card">
                <h3>Covered Bins</h3>
                <div class="value success">{covered_bins}</div>
            </div>
            <div class="card">
                <h3>Missed Bins</h3>
                <div class="value {'danger' if (total_bins - covered_bins) > 0 else 'success'}">{total_bins - covered_bins}</div>
            </div>
        </div>

        <h2 style="margin-bottom: 15px;">Module Coverage Details</h2>
"""

    # Per-module sections
    for model_name, model_data in sorted(coverage_data.get('models', {}).items()):
        pct = model_data.get('coverage_pct', 0)
        total = model_data.get('total_bins', 0)
        covered = model_data.get('covered_bins', 0)
        color_class = 'success' if pct >= 80 else 'warning' if pct >= 50 else 'danger'

        html += f"""
        <div class="module">
            <div class="module-header" onclick="toggleModule(this)">
                <span>{model_name}</span>
                <span>{pct:.1f}% ({covered}/{total} bins)</span>
            </div>
            <div class="module-body">
                <div class="progress-bar" style="margin-bottom: 15px;">
                    <div class="progress-fill {color_class}" style="width: {pct}%"></div>
                </div>
                <table>
                    <tr><th>Coverage Point</th><th>Hits</th><th>Status</th></tr>
"""
        for key, count in sorted(model_data.get('hits', {}).items()):
            status_class = 'covered' if count > 0 else 'missed'
            status_text = 'COVERED' if count > 0 else 'MISSED'
            html += f"                    <tr><td>{key}</td><td>{count}</td><td><span class='status {status_class}'>{status_text}</span></td></tr>\n"

        html += """                </table>
            </div>
        </div>
"""

    html += f"""
        <div class="footer">
            <p>{project_name} Coverage Report</p>
        </div>
    </div>

    <script>
        function toggleModule(header) {{
            const body = header.nextElementSibling;
            body.classList.toggle('active');
        }}
        // Expand first module by default
        document.querySelector('.module-body')?.classList.add('active');
    </script>
</body>
</html>
"""

    with open(output_file, 'w') as f:
        f.write(html)

    logger.info(f"HTML report generated: {output_file}")
    return output_file


def generate_text_report(coverage_data: Dict, output_dir: str, project_name: str = "Project") -> str:
    """Generate text coverage report"""
    os.makedirs(output_dir, exist_ok=True)
    output_file = os.path.join(output_dir, 'coverage_report.txt')

    lines = []
    lines.append("=" * 80)
    lines.append(f"{project_name.upper()} FUNCTIONAL COVERAGE REPORT")
    lines.append("=" * 80)
    lines.append(f"Generated: {coverage_data.get('timestamp', 'N/A')}")
    lines.append("")

    # Calculate totals
    total_bins = sum(m.get('total_bins', 0) for m in coverage_data.get('models', {}).values())
    covered_bins = sum(m.get('covered_bins', 0) for m in coverage_data.get('models', {}).values())
    overall_pct = (covered_bins / total_bins * 100) if total_bins > 0 else 0

    lines.append("SUMMARY")
    lines.append("-" * 40)
    lines.append(f"Total Bins:   {total_bins}")
    lines.append(f"Covered:      {covered_bins}")
    lines.append(f"Missed:       {total_bins - covered_bins}")
    lines.append(f"Coverage:     {overall_pct:.1f}%")
    lines.append("")

    # Per-module details
    lines.append("MODULE DETAILS")
    lines.append("=" * 80)

    for model_name, model_data in sorted(coverage_data.get('models', {}).items()):
        pct = model_data.get('coverage_pct', 0)
        lines.append("")
        lines.append(f"MODULE: {model_name}")
        lines.append(f"Coverage: {pct:.1f}% ({model_data.get('covered_bins', 0)}/{model_data.get('total_bins', 0)})")
        lines.append("-" * 60)

        # Show missed bins first
        missed = [(k, v) for k, v in model_data.get('hits', {}).items() if v == 0]
        covered = [(k, v) for k, v in model_data.get('hits', {}).items() if v > 0]

        if missed:
            lines.append("  MISSED:")
            for key, count in sorted(missed):
                lines.append(f"    - {key}")

        if covered:
            lines.append("  COVERED:")
            for key, count in sorted(covered):
                lines.append(f"    + {key} (hits: {count})")

    lines.append("")
    lines.append("=" * 80)

    with open(output_file, 'w') as f:
        f.write('\n'.join(lines))

    logger.info(f"Text report generated: {output_file}")
    return output_file


def merge_verilator_dat_files(input_dir: str, output_file: str) -> Optional[str]:
    """Merge Verilator .dat coverage files using verilator_coverage tool"""
    dat_files = find_verilator_coverage_files(input_dir)

    if not dat_files:
        logger.warning(f"No Verilator .dat files found in {input_dir}")
        return None

    logger.info(f"Found {len(dat_files)} Verilator coverage files")

    # Create output directory
    os.makedirs(os.path.dirname(output_file) or '.', exist_ok=True)

    try:
        cmd = ['verilator_coverage', '--write', output_file] + dat_files
        result = subprocess.run(cmd, capture_output=True, text=True)

        if result.returncode != 0:
            logger.error(f"verilator_coverage failed: {result.stderr}")
            return None

        logger.info(f"Merged Verilator coverage to {output_file}")
        return output_file

    except FileNotFoundError:
        logger.error("verilator_coverage not found. Is Verilator installed?")
        return None


def generate_verilator_html_report(dat_file: str, output_dir: str, rtl_dirs: List[str]) -> Optional[str]:
    """Generate annotated source report from Verilator coverage"""
    if not os.path.exists(dat_file):
        logger.error(f"Coverage file not found: {dat_file}")
        return None

    os.makedirs(output_dir, exist_ok=True)

    try:
        cmd = [
            'verilator_coverage',
            '--annotate', output_dir,
            '--annotate-all',
            '--annotate-min', '1',
            dat_file
        ]

        result = subprocess.run(cmd, capture_output=True, text=True)

        if result.returncode != 0:
            logger.warning(f"verilator_coverage annotate: {result.stderr}")
            # Continue anyway - partial annotation is still useful

        logger.info(f"Generated Verilator annotated sources in {output_dir}")
        return output_dir

    except FileNotFoundError:
        logger.error("verilator_coverage not found")
        return None


def main():
    parser = argparse.ArgumentParser(
        description='Coverage Aggregation Tool',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    # Aggregate FUB functional coverage
    %(prog)s --fub-only --output coverage_reports

    # Aggregate all coverage with HTML report
    %(prog)s --all --html --output coverage_reports

    # Specify project name for reports
    %(prog)s --project Q32 --all --html

    # Merge Verilator RTL coverage
    %(prog)s --merge-verilator --rtl-dir design_dv/project/tests/fub/local_sim_build

    # Full aggregation: FUB + Macro + Verilator
    %(prog)s --all --merge-verilator --html --text
        """
    )

    # Project options
    project_group = parser.add_argument_group('Project Options')
    project_group.add_argument('--project', '-p', type=str, default='Project',
                              help='Project name for report titles (default: Project)')

    # Coverage source options
    source_group = parser.add_argument_group('Coverage Sources')
    source_group.add_argument('--fub-only', action='store_true',
                             help='Aggregate only FUB-level coverage')
    source_group.add_argument('--macro-only', action='store_true',
                             help='Aggregate only Macro-level coverage')
    source_group.add_argument('--all', action='store_true',
                             help='Aggregate all available coverage')

    # Verilator options
    verilator_group = parser.add_argument_group('Verilator Coverage')
    verilator_group.add_argument('--merge-verilator', action='store_true',
                                help='Merge Verilator RTL coverage files')
    verilator_group.add_argument('--rtl-dir', type=str,
                                help='Directory containing Verilator .dat files')
    verilator_group.add_argument('--rtl-sources', type=str, nargs='+',
                                help='RTL source directories for annotation')

    # Output options
    output_group = parser.add_argument_group('Output Options')
    output_group.add_argument('--output', '-o', type=str, default='coverage_reports',
                             help='Output directory for reports (default: coverage_reports)')
    output_group.add_argument('--html', action='store_true',
                             help='Generate HTML report')
    output_group.add_argument('--text', action='store_true',
                             help='Generate text report')

    # Paths
    path_group = parser.add_argument_group('Path Options')
    path_group.add_argument('--fub-dir', type=str,
                           default='design_dv/tests/fub',
                           help='FUB test directory (default: design_dv/tests/fub)')
    path_group.add_argument('--macro-dir', type=str,
                           default='design_dv/tests/macro',
                           help='Macro test directory (default: design_dv/tests/macro)')

    args = parser.parse_args()

    # Default to --all if no source specified
    if not (args.fub_only or args.macro_only or args.all or args.merge_verilator):
        args.all = True

    # Default to HTML report if no format specified
    if not (args.html or args.text):
        args.html = True

    # Resolve paths
    output_dir = os.path.join(REPO_ROOT, args.output)
    fub_dir = os.path.join(REPO_ROOT, args.fub_dir)
    macro_dir = os.path.join(REPO_ROOT, args.macro_dir)

    # Collect coverage files
    coverage_files = []

    if args.fub_only or args.all:
        fub_files = find_coverage_files(fub_dir)
        logger.info(f"Found {len(fub_files)} FUB coverage files")
        coverage_files.extend(fub_files)

    if args.macro_only or args.all:
        macro_files = find_coverage_files(macro_dir)
        logger.info(f"Found {len(macro_files)} Macro coverage files")
        coverage_files.extend(macro_files)

    # Merge functional coverage
    if coverage_files:
        merged_file = os.path.join(output_dir, 'merged_functional_coverage.json')
        merged_data = merge_json_coverage(coverage_files, merged_file)

        # Generate reports
        if args.html:
            generate_html_report(merged_data, os.path.join(output_dir, 'html'), args.project)

        if args.text:
            generate_text_report(merged_data, output_dir, args.project)

        # Print summary
        total = sum(m.get('total_bins', 0) for m in merged_data.get('models', {}).values())
        covered = sum(m.get('covered_bins', 0) for m in merged_data.get('models', {}).values())
        pct = (covered / total * 100) if total > 0 else 0

        print("\n" + "=" * 60)
        print("FUNCTIONAL COVERAGE SUMMARY")
        print("=" * 60)
        print(f"Coverage Files: {len(coverage_files)}")
        print(f"Total Bins:     {total}")
        print(f"Covered Bins:   {covered}")
        print(f"Coverage:       {pct:.1f}%")
        print("=" * 60)
    else:
        logger.warning("No functional coverage files found")

    # Handle Verilator coverage
    if args.merge_verilator:
        rtl_dir = args.rtl_dir or os.path.join(fub_dir, 'local_sim_build')

        if os.path.exists(rtl_dir):
            merged_dat = os.path.join(output_dir, 'merged_verilator.dat')
            result = merge_verilator_dat_files(rtl_dir, merged_dat)

            if result:
                # Generate annotated sources
                rtl_sources = args.rtl_sources or [os.path.join(REPO_ROOT, 'rtl')]
                annotate_dir = os.path.join(output_dir, 'verilator_annotate')
                generate_verilator_html_report(merged_dat, annotate_dir, rtl_sources)

                print("\n" + "=" * 60)
                print("VERILATOR COVERAGE MERGED")
                print("=" * 60)
                print(f"Output: {merged_dat}")
                print(f"Annotated: {annotate_dir}")
                print("=" * 60)
        else:
            logger.warning(f"RTL coverage directory not found: {rtl_dir}")

    # Final output locations
    print("\n" + "=" * 60)
    print("OUTPUT LOCATIONS")
    print("=" * 60)
    print(f"Report Directory: {output_dir}")
    if args.html and coverage_files:
        print(f"HTML Report:      {os.path.join(output_dir, 'html', 'index.html')}")
    if args.text and coverage_files:
        print(f"Text Report:      {os.path.join(output_dir, 'coverage_report.txt')}")
    print("=" * 60)


if __name__ == '__main__':
    main()
