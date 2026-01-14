#!/usr/bin/env python3
"""
Hierarchical Coverage Report Generator

Generates a single markdown file with:
1. FUB-level coverage (line + functional) from FUB tests
2. Macro-level coverage from Macro tests (including FUB coverage achieved)
3. Top-level coverage from Top tests (including FUB/Macro coverage achieved)
4. Aggregate summary across all test levels

Usage:
    python3 generate_coverage_report.py --output coverage_report.md
    python3 generate_coverage_report.py --project Q32 --config coverage_config.json
    python3 generate_coverage_report.py --fub-modules mod1,mod2 --macro-modules mod3

Config file format (JSON):
{
    "project_name": "Q32",
    "fub_modules": ["q32_register_block", "q32_quantizer", ...],
    "macro_modules": ["q32_noqcore"],
    "dv_root": "design_dv/q32"
}
"""

import argparse
import json
import os
import re
import sys
from collections import defaultdict
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Tuple, Optional


class VerilatorCoverageParser:
    """Parse Verilator coverage.dat files for line coverage."""

    def __init__(self):
        self.file_coverage: Dict[str, Dict[int, int]] = defaultdict(lambda: defaultdict(int))
        self.module_coverage: Dict[str, Dict[str, int]] = defaultdict(lambda: {'hit': 0, 'total': 0})

    def parse_dat_file(self, dat_path: str) -> None:
        """Parse a single coverage.dat file."""
        if not os.path.exists(dat_path):
            return

        with open(dat_path, 'r') as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith('#'):
                    continue

                # Format: C 'f<filepath>l<line>...' <count>
                match = re.match(r"C '([^']+)' (\d+)", line)
                if match:
                    key = match.group(1)
                    count = int(match.group(2))

                    # Extract file path and line number
                    file_match = re.search(r'f([^l]+)l(\d+)', key)
                    if file_match:
                        filepath = file_match.group(1)
                        line_num = int(file_match.group(2))

                        # Get module name from filepath
                        module_name = self._extract_module_name(filepath)
                        if module_name:
                            self.file_coverage[filepath][line_num] = max(
                                self.file_coverage[filepath][line_num], count
                            )
                            self.module_coverage[module_name]['total'] += 1
                            if count > 0:
                                self.module_coverage[module_name]['hit'] += 1

    def _extract_module_name(self, filepath: str) -> Optional[str]:
        """Extract module name from file path."""
        # Look for q32_*.sv files
        match = re.search(r'(q32_[a-z_]+)\.sv', filepath)
        if match:
            return match.group(1)
        # Also capture qcore_*.sv
        match = re.search(r'(qcore_[a-z_]+)\.sv', filepath)
        if match:
            return match.group(1)
        return None

    def get_module_coverage(self) -> Dict[str, float]:
        """Get coverage percentage per module."""
        result = {}
        for module, data in self.module_coverage.items():
            if data['total'] > 0:
                result[module] = (data['hit'] / data['total']) * 100
            else:
                result[module] = 0.0
        return result


class FunctionalCoverageParser:
    """Parse functional coverage JSON files."""

    def __init__(self):
        self.coverage_data: Dict[str, Dict] = {}
        self.merged_bins: Dict[str, Dict[str, int]] = defaultdict(lambda: defaultdict(int))
        self._total_bins: Dict[str, int] = {}

    def parse_json_file(self, json_path: str) -> None:
        """Parse a single coverage JSON file."""
        if not os.path.exists(json_path):
            return

        try:
            with open(json_path, 'r') as f:
                data = json.load(f)

            # Handle format: {"version": ..., "models": {"ModuleName": {"hits": {...}, "total_bins": N}}}
            models = data.get('models', {})
            for module_name, module_data in models.items():
                if isinstance(module_data, dict):
                    # Get hits from 'hits' key
                    hits = module_data.get('hits', {})
                    total_bins = module_data.get('total_bins', 0)

                    for bin_name, hit_count in hits.items():
                        self.merged_bins[module_name][bin_name] = max(
                            self.merged_bins[module_name][bin_name],
                            hit_count if isinstance(hit_count, int) else 0
                        )

                    # Track total bins for uncovered bins calculation
                    if module_name not in self._total_bins:
                        self._total_bins[module_name] = total_bins

        except (json.JSONDecodeError, KeyError) as e:
            print(f"Warning: Could not parse {json_path}: {e}", file=sys.stderr)

    def get_coverage_summary(self) -> Dict[str, Dict]:
        """Get coverage summary per module."""
        result = {}
        for module_name, bins in self.merged_bins.items():
            # Use tracked total_bins if available, otherwise count from merged
            total = self._total_bins.get(module_name, len(bins))
            hit = sum(1 for v in bins.values() if v > 0)
            result[module_name] = {
                'total': total,
                'hit': hit,
                'percentage': (hit / total * 100) if total > 0 else 0,
                'bins': dict(bins)
            }
        return result


class CoverageReportGenerator:
    """Generate hierarchical markdown coverage report."""

    def __init__(self, repo_root: str, project_name: str = "Project",
                 fub_modules: List[str] = None, macro_modules: List[str] = None,
                 dv_root: str = None):
        self.repo_root = repo_root
        self.project_name = project_name
        self.fub_modules = fub_modules or []
        self.macro_modules = macro_modules or []

        # DV root can be specified or auto-detected
        if dv_root:
            self.dv_root = os.path.join(repo_root, dv_root)
        else:
            self.dv_root = os.path.join(repo_root, 'design_dv')

        # Coverage data by test level
        self.fub_line_coverage = VerilatorCoverageParser()
        self.fub_func_coverage = FunctionalCoverageParser()

        self.macro_line_coverage = VerilatorCoverageParser()
        self.macro_func_coverage = FunctionalCoverageParser()

        self.top_line_coverage = VerilatorCoverageParser()
        self.top_func_coverage = FunctionalCoverageParser()

    def collect_coverage(self) -> None:
        """Collect coverage data from all test levels."""
        # FUB tests
        fub_dir = os.path.join(self.dv_root, 'tests', 'fub', 'local_sim_build')
        self._collect_from_dir(fub_dir, self.fub_line_coverage, self.fub_func_coverage)

        # Macro tests
        macro_dir = os.path.join(self.dv_root, 'tests', 'macro', 'local_sim_build')
        self._collect_from_dir(macro_dir, self.macro_line_coverage, self.macro_func_coverage)

        # Top tests (if exists)
        top_dir = os.path.join(self.dv_root, 'tests', 'top', 'local_sim_build')
        self._collect_from_dir(top_dir, self.top_line_coverage, self.top_func_coverage)

    def _collect_from_dir(self, base_dir: str, line_parser: VerilatorCoverageParser,
                          func_parser: FunctionalCoverageParser) -> None:
        """Collect coverage from a test directory."""
        if not os.path.exists(base_dir):
            return

        for test_dir in os.listdir(base_dir):
            test_path = os.path.join(base_dir, test_dir)
            if not os.path.isdir(test_path):
                continue

            # Parse Verilator coverage
            dat_file = os.path.join(test_path, 'coverage.dat')
            line_parser.parse_dat_file(dat_file)

            # Parse functional coverage
            cov_data_dir = os.path.join(test_path, 'coverage_data')
            if os.path.exists(cov_data_dir):
                for json_file in os.listdir(cov_data_dir):
                    if json_file.endswith('_coverage.json'):
                        func_parser.parse_json_file(os.path.join(cov_data_dir, json_file))

    def generate_report(self) -> str:
        """Generate the markdown report."""
        lines = []

        # Header
        lines.append(f"# {self.project_name} Coverage Report")
        lines.append("")
        lines.append(f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        lines.append(f"**Repository:** {self.repo_root}")
        lines.append("")

        # Table of Contents
        lines.append("## Table of Contents")
        lines.append("")
        lines.append("1. [Executive Summary](#executive-summary)")
        lines.append("2. [FUB Coverage](#fub-coverage)")
        lines.append("3. [Macro Coverage](#macro-coverage)")
        lines.append("4. [Top Coverage](#top-coverage)")
        lines.append("5. [Aggregate Summary](#aggregate-summary)")
        lines.append("")

        # Executive Summary
        lines.extend(self._generate_executive_summary())

        # FUB Coverage
        lines.extend(self._generate_fub_section())

        # Macro Coverage
        lines.extend(self._generate_macro_section())

        # Top Coverage
        lines.extend(self._generate_top_section())

        # Aggregate Summary
        lines.extend(self._generate_aggregate_section())

        return '\n'.join(lines)

    def _generate_executive_summary(self) -> List[str]:
        """Generate executive summary section."""
        lines = []
        lines.append("## Executive Summary")
        lines.append("")

        # Calculate totals
        fub_func = self.fub_func_coverage.get_coverage_summary()
        macro_func = self.macro_func_coverage.get_coverage_summary()
        top_func = self.top_func_coverage.get_coverage_summary()

        fub_total_bins = sum(d['total'] for d in fub_func.values())
        fub_hit_bins = sum(d['hit'] for d in fub_func.values())

        macro_total_bins = sum(d['total'] for d in macro_func.values())
        macro_hit_bins = sum(d['hit'] for d in macro_func.values())

        top_total_bins = sum(d['total'] for d in top_func.values())
        top_hit_bins = sum(d['hit'] for d in top_func.values())

        lines.append("| Test Level | Functional Coverage | Line Coverage | Status |")
        lines.append("|------------|--------------------:|---------------|--------|")

        fub_pct = (fub_hit_bins / fub_total_bins * 100) if fub_total_bins > 0 else 0
        lines.append(f"| **FUB** | {fub_pct:.1f}% ({fub_hit_bins}/{fub_total_bins}) | See details | {'✅' if fub_pct >= 80 else '⚠️'} |")

        if macro_total_bins > 0:
            macro_pct = (macro_hit_bins / macro_total_bins * 100)
            lines.append(f"| **Macro** | {macro_pct:.1f}% ({macro_hit_bins}/{macro_total_bins}) | See details | {'✅' if macro_pct >= 80 else '⚠️'} |")
        else:
            lines.append("| **Macro** | No tests run | - | ❌ |")

        if top_total_bins > 0:
            top_pct = (top_hit_bins / top_total_bins * 100)
            lines.append(f"| **Top** | {top_pct:.1f}% ({top_hit_bins}/{top_total_bins}) | See details | {'✅' if top_pct >= 80 else '⚠️'} |")
        else:
            lines.append("| **Top** | No tests run | - | ❌ |")

        lines.append("")
        return lines

    def _generate_fub_section(self) -> List[str]:
        """Generate FUB coverage section."""
        lines = []
        lines.append("## FUB Coverage")
        lines.append("")
        lines.append("Coverage achieved by FUB-level unit tests.")
        lines.append("")

        func_summary = self.fub_func_coverage.get_coverage_summary()
        line_summary = self.fub_line_coverage.get_module_coverage()

        if not func_summary and not line_summary:
            lines.append("*No FUB coverage data available.*")
            lines.append("")
            return lines

        # Summary table
        lines.append("### FUB Summary")
        lines.append("")
        lines.append("| Module | Functional Coverage | Line Coverage |")
        lines.append("|--------|--------------------:|--------------:|")

        for module in self.fub_modules:
            func_data = None
            # Find matching functional coverage
            for name, data in func_summary.items():
                if module.replace('_', '') in name.lower().replace('_', ''):
                    func_data = data
                    break

            line_pct = line_summary.get(module, 0)

            if func_data:
                func_pct = func_data['percentage']
                lines.append(f"| {module} | {func_pct:.1f}% ({func_data['hit']}/{func_data['total']}) | {line_pct:.1f}% |")
            elif line_pct > 0:
                lines.append(f"| {module} | - | {line_pct:.1f}% |")
            else:
                lines.append(f"| {module} | - | - |")

        lines.append("")

        # Detailed functional coverage
        lines.append("### FUB Functional Coverage Details")
        lines.append("")

        for module_name, data in sorted(func_summary.items()):
            lines.append(f"#### {module_name}")
            lines.append("")
            lines.append(f"**Coverage:** {data['percentage']:.1f}% ({data['hit']}/{data['total']} bins)")
            lines.append("")

            covered = [(k, v) for k, v in data['bins'].items() if v > 0]
            missed = [(k, v) for k, v in data['bins'].items() if v == 0]

            if covered:
                lines.append("**Covered bins:**")
                for bin_name, hits in sorted(covered):
                    lines.append(f"- `{bin_name}` (hits: {hits})")
                lines.append("")

            if missed:
                lines.append("**Missed bins:**")
                for bin_name, _ in sorted(missed):
                    lines.append(f"- `{bin_name}`")
                lines.append("")

        return lines

    def _generate_macro_section(self) -> List[str]:
        """Generate Macro coverage section."""
        lines = []
        lines.append("## Macro Coverage")
        lines.append("")
        lines.append("Coverage achieved by Macro-level integration tests.")
        lines.append("")

        func_summary = self.macro_func_coverage.get_coverage_summary()
        line_summary = self.macro_line_coverage.get_module_coverage()

        if not func_summary and not line_summary:
            lines.append("*No Macro coverage data available. Run `make coverage-macro` to collect.*")
            lines.append("")
            return lines

        # Summary table
        lines.append("### Macro Summary")
        lines.append("")
        lines.append("| Module | Functional Coverage | Line Coverage |")
        lines.append("|--------|--------------------:|--------------:|")

        for module in self.macro_modules:
            func_data = None
            for name, data in func_summary.items():
                if module.replace('_', '') in name.lower().replace('_', ''):
                    func_data = data
                    break

            line_pct = line_summary.get(module, 0)

            if func_data:
                func_pct = func_data['percentage']
                lines.append(f"| {module} | {func_pct:.1f}% ({func_data['hit']}/{func_data['total']}) | {line_pct:.1f}% |")
            else:
                lines.append(f"| {module} | - | {line_pct:.1f}% |")

        lines.append("")

        # FUB coverage from Macro tests
        lines.append("### FUB Coverage from Macro Tests")
        lines.append("")
        lines.append("Coverage of FUB modules achieved through Macro-level tests:")
        lines.append("")
        lines.append("| FUB Module | Line Coverage from Macro |")
        lines.append("|------------|------------------------:|")

        for module in self.fub_modules:
            line_pct = line_summary.get(module, 0)
            lines.append(f"| {module} | {line_pct:.1f}% |")

        lines.append("")
        return lines

    def _generate_top_section(self) -> List[str]:
        """Generate Top coverage section."""
        lines = []
        lines.append("## Top Coverage")
        lines.append("")
        lines.append("Coverage achieved by Top-level system tests.")
        lines.append("")

        func_summary = self.top_func_coverage.get_coverage_summary()
        line_summary = self.top_line_coverage.get_module_coverage()

        if not func_summary and not line_summary:
            lines.append("*No Top coverage data available. Run `make coverage-top` when top tests are available.*")
            lines.append("")
            return lines

        # Similar structure to Macro section
        lines.append("### FUB/Macro Coverage from Top Tests")
        lines.append("")
        lines.append("| Module | Line Coverage from Top |")
        lines.append("|--------|----------------------:|")

        all_modules = self.fub_modules + self.macro_modules
        for module in all_modules:
            line_pct = line_summary.get(module, 0)
            lines.append(f"| {module} | {line_pct:.1f}% |")

        lines.append("")
        return lines

    def _generate_aggregate_section(self) -> List[str]:
        """Generate aggregate summary section."""
        lines = []
        lines.append("## Aggregate Summary")
        lines.append("")
        lines.append("Combined coverage across all test levels.")
        lines.append("")

        # Get all coverage summaries with proper totals
        all_summaries = [
            self.fub_func_coverage.get_coverage_summary(),
            self.macro_func_coverage.get_coverage_summary(),
            self.top_func_coverage.get_coverage_summary(),
        ]

        # Merge bins and track totals
        merged_data: Dict[str, Dict] = {}
        for summary in all_summaries:
            for module_name, data in summary.items():
                if module_name not in merged_data:
                    merged_data[module_name] = {
                        'total': data['total'],
                        'bins': dict(data['bins'])
                    }
                else:
                    # Use max total and merge bins
                    merged_data[module_name]['total'] = max(
                        merged_data[module_name]['total'], data['total']
                    )
                    for bin_name, hits in data['bins'].items():
                        current = merged_data[module_name]['bins'].get(bin_name, 0)
                        merged_data[module_name]['bins'][bin_name] = max(current, hits)

        # Calculate totals
        grand_total_bins = 0
        grand_total_hit = 0

        lines.append("### Functional Coverage by Module")
        lines.append("")
        lines.append("| Module | Covered | Total | Percentage |")
        lines.append("|--------|--------:|------:|-----------:|")

        for module_name in sorted(merged_data.keys()):
            data = merged_data[module_name]
            module_total = data['total']
            module_hit = sum(1 for v in data['bins'].values() if v > 0)
            grand_total_bins += module_total
            grand_total_hit += module_hit
            pct = (module_hit / module_total * 100) if module_total > 0 else 0
            lines.append(f"| {module_name} | {module_hit} | {module_total} | {pct:.1f}% |")

        lines.append("|--------|--------:|------:|-----------:|")
        total_pct = (grand_total_hit / grand_total_bins * 100) if grand_total_bins > 0 else 0
        lines.append(f"| **TOTAL** | **{grand_total_hit}** | **{grand_total_bins}** | **{total_pct:.1f}%** |")
        lines.append("")

        # Coverage holes - bins with 0 hits
        lines.append("### Coverage Holes")
        lines.append("")
        lines.append("Bins not covered by any test level:")
        lines.append("")

        has_holes = False
        for module_name in sorted(merged_data.keys()):
            bins = merged_data[module_name]['bins']
            missed = [k for k, v in bins.items() if v == 0]
            total = merged_data[module_name]['total']
            covered = len(bins)
            uncovered_count = total - covered

            if missed or uncovered_count > 0:
                has_holes = True
                lines.append(f"**{module_name}:** ({total - len([v for v in bins.values() if v > 0])}/{total} bins uncovered)")
                for bin_name in sorted(missed):
                    lines.append(f"- `{bin_name}`")
                if uncovered_count > 0:
                    lines.append(f"- *Plus {uncovered_count} bins not yet defined in coverage model*")
                lines.append("")

        if not has_holes:
            lines.append("*No coverage holes - all bins covered!*")
            lines.append("")

        return lines


def load_config(config_path: str) -> Dict:
    """Load configuration from JSON file."""
    if not os.path.exists(config_path):
        return {}
    with open(config_path, 'r') as f:
        return json.load(f)


def main():
    parser = argparse.ArgumentParser(
        description='Generate hierarchical coverage report',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    # Generate report with explicit project info
    %(prog)s --project Q32 --fub-modules q32_quantizer,q32_q4_block --output report.md

    # Use a config file
    %(prog)s --config coverage_config.json

    # Specify DV root
    %(prog)s --project MyProject --dv-root design_dv/myproject
        """
    )

    # Project options
    parser.add_argument('--project', '-p', type=str, default='Project',
                        help='Project name for report title')
    parser.add_argument('--config', '-c', type=str,
                        help='JSON config file with project settings')

    # Module lists
    parser.add_argument('--fub-modules', type=str,
                        help='Comma-separated list of FUB module names')
    parser.add_argument('--macro-modules', type=str,
                        help='Comma-separated list of Macro module names')

    # Paths
    parser.add_argument('--repo-root', default=os.environ.get('REPO_ROOT', '.'),
                        help='Repository root directory')
    parser.add_argument('--dv-root', type=str,
                        help='DV root relative to repo root (e.g., design_dv/q32)')
    parser.add_argument('--output', '-o', default='coverage_reports/coverage_report.md',
                        help='Output markdown file (relative to dv-root or absolute)')

    args = parser.parse_args()

    # Resolve repo root
    if args.repo_root == '.':
        args.repo_root = os.getcwd()

    # Load config file if specified
    config = {}
    if args.config:
        config_path = args.config
        if not os.path.isabs(config_path):
            config_path = os.path.join(args.repo_root, config_path)
        config = load_config(config_path)

    # Merge CLI args with config (CLI takes precedence)
    project_name = args.project if args.project != 'Project' else config.get('project_name', 'Project')
    dv_root = args.dv_root or config.get('dv_root')

    # Parse module lists
    fub_modules = []
    if args.fub_modules:
        fub_modules = [m.strip() for m in args.fub_modules.split(',')]
    elif 'fub_modules' in config:
        fub_modules = config['fub_modules']

    macro_modules = []
    if args.macro_modules:
        macro_modules = [m.strip() for m in args.macro_modules.split(',')]
    elif 'macro_modules' in config:
        macro_modules = config['macro_modules']

    # Create generator
    generator = CoverageReportGenerator(
        repo_root=args.repo_root,
        project_name=project_name,
        fub_modules=fub_modules,
        macro_modules=macro_modules,
        dv_root=dv_root
    )
    generator.collect_coverage()
    report = generator.generate_report()

    # Determine output path
    output_path = args.output
    if not os.path.isabs(output_path):
        if dv_root:
            output_path = os.path.join(args.repo_root, dv_root, output_path)
        else:
            output_path = os.path.join(args.repo_root, output_path)

    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    with open(output_path, 'w') as f:
        f.write(report)

    print(f"Coverage report generated: {output_path}")


if __name__ == '__main__':
    main()
