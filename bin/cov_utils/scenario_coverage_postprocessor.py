#!/usr/bin/env python3
"""
Scenario Coverage Post-Processor

Parses test log files for scenario execution markers and compares them
against testplan markdown files to calculate scenario coverage.

Scenario markers in test logs follow the pattern:
    === Scenario XXX-NNN ===
    === Scenario PREFIX-XXX-NNN ===

Testplan markdown files have scenarios in tables like:
    | XXX-NNN | Description | ... |

Usage:
    # Basic usage - analyze log file against testplan
    python scenario_coverage_postprocessor.py --log <test.log> --testplan <testplan.md>

    # Analyze directory of logs against directory of testplans
    python scenario_coverage_postprocessor.py --log-dir <logs/> --testplan-dir <testplans/>

    # Show detailed output
    python scenario_coverage_postprocessor.py --log <test.log> --testplan <testplan.md> -v

    # Output as JSON
    python scenario_coverage_postprocessor.py --log <test.log> --testplan <testplan.md> --format json

Author: RTLDesignSherpa/Claude Code
Version: 1.0
"""

import argparse
import json
import os
import re
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

try:
    import yaml
    YAML_AVAILABLE = True
except ImportError:
    YAML_AVAILABLE = False


@dataclass
class ScenarioCoverage:
    """Coverage data for a single testplan."""
    testplan_name: str
    testplan_path: str
    total_scenarios: int = 0
    executed_scenarios: int = 0
    missing_scenarios: List[str] = field(default_factory=list)
    extra_scenarios: List[str] = field(default_factory=list)
    executed_list: List[str] = field(default_factory=list)
    testplan_list: List[str] = field(default_factory=list)

    @property
    def coverage_pct(self) -> float:
        if self.total_scenarios == 0:
            return 0.0
        return (self.executed_scenarios / self.total_scenarios) * 100.0


@dataclass
class CoverageReport:
    """Aggregate coverage report."""
    testplan_results: List[ScenarioCoverage] = field(default_factory=list)
    total_scenarios: int = 0
    total_executed: int = 0
    all_missing: List[str] = field(default_factory=list)

    @property
    def overall_coverage_pct(self) -> float:
        if self.total_scenarios == 0:
            return 0.0
        return (self.total_executed / self.total_scenarios) * 100.0


def normalize_scenario_id(scenario_id: str) -> str:
    """
    Normalize scenario ID for comparison.

    Handles variations like:
    - REGBLK-AXI005 -> AXI005
    - AXI-005 -> AXI005
    - AXI005 -> AXI005
    - SEQR-CMD-001 -> CMD001

    Returns normalized form: PREFIX + NUMBER (no hyphens).
    """
    # Remove common prefixes (module-specific prefixes like REGBLK-, SEQR-, etc.)
    # These are prefixes added for disambiguation in multi-module tests
    module_prefixes = [
        'REGBLK-', 'SEQR-', 'DFS-', 'BCAST-', 'QUANT-', 'Q4BLK-',
        'NOQCORE-', 'MACRO-', 'FUB-'
    ]
    result = scenario_id.upper()
    for prefix in module_prefixes:
        if result.startswith(prefix):
            result = result[len(prefix):]
            break

    # Remove all hyphens and standardize
    result = result.replace('-', '')

    return result


def extract_scenarios_from_log(log_content: str, patterns: Optional[List[str]] = None) -> Set[str]:
    """
    Extract scenario IDs from test log content.

    Args:
        log_content: Full log file content
        patterns: Optional custom regex patterns (default uses === Scenario)

    Returns:
        Set of normalized scenario IDs found in the log
    """
    if patterns is None:
        # Default patterns for scenario markers
        patterns = [
            r'===\s*Scenario\s+([A-Z0-9_-]+):.*===',   # === Scenario XXX: description ===
            r'===\s*Scenario\s+([A-Z0-9_-]+):\s',      # === Scenario XXX: description (no trailing ===)
            r'===\s*Scenario\s+([A-Z0-9_-]+)\s*===',   # === Scenario XXX ===
            r'===\s*Scenario\s+([A-Z0-9_-]+)\s*$',     # === Scenario XXX (no trailing ===)
            r'\[SCENARIO\]\s+([A-Z0-9_-]+)',           # [SCENARIO] XXX
            r'Scenario:\s+([A-Z0-9_-]+)',              # Scenario: XXX
        ]

    scenarios = set()
    for pattern in patterns:
        matches = re.findall(pattern, log_content, re.IGNORECASE | re.MULTILINE)
        for match in matches:
            normalized = normalize_scenario_id(match)
            if normalized:  # Skip empty matches
                scenarios.add(normalized)

    # Also extract from "Also covers" lines (multi-scenario format)
    # Pattern: "Also covers: XXX-01 (desc), XXX-02 (desc), XXX-03 (desc)"
    also_covers_pattern = r'Also covers:([^\n]+)'
    also_covers_matches = re.findall(also_covers_pattern, log_content, re.IGNORECASE)
    for line in also_covers_matches:
        # Extract all scenario IDs from the line (format: PREFIX-NN or PREFIX-SUFFIX-NN)
        scenario_ids = re.findall(r'([A-Z]+-(?:[A-Z]+-)?(?:\d+|\w+))', line, re.IGNORECASE)
        for sid in scenario_ids:
            normalized = normalize_scenario_id(sid)
            if normalized:
                scenarios.add(normalized)

    # Extract from any line with "===" that contains scenario IDs
    # Pattern: "=== STREAM-CORE-07 (desc), STREAM-CORE-09 (desc) ===" or similar
    scenario_line_pattern = r'===([^=]+)==='
    scenario_line_matches = re.findall(scenario_line_pattern, log_content, re.IGNORECASE)
    for line in scenario_line_matches:
        # Extract all scenario IDs like STREAM-CORE-NN, STREAM-TOP-NN, etc.
        scenario_ids = re.findall(r'([A-Z]+-[A-Z]+-\d+)', line, re.IGNORECASE)
        for sid in scenario_ids:
            normalized = normalize_scenario_id(sid)
            if normalized:
                scenarios.add(normalized)

    # Also extract from compound scenario markers like "STREAM-CORE-01/02/03"
    # or "SRAM-CTRL-01/02/03/11"
    compound_pattern = r'([A-Z]+-[A-Z]+)-(\d+(?:/\d+)+)'
    compound_matches = re.findall(compound_pattern, log_content, re.IGNORECASE)
    for prefix, numbers in compound_matches:
        for num in numbers.split('/'):
            sid = f"{prefix}-{num}"
            normalized = normalize_scenario_id(sid)
            if normalized:
                scenarios.add(normalized)

    return scenarios


def extract_scenarios_from_testplan(testplan_path: Path) -> Set[str]:
    """
    Extract scenario IDs from testplan file (markdown or YAML).

    For markdown: Looks for table rows with scenario IDs in formats like:
        | AXI-001 | Description | ... |
        | CMD001 | Description | ... |

    For YAML: Looks for functional_scenarios[].id fields like:
        functional_scenarios:
          - id: SCHED-01
          - id: APB2DESC-02

    Args:
        testplan_path: Path to testplan file (markdown or YAML)

    Returns:
        Set of normalized scenario IDs found in the testplan
    """
    scenarios = set()
    suffix = testplan_path.suffix.lower()

    if suffix in ['.yaml', '.yml']:
        # YAML testplan format
        if not YAML_AVAILABLE:
            print(f"Warning: pyyaml not installed, cannot parse {testplan_path}", file=sys.stderr)
            return scenarios

        with open(testplan_path, 'r') as f:
            try:
                testplan = yaml.safe_load(f)
            except yaml.YAMLError as e:
                print(f"Warning: Failed to parse YAML {testplan_path}: {e}", file=sys.stderr)
                return scenarios

        # Extract from functional_scenarios list
        func_scenarios = testplan.get('functional_scenarios', [])
        if func_scenarios:
            for scenario in func_scenarios:
                sid = scenario.get('id', '')
                if sid:
                    normalized = normalize_scenario_id(sid)
                    if normalized:
                        scenarios.add(normalized)

        # Also check fsm_state_coverage if present (for FSM state tracking)
        fsm_states = testplan.get('fsm_state_coverage', {})
        for state_name in fsm_states.keys():
            if state_name not in ['verification_date', 'test_config', 'toggle_coverage',
                                   'behavioral_coverage', 'uncovered_analysis', 'notes',
                                   'uncovered_lines']:
                # Treat FSM states as scenarios with FSM- prefix
                normalized = normalize_scenario_id(f"FSM-{state_name}")
                if normalized:
                    scenarios.add(normalized)

    else:
        # Markdown testplan format
        with open(testplan_path, 'r') as f:
            content = f.read()

        # Pattern for scenario IDs in markdown tables
        # Matches: | XXX-NNN | or | XXXNNN |
        # Common prefixes: AXI, CMD, CTL, RST, SUB, DAT, ENB, FET, FSM, etc.
        table_pattern = r'\|\s*([A-Z]{2,}[-]?\d{3})\s*\|'

        matches = re.findall(table_pattern, content, re.MULTILINE)
        for match in matches:
            normalized = normalize_scenario_id(match)
            if normalized:
                scenarios.add(normalized)

    return scenarios


def analyze_coverage(
    log_content: str,
    testplan_path: Path,
    log_patterns: Optional[List[str]] = None
) -> ScenarioCoverage:
    """
    Analyze scenario coverage for a single testplan.

    Args:
        log_content: Test log content
        testplan_path: Path to testplan markdown file
        log_patterns: Optional custom log patterns

    Returns:
        ScenarioCoverage with detailed results
    """
    executed = extract_scenarios_from_log(log_content, log_patterns)
    testplan_scenarios = extract_scenarios_from_testplan(testplan_path)

    # Find missing and extra scenarios
    missing = testplan_scenarios - executed
    extra = executed - testplan_scenarios
    covered = testplan_scenarios & executed

    return ScenarioCoverage(
        testplan_name=testplan_path.stem,
        testplan_path=str(testplan_path),
        total_scenarios=len(testplan_scenarios),
        executed_scenarios=len(covered),
        missing_scenarios=sorted(list(missing)),
        extra_scenarios=sorted(list(extra)),
        executed_list=sorted(list(covered)),
        testplan_list=sorted(list(testplan_scenarios)),
    )


def collect_logs_from_directory(log_dir: Path, extensions: List[str] = None) -> str:
    """
    Collect and concatenate all log files from a directory.

    Args:
        log_dir: Directory containing log files
        extensions: File extensions to include (default: .log, .txt, .out)

    Returns:
        Concatenated content of all log files
    """
    if extensions is None:
        extensions = ['.log', '.txt', '.out']

    all_content = []
    for ext in extensions:
        for log_file in log_dir.rglob(f'*{ext}'):
            try:
                with open(log_file, 'r', errors='ignore') as f:
                    all_content.append(f.read())
            except Exception as e:
                print(f"Warning: Could not read {log_file}: {e}", file=sys.stderr)

    return '\n'.join(all_content)


def generate_report(
    results: List[ScenarioCoverage],
    output_format: str = 'text',
    verbose: bool = False
) -> str:
    """
    Generate coverage report in specified format.

    Args:
        results: List of ScenarioCoverage objects
        output_format: 'text', 'markdown', 'json', or 'csv'
        verbose: Include detailed scenario lists

    Returns:
        Formatted report string
    """
    # Aggregate totals
    total_scenarios = sum(r.total_scenarios for r in results)
    total_executed = sum(r.executed_scenarios for r in results)
    all_missing = []
    for r in results:
        all_missing.extend([f"{r.testplan_name}:{s}" for s in r.missing_scenarios])

    overall_pct = (total_executed / total_scenarios * 100) if total_scenarios else 0

    if output_format == 'json':
        report_data = {
            'summary': {
                'total_scenarios': total_scenarios,
                'total_executed': total_executed,
                'coverage_pct': round(overall_pct, 1),
            },
            'testplans': [
                {
                    'name': r.testplan_name,
                    'total': r.total_scenarios,
                    'executed': r.executed_scenarios,
                    'coverage_pct': round(r.coverage_pct, 1),
                    'missing': r.missing_scenarios if verbose else len(r.missing_scenarios),
                    'extra': r.extra_scenarios if verbose else len(r.extra_scenarios),
                }
                for r in results
            ],
            'all_missing': all_missing if verbose else len(all_missing),
        }
        return json.dumps(report_data, indent=2)

    elif output_format == 'csv':
        lines = ['testplan,total,executed,coverage_pct,missing_count,extra_count']
        for r in results:
            lines.append(f'{r.testplan_name},{r.total_scenarios},{r.executed_scenarios},'
                        f'{r.coverage_pct:.1f},{len(r.missing_scenarios)},{len(r.extra_scenarios)}')
        lines.append(f'TOTAL,{total_scenarios},{total_executed},{overall_pct:.1f},'
                    f'{len(all_missing)},0')
        return '\n'.join(lines)

    elif output_format == 'markdown':
        lines = [
            '# Scenario Coverage Report',
            '',
            '## Summary',
            '',
            f'- **Total Scenarios:** {total_scenarios}',
            f'- **Executed:** {total_executed}',
            f'- **Coverage:** {overall_pct:.1f}%',
            '',
            '## Coverage by Testplan',
            '',
            '| Testplan | Total | Executed | Coverage | Missing |',
            '|----------|-------|----------|----------|---------|',
        ]
        for r in sorted(results, key=lambda x: x.coverage_pct):
            lines.append(f'| {r.testplan_name} | {r.total_scenarios} | '
                        f'{r.executed_scenarios} | {r.coverage_pct:.1f}% | '
                        f'{len(r.missing_scenarios)} |')

        if verbose and all_missing:
            lines.extend([
                '',
                '## Missing Scenarios',
                '',
            ])
            for m in sorted(all_missing):
                lines.append(f'- {m}')

        return '\n'.join(lines)

    else:  # text format
        lines = [
            '=' * 70,
            'SCENARIO COVERAGE REPORT',
            '=' * 70,
            '',
            f'Total Scenarios: {total_scenarios}',
            f'Executed:        {total_executed}',
            f'Coverage:        {overall_pct:.1f}%',
            '',
            '-' * 70,
            f"{'Testplan':<30} {'Total':>8} {'Exec':>8} {'Cov%':>8} {'Missing':>8}",
            '-' * 70,
        ]

        for r in sorted(results, key=lambda x: x.coverage_pct):
            lines.append(f'{r.testplan_name:<30} {r.total_scenarios:>8} '
                        f'{r.executed_scenarios:>8} {r.coverage_pct:>7.1f}% '
                        f'{len(r.missing_scenarios):>8}')

        lines.extend([
            '-' * 70,
            f"{'TOTAL':<30} {total_scenarios:>8} {total_executed:>8} "
            f'{overall_pct:>7.1f}% {len(all_missing):>8}',
            '=' * 70,
        ])

        if verbose and all_missing:
            lines.extend([
                '',
                'MISSING SCENARIOS:',
                '-' * 70,
            ])
            for m in sorted(all_missing):
                lines.append(f'  - {m}')

        return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(
        description='Scenario Coverage Post-Processor',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    # Single log and testplan
    %(prog)s --log test_output.log --testplan q32_register_block_testplan.md

    # Directory of logs and testplans
    %(prog)s --log-dir ./test_results/ --testplan-dir ./testplans/

    # Verbose output with JSON format
    %(prog)s --log test.log --testplan plan.md -v --format json
        """
    )

    parser.add_argument('--log', '-l', type=Path,
                       help='Path to test log file')
    parser.add_argument('--log-dir', '-L', type=Path,
                       help='Directory containing test log files')
    parser.add_argument('--testplan', '-t', type=Path,
                       help='Path to testplan markdown file')
    parser.add_argument('--testplan-dir', '-T', type=Path,
                       help='Directory containing testplan markdown files')
    parser.add_argument('--format', '-f', choices=['text', 'markdown', 'json', 'csv'],
                       default='text', help='Output format (default: text)')
    parser.add_argument('--verbose', '-v', action='store_true',
                       help='Show detailed scenario lists')
    parser.add_argument('--output', '-o', type=Path,
                       help='Output file (default: stdout)')
    parser.add_argument('--exclude-quantizer', action='store_true',
                       help='Exclude quantizer testplan from analysis')

    args = parser.parse_args()

    # Validate arguments
    if not args.log and not args.log_dir:
        parser.error('Either --log or --log-dir is required')
    if not args.testplan and not args.testplan_dir:
        parser.error('Either --testplan or --testplan-dir is required')

    # Collect log content
    if args.log:
        with open(args.log, 'r', errors='ignore') as f:
            log_content = f.read()
    else:
        log_content = collect_logs_from_directory(args.log_dir)

    # Collect testplans
    testplans = []
    if args.testplan:
        testplans = [args.testplan]
    else:
        testplans = list(args.testplan_dir.glob('*_testplan.md'))
        # Also check for .yaml testplans
        testplans.extend(args.testplan_dir.glob('*_testplan.yaml'))
        testplans.extend(args.testplan_dir.glob('*_testplan.yml'))

    if not testplans:
        print('No testplan files found', file=sys.stderr)
        sys.exit(1)

    # Filter out quantizer if requested
    if args.exclude_quantizer:
        testplans = [t for t in testplans if 'quantizer' not in t.name.lower()]

    # Analyze each testplan
    results = []
    for tp in sorted(testplans):
        try:
            coverage = analyze_coverage(log_content, tp)
            results.append(coverage)
        except Exception as e:
            print(f'Error processing {tp}: {e}', file=sys.stderr)

    if not results:
        print('No testplans could be analyzed', file=sys.stderr)
        sys.exit(1)

    # Generate report
    report = generate_report(results, args.format, args.verbose)

    # Output
    if args.output:
        with open(args.output, 'w') as f:
            f.write(report)
        print(f'Report written to {args.output}')
    else:
        print(report)

    # Exit with non-zero if coverage < 100%
    total = sum(r.total_scenarios for r in results)
    executed = sum(r.executed_scenarios for r in results)
    if total > 0 and executed < total:
        sys.exit(1)
    sys.exit(0)


if __name__ == '__main__':
    main()
