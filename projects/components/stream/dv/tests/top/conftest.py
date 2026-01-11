"""
STREAM Top-Level Test Configuration for pytest

Configures the test environment for STREAM top-level integration tests.
Follows the established repository patterns (same as RAPIDS).

Coverage Features:
- Set COVERAGE=1 to enable code coverage collection
- Set COVERAGE_PROTOCOL=1 to enable protocol coverage collection
- Coverage reports are aggregated at session end
"""

import os
import sys
import logging
import json
import glob
from datetime import datetime
import pytest

# Configure pytest to always collect logs
def pytest_configure(config):
    # Add STREAM DV directory to path BEFORE pytest imports test modules
    # CRITICAL: Must be at position 0, even if already in sys.path from PYTHONPATH
    stream_dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))

    # Remove if already present (from PYTHONPATH), then insert at position 0
    if stream_dv_path in sys.path:
        sys.path.remove(stream_dv_path)
    sys.path.insert(0, stream_dv_path)

    # Create logs directory if it doesn't exist
    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)

    # Create coverage directory if coverage is enabled
    if os.environ.get('COVERAGE', '0') == '1':
        coverage_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "coverage_data")
        os.makedirs(os.path.join(coverage_dir, "per_test"), exist_ok=True)
        os.makedirs(os.path.join(coverage_dir, "merged"), exist_ok=True)
        os.makedirs(os.path.join(coverage_dir, "reports"), exist_ok=True)
        logging.info(f"Coverage enabled. Data will be stored in: {coverage_dir}")

    # Configure log file for pytest itself
    config.option.log_file = os.path.join(log_dir, "pytest_stream_top.log")
    config.option.log_file_level = "DEBUG"

    # Enable console logging
    config.option.log_cli = True
    config.option.log_cli_level = "INFO"

    # Register coverage-related markers
    config.addinivalue_line("markers", "coverage: Tests that collect coverage data")
    config.addinivalue_line("markers", "protocol_coverage: Tests that collect protocol coverage")


# Preserve all files regardless of test outcome
@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    """
    Called after whole test run finished, right before returning the exit status.
    Aggregates coverage data if coverage was enabled.
    """
    logging.info("STREAM top test session finished. Preserving all logs and build artifacts.")

    # Aggregate coverage if enabled
    if os.environ.get('COVERAGE', '0') == '1':
        _aggregate_coverage()


def _aggregate_coverage():
    """Aggregate all per-test coverage data into a merged report."""
    base_dir = os.path.dirname(os.path.abspath(__file__))
    coverage_dir = os.path.join(base_dir, "coverage_data")
    per_test_dir = os.path.join(coverage_dir, "per_test")
    merged_dir = os.path.join(coverage_dir, "merged")
    reports_dir = os.path.join(coverage_dir, "reports")

    # Find all summary files
    summary_files = glob.glob(os.path.join(per_test_dir, "*_summary.json"))

    if not summary_files:
        logging.info("No coverage data to aggregate")
        return

    # Aggregate protocol coverage
    merged_protocol = {
        'test_count': 0,
        'tests': [],
        'groups': {},
        'overall_protocol_pct': 0.0,
        'overall_line_pct': 0.0,
    }

    total_protocol_pct = 0.0
    total_line_pct = 0.0

    for summary_file in summary_files:
        try:
            with open(summary_file, 'r') as f:
                data = json.load(f)

            test_name = data.get('test_name', os.path.basename(summary_file))
            merged_protocol['tests'].append({
                'name': test_name,
                'protocol_pct': data.get('overall', {}).get('protocol_pct', 0),
                'line_pct': data.get('overall', {}).get('line_pct', 0),
            })

            total_protocol_pct += data.get('overall', {}).get('protocol_pct', 0)
            total_line_pct += data.get('overall', {}).get('line_pct', 0)
            merged_protocol['test_count'] += 1

            # Merge protocol groups
            protocol_data = data.get('protocol_coverage', {})
            for group_name, group_data in protocol_data.get('groups', {}).items():
                if group_name not in merged_protocol['groups']:
                    merged_protocol['groups'][group_name] = {
                        'covered': 0,
                        'total': 0,
                        'points': {}
                    }

                mg = merged_protocol['groups'][group_name]
                for point_name, point_data in group_data.get('points', {}).items():
                    if point_name not in mg['points']:
                        mg['points'][point_name] = {'hits': 0, 'goal': point_data.get('goal', 1)}
                    mg['points'][point_name]['hits'] += point_data.get('hits', 0)

        except Exception as e:
            logging.warning(f"Failed to parse {summary_file}: {e}")

    # Calculate merged coverage percentages
    if merged_protocol['test_count'] > 0:
        merged_protocol['overall_protocol_pct'] = total_protocol_pct / merged_protocol['test_count']
        merged_protocol['overall_line_pct'] = total_line_pct / merged_protocol['test_count']

    # Calculate per-group coverage
    for group_name, group_data in merged_protocol['groups'].items():
        covered = sum(1 for p in group_data['points'].values() if p['hits'] >= p['goal'])
        total = len(group_data['points'])
        group_data['covered'] = covered
        group_data['total'] = total
        group_data['coverage_pct'] = (covered / total * 100) if total > 0 else 0.0

    # Save merged data
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    merged_file = os.path.join(merged_dir, f"merged_coverage_{timestamp}.json")
    with open(merged_file, 'w') as f:
        json.dump(merged_protocol, f, indent=2)

    # Also save as latest
    latest_file = os.path.join(merged_dir, "latest_merged_coverage.json")
    with open(latest_file, 'w') as f:
        json.dump(merged_protocol, f, indent=2)

    # Generate text report
    _generate_coverage_report(merged_protocol, reports_dir, timestamp)

    logging.info(f"Coverage aggregated: {merged_protocol['test_count']} tests")
    logging.info(f"  Overall Protocol: {merged_protocol['overall_protocol_pct']:.1f}%")
    logging.info(f"  Overall Line:     {merged_protocol['overall_line_pct']:.1f}%")
    logging.info(f"  Report: {reports_dir}/coverage_report_{timestamp}.md")


def _generate_coverage_report(data: dict, reports_dir: str, timestamp: str):
    """Generate markdown coverage report."""
    os.makedirs(reports_dir, exist_ok=True)

    report_lines = []
    report_lines.append("# STREAM Top-Level Coverage Report")
    report_lines.append("")
    report_lines.append(f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    report_lines.append(f"**Tests Run:** {data['test_count']}")
    report_lines.append("")
    report_lines.append("## Summary")
    report_lines.append("")
    report_lines.append("| Metric | Coverage | Target | Status |")
    report_lines.append("|--------|----------|--------|--------|")

    protocol_pct = data['overall_protocol_pct']
    line_pct = data['overall_line_pct']

    protocol_status = "PASS" if protocol_pct >= 80 else "FAIL"
    line_status = "PASS" if line_pct >= 80 else "FAIL"

    report_lines.append(f"| Protocol Coverage | {protocol_pct:.1f}% | 80% | {protocol_status} |")
    report_lines.append(f"| Line Coverage | {line_pct:.1f}% | 80% | {line_status} |")
    report_lines.append("")

    report_lines.append("## Protocol Coverage by Group")
    report_lines.append("")
    report_lines.append("| Group | Covered | Total | Percentage |")
    report_lines.append("|-------|---------|-------|------------|")

    for group_name, group_data in sorted(data['groups'].items()):
        covered = group_data.get('covered', 0)
        total = group_data.get('total', 0)
        pct = group_data.get('coverage_pct', 0)
        report_lines.append(f"| {group_name} | {covered} | {total} | {pct:.1f}% |")

    report_lines.append("")
    report_lines.append("## Per-Test Results")
    report_lines.append("")
    report_lines.append("| Test Name | Protocol | Line |")
    report_lines.append("|-----------|----------|------|")

    for test in sorted(data['tests'], key=lambda x: x['name']):
        report_lines.append(f"| {test['name']} | {test['protocol_pct']:.1f}% | {test['line_pct']:.1f}% |")

    report_lines.append("")
    report_lines.append("## Coverage Gaps")
    report_lines.append("")

    # Find uncovered points
    uncovered = []
    for group_name, group_data in data['groups'].items():
        for point_name, point_data in group_data.get('points', {}).items():
            if point_data['hits'] < point_data['goal']:
                uncovered.append(f"- **{group_name}**: {point_name} (0 hits)")

    if uncovered:
        report_lines.append("The following coverage points were NOT hit:")
        report_lines.append("")
        report_lines.extend(uncovered[:50])  # Limit to first 50
        if len(uncovered) > 50:
            report_lines.append(f"... and {len(uncovered) - 50} more")
    else:
        report_lines.append("All coverage points were hit!")

    report_lines.append("")
    report_lines.append("---")
    report_lines.append("*Report generated by STREAM top-level coverage infrastructure*")

    # Write report
    report_file = os.path.join(reports_dir, f"coverage_report_{timestamp}.md")
    with open(report_file, 'w') as f:
        f.write('\n'.join(report_lines))

    # Also save as latest
    latest_file = os.path.join(reports_dir, "latest_coverage_report.md")
    with open(latest_file, 'w') as f:
        f.write('\n'.join(report_lines))


# Disable automatic test collection in the logs directory if it exists
def pytest_ignore_collect(collection_path, config):
    path_str = str(collection_path)
    return 'logs' in path_str or 'coverage_data' in path_str


# Test level fixture - provides test complexity level
@pytest.fixture(scope="function")
def test_level():
    """Test level fixture - can be overridden by TEST_LEVEL environment variable"""
    return os.environ.get('TEST_LEVEL', 'gate')


# Coverage fixtures
@pytest.fixture(scope="function")
def coverage_enabled():
    """Check if coverage collection is enabled."""
    return os.environ.get('COVERAGE', '0') == '1'


@pytest.fixture(scope="function")
def coverage_config():
    """Get coverage configuration."""
    from projects.components.stream.dv.stream_coverage import CoverageConfig
    return CoverageConfig.from_environment()
