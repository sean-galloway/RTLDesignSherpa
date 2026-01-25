"""
Retro Legacy Blocks Test Configuration for pytest

Configures the test environment for RLB peripheral validation (HPET, GPIO, UART, etc.),
following the established repository patterns.

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

# Add repository paths before any test imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
sys.path.insert(0, repo_root)
sys.path.insert(0, os.path.join(repo_root, 'bin'))


def get_coverage_compile_args():
    """Get Verilator compile arguments for coverage collection.

    Usage in test files:
        from conftest import get_coverage_compile_args
        compile_args.extend(get_coverage_compile_args())

    Enable coverage by setting COVERAGE=1 environment variable.
    """
    if os.environ.get('COVERAGE', '0') != '1':
        return []
    return [
        '--coverage',
        '--coverage-line',
        '--coverage-toggle',
        '--coverage-underscore',
    ]


def pytest_configure(config):
    """Configure pytest for Retro Legacy Blocks testing"""
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
    config.option.log_file = os.path.join(log_dir, "pytest_rlb.log")
    config.option.log_file_level = "DEBUG"

    # Enable console logging
    config.option.log_cli = True
    config.option.log_cli_level = "INFO"

    # Test level markers
    config.addinivalue_line("markers", "basic: Basic functionality tests")
    config.addinivalue_line("markers", "medium: Medium complexity tests")
    config.addinivalue_line("markers", "full: Full comprehensive tests")

    # Feature markers
    config.addinivalue_line("markers", "register_access: Register access tests")
    config.addinivalue_line("markers", "timer_operation: Timer operation tests")
    config.addinivalue_line("markers", "counter_operation: Counter operation tests")
    config.addinivalue_line("markers", "interrupt_handling: Interrupt handling tests")
    config.addinivalue_line("markers", "periodic_mode: Periodic timer mode tests")
    config.addinivalue_line("markers", "oneshot_mode: One-shot timer mode tests")
    config.addinivalue_line("markers", "clock_domain_crossing: CDC tests")

    # Configuration markers
    config.addinivalue_line("markers", "two_timer: 2-timer configuration tests")
    config.addinivalue_line("markers", "three_timer: 3-timer configuration tests")
    config.addinivalue_line("markers", "eight_timer: 8-timer configuration tests")

    # Performance markers
    config.addinivalue_line("markers", "stress: Stress testing")
    config.addinivalue_line("markers", "regression: Regression test suite")
    config.addinivalue_line("markers", "coverage: Tests that collect coverage data")

    # Block-specific markers
    config.addinivalue_line("markers", "hpet: HPET tests")
    config.addinivalue_line("markers", "gpio: GPIO tests")
    config.addinivalue_line("markers", "uart: UART tests")
    config.addinivalue_line("markers", "pic: 8259 PIC tests")
    config.addinivalue_line("markers", "pit: 8254 PIT tests")
    config.addinivalue_line("markers", "rtc: RTC tests")
    config.addinivalue_line("markers", "smbus: SMBus tests")
    config.addinivalue_line("markers", "pm_acpi: PM/ACPI tests")
    config.addinivalue_line("markers", "ioapic: IOAPIC tests")


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    """Called after whole test run finished"""
    logging.info("Retro Legacy Blocks test session finished. Preserving all logs and build artifacts.")

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
    report_lines.append("# Retro Legacy Blocks Coverage Report")
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
    report_lines.append("---")
    report_lines.append("*Report generated by Retro Legacy Blocks coverage infrastructure*")

    # Write report
    report_file = os.path.join(reports_dir, f"coverage_report_{timestamp}.md")
    with open(report_file, 'w') as f:
        f.write('\n'.join(report_lines))

    # Also save as latest
    latest_file = os.path.join(reports_dir, "latest_coverage_report.md")
    with open(latest_file, 'w') as f:
        f.write('\n'.join(report_lines))


def pytest_ignore_collect(collection_path, config):
    """Disable automatic test collection in logs and coverage directories"""
    path_str = str(collection_path)
    return 'logs' in path_str or 'coverage_data' in path_str


# HPET-specific parametrization fixtures (kept from original)
@pytest.fixture(scope="module", params=[
    # Timer configurations: (num_timers, vendor_id, revision_id, description)
    (2, 0x8086, 1, "2-timer Intel-like"),
    (3, 0x1022, 2, "3-timer AMD-like"),
    (8, 0x43981, 16, "8-timer custom"),
])
def hpet_timer_config(request):
    """APB HPET timer configuration parameters"""
    num_timers, vendor_id, revision_id, description = request.param
    return {
        'NUM_TIMERS': num_timers,
        'VENDOR_ID': vendor_id,
        'REVISION_ID': revision_id,
        'description': description
    }


@pytest.fixture(scope="module", params=[
    # CDC configurations: (cdc_enable, description)
    (0, "no CDC"),
    (1, "with CDC"),
])
def hpet_cdc_config(request):
    """APB HPET clock domain crossing configuration"""
    cdc_enable, description = request.param
    return {
        'CDC_ENABLE': cdc_enable,
        'description': description
    }


@pytest.fixture(scope="module", params=[
    # Test levels: (level, description, test_count, timeout_factor)
    ('basic', 'Basic functionality', 4, 1.0),
    ('medium', 'Medium stress testing', 5, 1.5),
    ('full', 'Full comprehensive testing', 3, 2.0),
])
def hpet_test_level(request):
    """APB HPET test level configuration"""
    level, description, test_count, timeout_factor = request.param

    # Override from environment if specified
    env_level = os.environ.get('TEST_LEVEL', level).lower()
    if env_level in ['basic', 'medium', 'full']:
        level = env_level

    return {
        'level': level,
        'description': description,
        'test_count': test_count,
        'timeout_factor': timeout_factor
    }


@pytest.fixture(scope="module", params=[
    # Timer mode configurations: (mode, description)
    ('one-shot', 'One-shot mode'),
    ('periodic', 'Periodic mode'),
])
def hpet_timer_mode(request):
    """APB HPET timer mode configuration"""
    mode, description = request.param
    return {
        'mode': mode,
        'description': description
    }


# APB HPET-specific environment variable helpers
def get_hpet_env_config():
    """Get APB HPET configuration from environment variables"""
    return {
        'NUM_TIMERS': int(os.environ.get('HPET_NUM_TIMERS', '2')),
        'VENDOR_ID': int(os.environ.get('HPET_VENDOR_ID', '0x8086')),
        'REVISION_ID': int(os.environ.get('HPET_REVISION_ID', '1')),
        'CDC_ENABLE': int(os.environ.get('HPET_CDC_ENABLE', '0')),
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', 'basic').lower(),
        'ENABLE_COVERAGE': os.environ.get('ENABLE_COVERAGE', '0') == '1',
        'ENABLE_WAVEDUMP': os.environ.get('ENABLE_WAVEDUMP', '1') == '1',
    }


# Test collection hooks for RLB-specific organization
def pytest_collection_modifyitems(config, items):
    """Modify test collection to add RLB-specific markers"""
    for item in items:
        # Add markers based on test file patterns
        if "basic" in item.nodeid:
            item.add_marker(pytest.mark.basic)
        elif "medium" in item.nodeid:
            item.add_marker(pytest.mark.medium)
        elif "full" in item.nodeid:
            item.add_marker(pytest.mark.full)

        # Add block-specific markers
        if "hpet" in item.nodeid.lower():
            item.add_marker(pytest.mark.hpet)
        elif "gpio" in item.nodeid.lower():
            item.add_marker(pytest.mark.gpio)
        elif "uart" in item.nodeid.lower():
            item.add_marker(pytest.mark.uart)
        elif "pic" in item.nodeid.lower() or "8259" in item.nodeid:
            item.add_marker(pytest.mark.pic)
        elif "pit" in item.nodeid.lower() or "8254" in item.nodeid:
            item.add_marker(pytest.mark.pit)
        elif "rtc" in item.nodeid.lower():
            item.add_marker(pytest.mark.rtc)
        elif "smbus" in item.nodeid.lower():
            item.add_marker(pytest.mark.smbus)
        elif "pm_acpi" in item.nodeid.lower() or "acpi" in item.nodeid.lower():
            item.add_marker(pytest.mark.pm_acpi)
        elif "ioapic" in item.nodeid.lower():
            item.add_marker(pytest.mark.ioapic)

        # Add feature-specific markers
        feature_markers = {
            'register': 'register_access',
            'timer': 'timer_operation',
            'counter': 'counter_operation',
            'interrupt': 'interrupt_handling',
            'periodic': 'periodic_mode',
            'oneshot': 'oneshot_mode',
            'cdc': 'clock_domain_crossing',
        }

        for feature, marker in feature_markers.items():
            if feature in item.nodeid.lower():
                item.add_marker(getattr(pytest.mark, marker))


# Coverage fixtures
@pytest.fixture(scope="function")
def coverage_enabled():
    """Check if coverage collection is enabled."""
    return os.environ.get('COVERAGE', '0') == '1'


@pytest.fixture(scope="function")
def test_level():
    """Test level fixture - can be overridden by TEST_LEVEL environment variable"""
    return os.environ.get('TEST_LEVEL', 'basic')
