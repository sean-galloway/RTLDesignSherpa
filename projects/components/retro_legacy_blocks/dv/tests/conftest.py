"""Retro Legacy Blocks test configuration for pytest.

The coverage/log boilerplate (log dir, coverage dir creation, log-file config,
marker registration, session-end coverage aggregation, scratch-dir ignore)
lives in ``bin/cov_utils/conftest_base.py`` -- the SAME shared base the val
areas, stream and rapids use. This file declares only the area-specific bits.

This replaced a hand-written conftest that re-implemented that boilerplate
locally, including a private ~175-line _aggregate_coverage/_generate_coverage_report
pair duplicating cov_utils.conftest_coverage.aggregate_all_coverage, and a local
get_coverage_compile_args whose docstring advertised
``from conftest import get_coverage_compile_args`` -- which nothing in the repo
ever did. The shared one is re-exported below instead.

Coverage: `COVERAGE=1` (line) / `COVERAGE_PROTOCOL=1` (protocol); aggregated at
session end by the shared base.
"""

import os
import sys

# Repo root + bin for the shared conftest base. env_python already exports these
# on PYTHONPATH -- added here too so a bare pytest invocation still resolves them.
_here = os.path.dirname(os.path.abspath(__file__))
_repo_root = os.path.abspath(os.path.join(_here, '../../../../..'))
for _p in (_repo_root, os.path.join(_repo_root, 'bin')):
    if _p in sys.path:
        sys.path.remove(_p)
    sys.path.insert(0, _p)

import pytest  # noqa: E402
from cov_utils.conftest_base import configure, sessionfinish, ignore_collect  # noqa: E402
from cov_utils.conftest_coverage import get_coverage_compile_args  # noqa: E402,F401 -- re-exported for test files

AREA_NAME = 'Retro Legacy Blocks'
LOG_BASENAME = 'pytest_rlb.log'
MARKERS = (
    'basic: Basic functionality tests',
    'medium: Medium complexity tests',
    'full: Full comprehensive tests',
    'register_access: Register access tests',
    'timer_operation: Timer operation tests',
    'counter_operation: Counter operation tests',
    'interrupt_handling: Interrupt handling tests',
    'periodic_mode: Periodic timer mode tests',
    'oneshot_mode: One-shot timer mode tests',
    'clock_domain_crossing: CDC tests',
    'two_timer: 2-timer configuration tests',
    'three_timer: 3-timer configuration tests',
    'eight_timer: 8-timer configuration tests',
    'stress: Stress testing',
    'regression: Regression test suite',
    'coverage: Tests that collect coverage data',
    'protocol_coverage: Tests that collect protocol coverage',
    'hpet: HPET tests',
    'gpio: GPIO tests',
    'uart: UART tests',
    'pic: 8259 PIC tests',
    'pit: 8254 PIT tests',
    'rtc: RTC tests',
    'smbus: SMBus tests',
    'pm_acpi: PM/ACPI tests',
    'ioapic: IOAPIC tests',
)


def pytest_configure(config):
    configure(config, __file__, LOG_BASENAME, markers=MARKERS)


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    sessionfinish(__file__, AREA_NAME)


def pytest_ignore_collect(collection_path, config):
    return ignore_collect(collection_path)


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


# NOTE: hpet_timer_config, hpet_cdc_config, hpet_test_level, hpet_timer_mode and
# get_hpet_env_config used to live here. All five were dead -- measured
# 2026-09-14, nothing in the repo requests or imports any of them -- and the
# first four were module-scoped params fixtures that would have multiplied
# collection 3 x 2 x 3 x 2 had anything asked for one. hpet_test_level also
# encoded a SECOND level model with its own test_count/timeout_factor table,
# conflicting with the reg_level_grid()/level_env() axis the wrappers use.
# Removed so that axis is the only level mechanism in this area.

# ----------------------------------------------------------------------
# Fixtures (kept local to this area)
# ----------------------------------------------------------------------
@pytest.fixture(scope="function")
def coverage_enabled():
    """Check if coverage collection is enabled."""
    return os.environ.get('COVERAGE', '0') == '1'


@pytest.fixture(scope="function")
def test_level():
    """Test level fixture - can be overridden by TEST_LEVEL environment variable.

    NOTE this is the fallback for a bare `pytest` run. Every wrapper in this area
    parametrizes `test_level` over reg_level_grid() and exports it with
    level_env(), and a parametrized argument takes precedence over a fixture of
    the same name -- so in a normal `make run-all-*` run this body does not
    execute.
    """
    return os.environ.get('TEST_LEVEL', 'gate')

# ----------------------------------------------------------------------
# NO REG_LEVEL -> TEST_LEVEL STAMP HERE. DELIBERATELY.
# ----------------------------------------------------------------------
# There used to be one, and it was load-bearing while the wrappers exported
# nothing: without it `make run-all-full-parallel` fell back to the default
# depth and ran a smaller matrix while still reporting "passed".
#
# The trap is what it does once the wrappers DO export a per-cell level.
# cocotb_test's set_env applies extra_env first and then copies every
# os.environ entry over it, so a process-level TEST_LEVEL beats the value the
# wrapper just passed. The REG_LEVEL grid still expanded to gate/func/full
# cells and every one of them ran at the same depth. MEASURED HERE on
# 2026-09-11 before the conversion: pm_acpi's gate, func and full cells each
# logged "Starting FULL PM_ACPI" and each ran the identical 57 tests.
# Re-stamping the cell's own value from the wrapper does not help either;
# that was measured on the bridge and is written up in
# TBClasses.shared.test_levels.
#
# So the area converts both halves at once: every wrapper parametrizes on
# reg_level_grid() and passes level_env(test_level), and this stamp is gone.
# Removing the stamp alone would drop the area to the default depth, which is
# why this comment exists rather than a blank space.
