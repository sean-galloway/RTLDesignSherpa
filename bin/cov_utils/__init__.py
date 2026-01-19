# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: bin/cov_utils/__init__.py
# Purpose: Shared coverage collection and reporting utilities
# Note: Named cov_utils (not coverage) to avoid shadowing Python's coverage package
#
# Author: sean galloway
# Created: 2025-01-10

"""
Shared Coverage Collection Package

This package provides AGNOSTIC coverage utilities that can be used by any project:
1. Protocol coverage base classes (AXI, APB, AXIS)
2. Report generation utilities (Verilator coverage parsing, report formatting)
3. Configuration base classes
4. Generic coverage report generator script

Project-specific configurations (legal coverage specs, component-specific
scenarios) remain in each project's dv/{project}_coverage/ directory.

Structure:
    bin/cov_utils/                     # AGNOSTIC shared utilities (named to avoid shadowing)
        generate_coverage_report.py    # ★ CLI script: generic coverage report generator
        protocol_coverage_base.py      # Base classes for AXI/APB/AXIS coverage
        report_generator.py            # Report generation utilities
        verilator_coverage.py          # Verilator .dat file parsing
        config_base.py                 # Base configuration classes

    projects/components/{name}/dv/{name}_coverage/  # PROJECT-SPECIFIC
        {name}_legal_coverage.yaml     # Legal coverage spec for THIS component
        __init__.py                    # Project-specific exports
        (may extend base classes)

Usage - Command Line:
    # Auto-detect component from current directory
    python bin/cov_utils/generate_coverage_report.py

    # Specify component explicitly
    python bin/cov_utils/generate_coverage_report.py --component rapids
    python bin/cov_utils/generate_coverage_report.py --component stream

    # Generate HTML report with legal coverage
    python bin/cov_utils/generate_coverage_report.py --html --legal

Usage - Python API:
    # Shared utilities import
    from bin.cov_utils import ProtocolCoverageBase, ReportGenerator

    # Project-specific import (preferred for extending)
    from projects.components.stream.dv.stream_coverage import CoverageHelper
"""

from .protocol_coverage_base import (
    ProtocolCoverageBase,
    CoveragePoint,
    CoverGroup,
    AxiBurstType,
    AxiResponse,
    ApbResponse,
)
from .verilator_coverage import (
    parse_verilator_coverage_file,
    get_merged_verilator_coverage,
    parse_coverage_stats,
)
from .report_generator import (
    ReportGenerator,
    generate_coverage_report,
    generate_markdown_report,
)
from .config_base import (
    CoverageType,
    CoverageGoals,
    CoverageConfigBase,
    LegalCoverageConfigBase,
)

import os


def get_coverage_compile_args():
    """
    Get Verilator compile arguments for coverage collection.

    Returns coverage-related compile args if COVERAGE=1 is set, otherwise empty list.

    Usage in test pytest wrapper:
        from cov_utils import get_coverage_compile_args
        compile_args.extend(get_coverage_compile_args())

    Or in test file:
        from bin.cov_utils import get_coverage_compile_args
        compile_args.extend(get_coverage_compile_args())
    """
    if os.environ.get('COVERAGE', '0') != '1':
        return []

    return [
        '--coverage',
        '--coverage-line',
        '--coverage-toggle',
        '--coverage-underscore',
    ]


def get_coverage_env(test_name: str, sim_build: str = None) -> dict:
    """
    Get environment variables for coverage collection.

    Args:
        test_name: Unique test name for coverage file naming
        sim_build: Path to simulation build directory (for Verilator line coverage)

    Returns:
        Dict of environment variables to set for coverage
    """
    if os.environ.get('COVERAGE', '0') != '1':
        return {}

    env = {
        'COVERAGE_TEST_NAME': test_name,
    }

    if sim_build:
        env['COVERAGE_SIM_BUILD'] = os.path.abspath(sim_build)

    return env


__all__ = [
    # Protocol coverage base
    'ProtocolCoverageBase',
    'CoveragePoint',
    'CoverGroup',
    'AxiBurstType',
    'AxiResponse',
    'ApbResponse',
    # Verilator utilities
    'parse_verilator_coverage_file',
    'get_merged_verilator_coverage',
    'parse_coverage_stats',
    # Report generation
    'ReportGenerator',
    'generate_coverage_report',
    'generate_markdown_report',
    # Configuration
    'CoverageType',
    'CoverageGoals',
    'CoverageConfigBase',
    'LegalCoverageConfigBase',
    # Compile args helpers
    'get_coverage_compile_args',
    'get_coverage_env',
]
