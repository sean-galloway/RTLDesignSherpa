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

Project-specific configurations (legal coverage specs, component-specific
scenarios) remain in each project's dv/{project}_coverage/ directory.

Structure:
    bin/cov_utils/                     # AGNOSTIC shared utilities (named to avoid shadowing)
        protocol_coverage_base.py      # Base classes for AXI/APB/AXIS coverage
        report_generator.py            # Report generation utilities
        verilator_coverage.py          # Verilator .dat file parsing
        config_base.py                 # Base configuration classes

    projects/components/{name}/dv/{name}_coverage/  # PROJECT-SPECIFIC
        {name}_legal_coverage.yaml     # Legal coverage spec for THIS component
        __init__.py                    # Project-specific exports
        (may extend base classes)

Usage:
    # Project-specific import (preferred)
    from projects.components.stream.dv.stream_coverage import CoverageHelper

    # Shared utilities import
    from bin.cov_utils import ProtocolCoverageBase, ReportGenerator
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
]
