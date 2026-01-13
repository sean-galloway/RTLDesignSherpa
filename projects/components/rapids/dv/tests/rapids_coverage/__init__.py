# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rapids_coverage/__init__.py
# Purpose: Coverage collection and reporting for RAPIDS beats component
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids/dv/tests/rapids_coverage
#
# Author: sean galloway
# Created: 2025-01-11

"""
RAPIDS Beats Coverage Collection Package

This package provides:
1. Code coverage collection via Verilator --coverage flag
2. Protocol coverage tracking for AXI/APB transactions
3. Functional coverage for FSM states and scenarios
4. Legal coverage calculation (against what RAPIDS actually supports)

Usage:
    from projects.components.rapids.dv.tests.rapids_coverage import (
        CoverageCollector,
        ProtocolCoverage,
        LegalCoverageConfig
    )
"""

from .coverage_collector import (
    CoverageCollector,
    CodeCoverageStats,
    get_coverage_compile_args,
    get_coverage_env,
)
from .protocol_coverage import ProtocolCoverage, CoverGroup, CoveragePoint
from .coverage_config import (
    RapidsCoverageConfig,
    LegalCoverageConfig,
    CoverageGoals,
)

__all__ = [
    'CoverageCollector',
    'CodeCoverageStats',
    'get_coverage_compile_args',
    'get_coverage_env',
    'ProtocolCoverage',
    'CoverGroup',
    'CoveragePoint',
    'RapidsCoverageConfig',
    'LegalCoverageConfig',
    'CoverageGoals',
]
