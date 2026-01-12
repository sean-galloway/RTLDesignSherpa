# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rapids_coverage/__init__.py
# Purpose: Coverage collection and reporting for RAPIDS component
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids/dv/rapids_coverage
#
# Author: sean galloway
# Created: 2025-01-10

"""
RAPIDS Coverage Collection Package

This package provides:
1. Code coverage collection via Verilator --coverage flag
2. Protocol coverage tracking for AXI/APB transactions
3. Functional coverage for FSM states and scenarios
4. Coverage aggregation and reporting

Usage:
    from projects.components.rapids.dv.rapids_coverage import (
        CoverageCollector,
        ProtocolCoverage,
        generate_coverage_report
    )
"""

from .coverage_collector import CoverageCollector
from .protocol_coverage import ProtocolCoverage
from .coverage_config import CoverageConfig, LegalCoverageConfig
from .coverage_mixin import (
    CoverageHelper,
    CoverageMixin,
    get_coverage_compile_args,
    get_coverage_env,
    register_bfm_coverage
)

__all__ = [
    'CoverageCollector',
    'ProtocolCoverage',
    'CoverageConfig',
    'LegalCoverageConfig',
    'CoverageHelper',
    'CoverageMixin',
    'get_coverage_compile_args',
    'get_coverage_env',
    'register_bfm_coverage',
]
