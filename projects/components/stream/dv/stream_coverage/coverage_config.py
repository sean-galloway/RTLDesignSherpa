# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: coverage_config
# Purpose: Configuration for STREAM coverage collection
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream/dv/coverage
#
# Author: sean galloway
# Created: 2025-01-10

"""
Coverage Configuration for STREAM Component

Extends the shared coverage configuration base classes with STREAM-specific:
- Module lists
- Coverage goals
- Legal coverage definitions

Supports "legal coverage" mode where coverage is measured against
only the legal variations that STREAM actually supports, rather than
the full AXI4 protocol space. This gives realistic coverage numbers.

Usage:
    # Default: full protocol coverage
    config = StreamCoverageConfig()

    # Legal coverage mode: only STREAM-supported variations
    config = StreamCoverageConfig.from_environment()  # Set COVERAGE_LEGAL=1

    # Or load specific legal config
    legal_config = LegalCoverageConfig.load('stream')
"""

import os
from dataclasses import dataclass, field
from typing import List, Dict, Set
from pathlib import Path

# Import shared base classes
from bin.cov_utils import (
    CoverageConfigBase,
    CoverageGoals,
    CoverageType,
    LegalCoverageConfigBase,
)

# Re-export for backward compatibility
__all__ = [
    'CoverageType',
    'CoverageGoals',
    'StreamCoverageGoals',
    'ProtocolCoverageBins',
    'FunctionalCoverageBins',
    'CoverageConfig',
    'StreamCoverageConfig',
    'LegalCoverageConfig',
]


@dataclass
class StreamCoverageGoals(CoverageGoals):
    """Coverage goals for STREAM component - higher than defaults."""
    # Override defaults with STREAM-specific targets
    line_coverage_target: float = 90.0      # 90% line coverage
    toggle_coverage_target: float = 80.0    # 80% toggle coverage
    branch_coverage_target: float = 85.0    # 85% branch coverage
    protocol_coverage_target: float = 95.0  # 95% protocol coverage
    functional_coverage_target: float = 90.0 # 90% functional coverage


@dataclass
class ProtocolCoverageBins:
    """Define coverage bins for protocol transactions."""

    # AXI burst types
    axi_burst_types: List[str] = field(default_factory=lambda: [
        'FIXED', 'INCR', 'WRAP'
    ])

    # AXI burst sizes (2^size bytes per beat)
    axi_burst_sizes: List[int] = field(default_factory=lambda: [
        1, 2, 4, 8, 16, 32, 64, 128
    ])

    # AXI burst lengths (0-255 for AXI4)
    axi_burst_length_bins: List[tuple] = field(default_factory=lambda: [
        (0, 0, 'single'),        # Single beat
        (1, 3, 'short'),         # 2-4 beats
        (4, 7, 'medium'),        # 5-8 beats
        (8, 15, 'long'),         # 9-16 beats
        (16, 255, 'very_long'),  # 17-256 beats
    ])

    # AXI response types
    axi_response_types: List[str] = field(default_factory=lambda: [
        'OKAY', 'EXOKAY', 'SLVERR', 'DECERR'
    ])

    # APB transaction types
    apb_transaction_types: List[str] = field(default_factory=lambda: [
        'READ', 'WRITE'
    ])

    # APB response types
    apb_response_types: List[str] = field(default_factory=lambda: [
        'OKAY', 'ERROR'
    ])

    # Address alignment coverage
    address_alignment_bins: List[str] = field(default_factory=lambda: [
        'byte_aligned',      # Any address
        'halfword_aligned',  # 2-byte aligned
        'word_aligned',      # 4-byte aligned
        'dword_aligned',     # 8-byte aligned
        'cache_aligned',     # 64-byte aligned (typical cache line)
    ])


@dataclass
class FunctionalCoverageBins:
    """Define coverage bins for functional scenarios."""

    # Scheduler FSM states
    scheduler_states: List[str] = field(default_factory=lambda: [
        'IDLE', 'FETCH_DESC', 'PARSE_DESC', 'DISPATCH',
        'WAIT_COMPLETE', 'HANDLE_ERROR', 'CHAIN_NEXT'
    ])

    # Descriptor engine states
    descriptor_engine_states: List[str] = field(default_factory=lambda: [
        'IDLE', 'READ_DESC', 'PARSE', 'EXECUTE', 'COMPLETE', 'ERROR'
    ])

    # SRAM controller states
    sram_controller_states: List[str] = field(default_factory=lambda: [
        'IDLE', 'READ', 'WRITE', 'ALLOC', 'DEALLOC'
    ])

    # Scenario coverage
    scenarios: List[str] = field(default_factory=lambda: [
        'single_descriptor',
        'chained_descriptors',
        'concurrent_read_write',
        'back_to_back_transactions',
        'error_injection',
        'timeout_recovery',
        'full_pipeline',
        'backpressure_handling',
    ])


@dataclass
class StreamCoverageConfig(CoverageConfigBase):
    """STREAM-specific coverage configuration."""

    # Override goals with STREAM-specific targets
    goals: StreamCoverageGoals = field(default_factory=StreamCoverageGoals)

    # Coverage bin definitions (STREAM-specific)
    protocol_bins: ProtocolCoverageBins = field(default_factory=ProtocolCoverageBins)
    functional_bins: FunctionalCoverageBins = field(default_factory=FunctionalCoverageBins)

    # STREAM modules to include in coverage
    include_modules: List[str] = field(default_factory=lambda: [
        'scheduler',
        'descriptor_engine',
        'sram_controller',
        'stream_latency_bridge',
        'perf_profiler',
        'apbtodescr',
        'stream_core',
        'datapath_rd_test',
        'datapath_wr_test',
        'stream_top',
    ])

    def get_merged_coverage_path(self) -> str:
        """Get path for merged coverage data."""
        return os.path.join(self.coverage_dir, self.merged_dir)

    def get_report_path(self, report_name: str = "coverage_report") -> str:
        """Get path for coverage report."""
        return os.path.join(self.coverage_dir, self.report_dir, report_name)


# Backward compatibility alias
CoverageConfig = StreamCoverageConfig


# ===========================================================================
# Legal Coverage Configuration
# ===========================================================================

@dataclass
class LegalCoverageConfig(LegalCoverageConfigBase):
    """
    Legal coverage configuration for STREAM component.

    Extends LegalCoverageConfigBase with STREAM-specific defaults.

    Defines which coverage points are "legal" (expected to be covered)
    vs "illegal" (not applicable to STREAM's usage pattern).

    This allows coverage to be calculated against a realistic subset
    of the full AXI4 protocol space.
    """

    name: str = "stream"
    description: str = "STREAM DMA engine legal coverage points"

    # AXI burst types that STREAM uses
    legal_burst_types: Set[str] = field(default_factory=lambda: {'INCR'})
    illegal_burst_types: Set[str] = field(default_factory=lambda: {'FIXED', 'WRAP'})

    # AXI burst sizes that STREAM uses (in bytes)
    legal_burst_sizes: Set[int] = field(default_factory=lambda: {64})
    illegal_burst_sizes: Set[int] = field(default_factory=lambda: {1, 2, 4, 8, 16, 32, 128})

    # AXI burst length bins that STREAM uses
    legal_burst_lengths: Set[str] = field(default_factory=lambda: {'len_1', 'len_5_8'})
    optional_burst_lengths: Set[str] = field(default_factory=lambda: {'len_2_4', 'len_9_16', 'len_17_256'})

    # AXI responses that STREAM should handle
    legal_responses: Set[str] = field(default_factory=lambda: {'OKAY', 'SLVERR'})
    illegal_responses: Set[str] = field(default_factory=lambda: {'EXOKAY'})
    optional_responses: Set[str] = field(default_factory=lambda: {'DECERR'})

    # APB transactions
    legal_apb: Set[str] = field(default_factory=lambda: {'write_okay', 'read_okay'})
    optional_apb: Set[str] = field(default_factory=lambda: {'write_error', 'read_error'})

    # Address alignment
    legal_alignment: Set[str] = field(default_factory=lambda: {'cache_line', 'dword'})
    optional_alignment: Set[str] = field(default_factory=lambda: {'qword', 'word'})
    illegal_alignment: Set[str] = field(default_factory=lambda: {'halfword', 'unaligned'})

    # Handshakes
    legal_handshakes: Set[str] = field(default_factory=lambda: {
        'desc_valid_ready', 'desc_done', 'mem_cmd_valid_ready',
        'mem_data_valid_ready', 'backpressure_stall'
    })
    optional_handshakes: Set[str] = field(default_factory=lambda: {
        'network_tx_valid_ready', 'network_rx_valid_ready',
        'scheduler_to_read_engine', 'scheduler_to_write_engine',
        'read_engine_complete', 'write_engine_complete', 'pipeline_bubble'
    })

    # Scenarios
    critical_scenarios: Set[str] = field(default_factory=lambda: {
        'single_desc', 'chained_desc', 'error_handling', 'timeout_recovery'
    })
    important_scenarios: Set[str] = field(default_factory=lambda: {
        'concurrent_rw', 'back_to_back', 'backpressure'
    })
    optional_scenarios: Set[str] = field(default_factory=lambda: {
        'full_pipeline', 'max_outstanding', 'empty_desc', 'wrap_burst', 'narrow_transfer'
    })

    # Cross coverage
    legal_cross: Set[str] = field(default_factory=lambda: {'INCR_size64'})

    @classmethod
    def load(cls, config_name: str = 'stream') -> 'LegalCoverageConfig':
        """Load legal coverage config from YAML file.

        Args:
            config_name: Name of the config (e.g., 'stream')

        Returns:
            LegalCoverageConfig with values from YAML file
        """
        # Try to load YAML file
        config_dir = Path(__file__).parent
        yaml_file = config_dir / f"{config_name}_legal_coverage.yaml"

        if not yaml_file.exists():
            # Return default config
            return cls()

        # Use base class YAML loader
        base_config = LegalCoverageConfigBase.load_yaml(str(yaml_file))

        # Create STREAM config with loaded values
        config = cls(
            name=base_config.name,
            description=base_config.description,
            legal_burst_types=base_config.legal_burst_types or cls().legal_burst_types,
            illegal_burst_types=base_config.illegal_burst_types or cls().illegal_burst_types,
            legal_burst_sizes=base_config.legal_burst_sizes or cls().legal_burst_sizes,
            illegal_burst_sizes=base_config.illegal_burst_sizes or cls().illegal_burst_sizes,
            legal_burst_lengths=base_config.legal_burst_lengths or cls().legal_burst_lengths,
            optional_burst_lengths=base_config.optional_burst_lengths or cls().optional_burst_lengths,
            legal_responses=base_config.legal_responses or cls().legal_responses,
            illegal_responses=base_config.illegal_responses or cls().illegal_responses,
            optional_responses=base_config.optional_responses or cls().optional_responses,
            legal_apb=base_config.legal_apb or cls().legal_apb,
            optional_apb=base_config.optional_apb or cls().optional_apb,
            legal_alignment=base_config.legal_alignment or cls().legal_alignment,
            optional_alignment=base_config.optional_alignment or cls().optional_alignment,
            illegal_alignment=base_config.illegal_alignment or cls().illegal_alignment,
            legal_handshakes=base_config.legal_handshakes or cls().legal_handshakes,
            optional_handshakes=base_config.optional_handshakes or cls().optional_handshakes,
            critical_scenarios=base_config.critical_scenarios or cls().critical_scenarios,
            important_scenarios=base_config.important_scenarios or cls().important_scenarios,
            optional_scenarios=base_config.optional_scenarios or cls().optional_scenarios,
            legal_cross=base_config.legal_cross or cls().legal_cross,
        )

        return config
