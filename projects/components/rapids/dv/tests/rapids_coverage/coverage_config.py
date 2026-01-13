# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: coverage_config
# Purpose: Configuration for RAPIDS beats coverage collection
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids/dv/tests/rapids_coverage
#
# Author: sean galloway
# Created: 2025-01-11

"""
Coverage Configuration for RAPIDS Beats Component

Provides:
- Coverage goals and thresholds
- Module lists for coverage inclusion
- Legal coverage definitions from YAML

Supports "legal coverage" mode where coverage is measured against
only the legal variations that RAPIDS actually supports, rather than
the full AXI4 protocol space.

Usage:
    # Default configuration
    config = RapidsCoverageConfig()

    # Legal coverage mode: only RAPIDS-supported variations
    legal_config = LegalCoverageConfig.load('rapids')
"""

import os
import yaml
from dataclasses import dataclass, field
from typing import List, Dict, Set, Optional
from pathlib import Path


@dataclass
class CoverageGoals:
    """Coverage targets for RAPIDS component."""
    line_coverage_target: float = 60.0       # 60% line coverage (initial target)
    toggle_coverage_target: float = 50.0     # 50% toggle coverage
    branch_coverage_target: float = 55.0     # 55% branch coverage
    protocol_coverage_target: float = 80.0   # 80% protocol coverage
    functional_coverage_target: float = 70.0 # 70% functional coverage


@dataclass
class RapidsCoverageConfig:
    """RAPIDS-specific coverage configuration."""

    # Coverage goals
    goals: CoverageGoals = field(default_factory=CoverageGoals)

    # Directory structure
    coverage_dir: str = "coverage_data"
    per_test_dir: str = "per_test"
    merged_dir: str = "merged"
    report_dir: str = "reports"

    # RAPIDS modules to include in coverage
    include_modules: List[str] = field(default_factory=lambda: [
        # FUB-level modules
        'scheduler_beats',
        'descriptor_engine_beats',
        'axi_read_engine_beats',
        'axi_write_engine_beats',
        'alloc_ctrl_beats',
        'drain_ctrl_beats',
        'latency_bridge_beats',
        # Macro-level modules
        'snk_data_path_beats',
        'snk_data_path_axis_beats',
        'src_data_path_beats',
        'src_data_path_axis_beats',
        'snk_sram_controller_beats',
        'src_sram_controller_beats',
        'scheduler_group_beats',
        'scheduler_group_array_beats',
    ])

    # Coverage types to collect
    collect_line: bool = True
    collect_toggle: bool = True
    collect_branch: bool = True

    @classmethod
    def from_environment(cls) -> 'RapidsCoverageConfig':
        """Create config from environment variables."""
        config = cls()

        # Override goals from environment
        if os.environ.get('COVERAGE_LINE_TARGET'):
            config.goals.line_coverage_target = float(os.environ['COVERAGE_LINE_TARGET'])
        if os.environ.get('COVERAGE_PROTOCOL_TARGET'):
            config.goals.protocol_coverage_target = float(os.environ['COVERAGE_PROTOCOL_TARGET'])

        # Override directory from environment
        if os.environ.get('COVERAGE_DIR'):
            config.coverage_dir = os.environ['COVERAGE_DIR']

        return config


@dataclass
class LegalCoverageConfig:
    """
    Legal coverage configuration for RAPIDS component.

    Defines which coverage points are "legal" (expected to be covered)
    vs "illegal" (not applicable to RAPIDS's usage pattern).

    This allows coverage to be calculated against a realistic subset
    of the full AXI4 protocol space.
    """

    name: str = "rapids"
    description: str = "RAPIDS beats architecture legal coverage points"

    # AXI burst types that RAPIDS uses
    legal_burst_types: Set[str] = field(default_factory=lambda: {'INCR'})
    illegal_burst_types: Set[str] = field(default_factory=lambda: {'FIXED', 'WRAP'})

    # AXI burst sizes that RAPIDS uses (in bytes)
    legal_burst_sizes: Set[str] = field(default_factory=lambda: {'size_64'})
    illegal_burst_sizes: Set[str] = field(default_factory=lambda: {
        'size_1', 'size_2', 'size_4', 'size_8', 'size_16', 'size_32', 'size_128'
    })
    optional_burst_sizes: Set[str] = field(default_factory=lambda: {'size_32'})

    # AXI burst lengths
    legal_burst_lengths: Set[str] = field(default_factory=lambda: {
        'len_1', 'len_2', 'len_4', 'len_8'
    })
    optional_burst_lengths: Set[str] = field(default_factory=lambda: {'len_16', 'len_32'})
    illegal_burst_lengths: Set[str] = field(default_factory=lambda: {'len_256'})

    # AXI responses that RAPIDS should handle
    legal_responses: Set[str] = field(default_factory=lambda: {'OKAY', 'SLVERR'})
    optional_responses: Set[str] = field(default_factory=lambda: {'DECERR'})
    illegal_responses: Set[str] = field(default_factory=lambda: {'EXOKAY'})

    # APB transactions
    legal_apb: Set[str] = field(default_factory=lambda: {'write_kick_off', 'write_okay'})
    optional_apb: Set[str] = field(default_factory=lambda: {'write_rejected'})
    illegal_apb: Set[str] = field(default_factory=lambda: {'read'})

    # Address alignment
    legal_alignment: Set[str] = field(default_factory=lambda: {
        'cache_line_aligned', 'dword_aligned'
    })
    optional_alignment: Set[str] = field(default_factory=lambda: {'word_aligned'})
    illegal_alignment: Set[str] = field(default_factory=lambda: {'unaligned'})

    # Handshakes
    legal_handshakes: Set[str] = field(default_factory=lambda: {
        'desc_valid_ready', 'apb_valid_ready',
        'ar_valid_ready', 'r_valid_ready',
        'sched_rd_valid_start', 'sched_wr_valid_start',
        'rd_done_strobe', 'wr_done_strobe',
        'ar_handshake', 'r_handshake',
        'aw_handshake', 'w_handshake', 'b_handshake',
        'alloc_req', 'drain_req',
    })
    optional_handshakes: Set[str] = field(default_factory=lambda: {
        'sram_wr_valid_ready', 'sram_rd_valid_ready',
        'ar_wait', 'r_wait', 'aw_wait', 'w_wait',
        'sram_full', 'sram_empty',
    })

    # Scheduler states
    legal_scheduler_states: Set[str] = field(default_factory=lambda: {
        'CH_IDLE', 'CH_FETCH_DESC', 'CH_XFER_DATA', 'CH_COMPLETE', 'CH_NEXT_DESC'
    })
    optional_scheduler_states: Set[str] = field(default_factory=lambda: {'CH_ERROR'})

    # Descriptor engine states
    legal_desc_engine_states: Set[str] = field(default_factory=lambda: {
        'RD_IDLE', 'RD_ISSUE_ADDR', 'RD_WAIT_DATA', 'RD_COMPLETE'
    })
    optional_desc_engine_states: Set[str] = field(default_factory=lambda: {'RD_ERROR'})

    # Scenarios
    critical_scenarios: Set[str] = field(default_factory=lambda: {
        'single_descriptor_complete', 'chained_descriptor_complete',
        'concurrent_read_write', 'backpressure_handling'
    })
    important_scenarios: Set[str] = field(default_factory=lambda: {
        'multi_channel_arbitration', 'burst_size_variations',
        'error_flag_propagation', 'descriptor_valid_invalid'
    })
    optional_scenarios: Set[str] = field(default_factory=lambda: {
        'timeout_detection', 'channel_reset_recovery',
        'very_large_transfer', 'descriptor_chain_exhaustion'
    })

    # Cross coverage
    legal_cross: Set[str] = field(default_factory=lambda: {
        'INCR_size64_len1', 'INCR_size64_len2',
        'INCR_size64_len4', 'INCR_size64_len8'
    })

    @classmethod
    def load(cls, config_name: str = 'rapids') -> 'LegalCoverageConfig':
        """Load legal coverage config from YAML file.

        Args:
            config_name: Name of the config (e.g., 'rapids')

        Returns:
            LegalCoverageConfig with values from YAML file
        """
        # Try to load YAML file
        config_dir = Path(__file__).parent
        yaml_file = config_dir / f"{config_name}_legal_coverage.yaml"

        if not yaml_file.exists():
            # Return default config
            return cls()

        with open(yaml_file, 'r') as f:
            data = yaml.safe_load(f)

        # Parse YAML into config
        config = cls(
            name=data.get('component', config_name),
            description=data.get('description', ''),
        )

        # AXI burst types
        if 'axi_burst_types' in data:
            config.legal_burst_types = set(data['axi_burst_types'].get('legal', []))
            config.illegal_burst_types = set(data['axi_burst_types'].get('illegal', []))

        # AXI burst sizes
        if 'axi_burst_sizes' in data:
            config.legal_burst_sizes = set(data['axi_burst_sizes'].get('legal', []))
            config.illegal_burst_sizes = set(data['axi_burst_sizes'].get('illegal', []))
            config.optional_burst_sizes = set(data['axi_burst_sizes'].get('optional', []))

        # AXI burst lengths
        if 'axi_burst_lengths' in data:
            config.legal_burst_lengths = set(data['axi_burst_lengths'].get('legal', []))
            config.optional_burst_lengths = set(data['axi_burst_lengths'].get('optional', []))
            config.illegal_burst_lengths = set(data['axi_burst_lengths'].get('illegal', []))

        # AXI responses
        if 'axi_responses' in data:
            config.legal_responses = set(data['axi_responses'].get('legal', []))
            config.optional_responses = set(data['axi_responses'].get('optional', []))
            config.illegal_responses = set(data['axi_responses'].get('illegal', []))

        # APB transactions
        if 'apb_transactions' in data:
            config.legal_apb = set(data['apb_transactions'].get('legal', []))
            config.optional_apb = set(data['apb_transactions'].get('optional', []))
            config.illegal_apb = set(data['apb_transactions'].get('illegal', []))

        # Address alignment
        if 'address_alignment' in data:
            config.legal_alignment = set(data['address_alignment'].get('legal', []))
            config.optional_alignment = set(data['address_alignment'].get('optional', []))
            config.illegal_alignment = set(data['address_alignment'].get('illegal', []))

        # Handshakes
        if 'handshakes' in data:
            all_handshakes = []
            for category, items in data['handshakes'].items():
                if isinstance(items, list):
                    all_handshakes.extend(items)
            config.legal_handshakes = set(all_handshakes)

        # Scheduler states
        if 'scheduler_states' in data:
            config.legal_scheduler_states = set(data['scheduler_states'].get('legal', []))
            config.optional_scheduler_states = set(data['scheduler_states'].get('optional', []))

        # Descriptor engine states
        if 'descriptor_engine_states' in data:
            config.legal_desc_engine_states = set(data['descriptor_engine_states'].get('legal', []))
            config.optional_desc_engine_states = set(data['descriptor_engine_states'].get('optional', []))

        # Scenarios
        if 'scenarios' in data:
            config.critical_scenarios = set(data['scenarios'].get('critical', []))
            config.important_scenarios = set(data['scenarios'].get('important', []))
            config.optional_scenarios = set(data['scenarios'].get('optional', []))

        # Cross coverage
        if 'cross_coverage' in data:
            if 'burst_combinations' in data['cross_coverage']:
                config.legal_cross = set(data['cross_coverage']['burst_combinations'])

        return config

    def get_all_legal_points(self) -> Dict[str, Set[str]]:
        """Get all legal coverage points organized by category."""
        return {
            'axi_burst_type': self.legal_burst_types,
            'axi_burst_size': self.legal_burst_sizes,
            'axi_burst_length': self.legal_burst_lengths,
            'axi_response': self.legal_responses,
            'apb': self.legal_apb,
            'alignment': self.legal_alignment,
            'handshakes': self.legal_handshakes,
            'scheduler_states': self.legal_scheduler_states,
            'desc_engine_states': self.legal_desc_engine_states,
            'critical_scenarios': self.critical_scenarios,
            'important_scenarios': self.important_scenarios,
            'cross': self.legal_cross,
        }

    def get_total_legal_points(self) -> int:
        """Get total count of legal coverage points."""
        return sum(len(s) for s in self.get_all_legal_points().values())
