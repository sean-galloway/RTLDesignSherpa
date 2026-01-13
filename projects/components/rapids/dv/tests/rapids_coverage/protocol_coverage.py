# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: protocol_coverage
# Purpose: RAPIDS-specific protocol coverage collection
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids/dv/tests/rapids_coverage
#
# Author: sean galloway
# Created: 2025-01-11

"""
Protocol Coverage Collector for RAPIDS Beats Component

Tracks coverage of:
- AXI4 transaction types (burst type, size, length, response)
- APB transaction types (descriptor kick-off)
- Scheduler FSM states
- Descriptor engine FSM states
- Handshake coverage
- Scenario coverage
- Cross-coverage (burst type x size x length)

Supports "legal coverage" mode where coverage is measured against
only the legal variations that RAPIDS actually supports.
"""

import logging
import json
from dataclasses import dataclass, field
from typing import Dict, Optional, Set, List, Any
from pathlib import Path


@dataclass
class CoveragePoint:
    """A single coverage point."""
    name: str
    description: str
    goal: int = 1  # Number of hits required to cover
    hits: int = 0  # Current hit count

    @property
    def is_covered(self) -> bool:
        return self.hits >= self.goal

    def sample(self, count: int = 1):
        """Record hit(s) on this coverage point."""
        self.hits += count

    def to_dict(self) -> Dict:
        return {
            'name': self.name,
            'description': self.description,
            'goal': self.goal,
            'hits': self.hits,
            'covered': self.is_covered,
        }


@dataclass
class CoverGroup:
    """A group of related coverage points."""
    name: str
    description: str
    points: Dict[str, CoveragePoint] = field(default_factory=dict)

    def add_point(self, name: str, description: str, goal: int = 1):
        """Add a coverage point to this group."""
        self.points[name] = CoveragePoint(name, description, goal)

    def sample(self, point_name: str, count: int = 1):
        """Sample a specific coverage point."""
        if point_name in self.points:
            self.points[point_name].sample(count)

    @property
    def covered_count(self) -> int:
        return sum(1 for p in self.points.values() if p.is_covered)

    @property
    def total_count(self) -> int:
        return len(self.points)

    @property
    def coverage_pct(self) -> float:
        if self.total_count == 0:
            return 0.0
        return (self.covered_count / self.total_count) * 100

    def to_dict(self) -> Dict:
        return {
            'name': self.name,
            'description': self.description,
            'covered': self.covered_count,
            'total': self.total_count,
            'coverage_pct': self.coverage_pct,
            'points': {k: v.to_dict() for k, v in self.points.items()},
        }


class ProtocolCoverage:
    """
    Protocol coverage collector for RAPIDS beats component.

    Provides coverage groups for:
    - AXI read transactions (burst type, size, length, response)
    - AXI write transactions (burst type, size, length, response)
    - APB transactions (descriptor kick-off)
    - Scheduler FSM states
    - Descriptor engine FSM states
    - Handshakes
    - Scenarios

    Supports "legal coverage" mode where coverage is measured against
    only the legal variations that RAPIDS supports (from YAML config).
    """

    def __init__(self, name: str = "rapids_protocol_coverage",
                 log: Optional[logging.Logger] = None,
                 legal_config: Optional['LegalCoverageConfig'] = None):
        """Initialize RAPIDS protocol coverage collector.

        Args:
            name: Name for this coverage instance
            log: Optional logger
            legal_config: Optional legal coverage config
        """
        self.name = name
        self.log = log or logging.getLogger(name)
        self.legal_config = legal_config

        # Initialize coverage groups
        self._init_axi_burst_type_coverage()
        self._init_axi_burst_size_coverage()
        self._init_axi_burst_length_coverage()
        self._init_axi_response_coverage()
        self._init_apb_coverage()
        self._init_scheduler_state_coverage()
        self._init_desc_engine_state_coverage()
        self._init_handshake_coverage()
        self._init_scenario_coverage()
        self._init_cross_coverage()

    def _init_axi_burst_type_coverage(self):
        """Initialize AXI burst type coverage."""
        self.axi_read_burst_type = CoverGroup("axi_read_burst_type", "AXI read burst types")
        self.axi_write_burst_type = CoverGroup("axi_write_burst_type", "AXI write burst types")

        for burst_type in ['FIXED', 'INCR', 'WRAP']:
            self.axi_read_burst_type.add_point(burst_type, f"AXI read {burst_type} burst")
            self.axi_write_burst_type.add_point(burst_type, f"AXI write {burst_type} burst")

    def _init_axi_burst_size_coverage(self):
        """Initialize AXI burst size coverage."""
        self.axi_read_burst_size = CoverGroup("axi_read_burst_size", "AXI read burst sizes")
        self.axi_write_burst_size = CoverGroup("axi_write_burst_size", "AXI write burst sizes")

        for size in ['size_1', 'size_2', 'size_4', 'size_8', 'size_16', 'size_32', 'size_64', 'size_128']:
            self.axi_read_burst_size.add_point(size, f"AXI read {size} bytes/beat")
            self.axi_write_burst_size.add_point(size, f"AXI write {size} bytes/beat")

    def _init_axi_burst_length_coverage(self):
        """Initialize AXI burst length coverage."""
        self.axi_read_burst_length = CoverGroup("axi_read_burst_length", "AXI read burst lengths")
        self.axi_write_burst_length = CoverGroup("axi_write_burst_length", "AXI write burst lengths")

        lengths = [
            ('len_1', '1 beat'),
            ('len_2', '2 beats'),
            ('len_4', '4 beats'),
            ('len_8', '8 beats'),
            ('len_16', '16 beats'),
            ('len_32', '32 beats'),
            ('len_256', '256 beats'),
        ]
        for name, desc in lengths:
            self.axi_read_burst_length.add_point(name, f"AXI read {desc}")
            self.axi_write_burst_length.add_point(name, f"AXI write {desc}")

    def _init_axi_response_coverage(self):
        """Initialize AXI response coverage."""
        self.axi_read_response = CoverGroup("axi_read_response", "AXI read responses")
        self.axi_write_response = CoverGroup("axi_write_response", "AXI write responses")

        for resp in ['OKAY', 'EXOKAY', 'SLVERR', 'DECERR']:
            self.axi_read_response.add_point(resp, f"AXI read {resp} response")
            self.axi_write_response.add_point(resp, f"AXI write {resp} response")

    def _init_apb_coverage(self):
        """Initialize APB transaction coverage."""
        self.apb_transactions = CoverGroup("apb_transactions", "APB transactions")
        transactions = [
            ('write_kick_off', 'APB write to kick off descriptor'),
            ('write_okay', 'APB write with OKAY response'),
            ('write_rejected', 'APB write rejected (busy/reset)'),
            ('read', 'APB read transaction'),
        ]
        for name, desc in transactions:
            self.apb_transactions.add_point(name, desc)

    def _init_scheduler_state_coverage(self):
        """Initialize scheduler FSM state coverage."""
        self.scheduler_states = CoverGroup("scheduler_states", "Scheduler FSM states")
        states = [
            ('CH_IDLE', 'Idle, waiting for descriptor'),
            ('CH_FETCH_DESC', 'Fetching descriptor'),
            ('CH_XFER_DATA', 'Transferring data (concurrent R/W)'),
            ('CH_COMPLETE', 'Transfer complete'),
            ('CH_NEXT_DESC', 'Chaining to next descriptor'),
            ('CH_ERROR', 'Error state'),
        ]
        for name, desc in states:
            self.scheduler_states.add_point(name, desc)

    def _init_desc_engine_state_coverage(self):
        """Initialize descriptor engine FSM state coverage."""
        self.desc_engine_states = CoverGroup("desc_engine_states", "Descriptor engine FSM states")
        states = [
            ('RD_IDLE', 'Idle, waiting for fetch request'),
            ('RD_ISSUE_ADDR', 'Issuing AXI AR'),
            ('RD_WAIT_DATA', 'Waiting for AXI R'),
            ('RD_COMPLETE', 'Fetch complete'),
            ('RD_ERROR', 'Fetch error'),
        ]
        for name, desc in states:
            self.desc_engine_states.add_point(name, desc)

    def _init_handshake_coverage(self):
        """Initialize valid/ready handshake coverage."""
        self.handshake_coverage = CoverGroup("handshakes", "Valid/ready handshakes")
        handshakes = [
            # Descriptor interfaces
            ('desc_valid_ready', 'Descriptor valid/ready handshake'),
            ('apb_valid_ready', 'APB valid/ready for kick-off'),
            ('ar_valid_ready', 'AXI AR valid/ready (descriptor)'),
            ('r_valid_ready', 'AXI R valid/ready (descriptor)'),
            # Scheduler to engine interfaces
            ('sched_rd_valid_start', 'Scheduler read valid start'),
            ('sched_wr_valid_start', 'Scheduler write valid start'),
            ('rd_done_strobe', 'Read engine done strobe'),
            ('wr_done_strobe', 'Write engine done strobe'),
            # AXI data engine interfaces
            ('ar_handshake', 'AXI AR handshake (data)'),
            ('r_handshake', 'AXI R handshake (data)'),
            ('aw_handshake', 'AXI AW handshake'),
            ('w_handshake', 'AXI W handshake'),
            ('b_handshake', 'AXI B handshake'),
            # SRAM interfaces
            ('alloc_req', 'SRAM allocation request'),
            ('drain_req', 'SRAM drain request'),
            ('sram_wr_valid_ready', 'SRAM write handshake'),
            ('sram_rd_valid_ready', 'SRAM read handshake'),
            # Backpressure
            ('ar_wait', 'AR channel backpressure'),
            ('r_wait', 'R channel backpressure'),
            ('aw_wait', 'AW channel backpressure'),
            ('w_wait', 'W channel backpressure'),
            ('sram_full', 'SRAM buffer full'),
            ('sram_empty', 'SRAM buffer empty'),
        ]
        for name, desc in handshakes:
            self.handshake_coverage.add_point(name, desc)

    def _init_scenario_coverage(self):
        """Initialize functional scenario coverage."""
        self.scenarios = CoverGroup("scenarios", "Functional scenarios")
        scenarios = [
            # Critical
            ('single_descriptor_complete', 'Single descriptor flow'),
            ('chained_descriptor_complete', 'Chained descriptor flow'),
            ('concurrent_read_write', 'Concurrent R/W in XFER_DATA'),
            ('backpressure_handling', 'SRAM backpressure recovery'),
            # Important
            ('multi_channel_arbitration', 'Multi-channel round-robin'),
            ('burst_size_variations', 'Different cfg_axi_xfer_beats'),
            ('error_flag_propagation', 'Error from AXI response'),
            ('descriptor_valid_invalid', 'Valid bit checking'),
            # Optional
            ('timeout_detection', 'Watchdog timeout'),
            ('channel_reset_recovery', 'Reset mid-operation'),
            ('very_large_transfer', 'Transfer > SRAM size'),
            ('descriptor_chain_exhaustion', 'Long chain completion'),
        ]
        for name, desc in scenarios:
            self.scenarios.add_point(name, desc)

    def _init_cross_coverage(self):
        """Initialize cross coverage groups."""
        self.cross_coverage = CoverGroup("cross_coverage", "Burst combinations")
        crosses = [
            ('INCR_size64_len1', 'INCR burst, 64 bytes, 1 beat'),
            ('INCR_size64_len2', 'INCR burst, 64 bytes, 2 beats'),
            ('INCR_size64_len4', 'INCR burst, 64 bytes, 4 beats'),
            ('INCR_size64_len8', 'INCR burst, 64 bytes, 8 beats'),
        ]
        for name, desc in crosses:
            self.cross_coverage.add_point(name, desc)

    # =========================================================================
    # Sampling Methods
    # =========================================================================

    def sample_axi_read(self, burst_type: int, burst_size: int, burst_len: int):
        """Sample an AXI read transaction.

        Args:
            burst_type: AXI burst type (0=FIXED, 1=INCR, 2=WRAP)
            burst_size: AXI burst size (log2 of bytes per beat)
            burst_len: AXI burst length (0-255, actual length = len+1)
        """
        # Map burst type
        type_names = {0: 'FIXED', 1: 'INCR', 2: 'WRAP'}
        type_name = type_names.get(burst_type, 'UNKNOWN')
        self.axi_read_burst_type.sample(type_name)

        # Map burst size
        size_bytes = 1 << burst_size
        size_name = f'size_{size_bytes}'
        self.axi_read_burst_size.sample(size_name)

        # Map burst length
        actual_len = burst_len + 1
        if actual_len == 1:
            len_name = 'len_1'
        elif actual_len <= 2:
            len_name = 'len_2'
        elif actual_len <= 4:
            len_name = 'len_4'
        elif actual_len <= 8:
            len_name = 'len_8'
        elif actual_len <= 16:
            len_name = 'len_16'
        elif actual_len <= 32:
            len_name = 'len_32'
        else:
            len_name = 'len_256'
        self.axi_read_burst_length.sample(len_name)

        # Cross coverage
        if type_name == 'INCR' and size_bytes == 64:
            cross_name = f'INCR_size64_{len_name}'
            self.cross_coverage.sample(cross_name)

    def sample_axi_write(self, burst_type: int, burst_size: int, burst_len: int):
        """Sample an AXI write transaction.

        Args:
            burst_type: AXI burst type (0=FIXED, 1=INCR, 2=WRAP)
            burst_size: AXI burst size (log2 of bytes per beat)
            burst_len: AXI burst length (0-255, actual length = len+1)
        """
        # Map burst type
        type_names = {0: 'FIXED', 1: 'INCR', 2: 'WRAP'}
        type_name = type_names.get(burst_type, 'UNKNOWN')
        self.axi_write_burst_type.sample(type_name)

        # Map burst size
        size_bytes = 1 << burst_size
        size_name = f'size_{size_bytes}'
        self.axi_write_burst_size.sample(size_name)

        # Map burst length
        actual_len = burst_len + 1
        if actual_len == 1:
            len_name = 'len_1'
        elif actual_len <= 2:
            len_name = 'len_2'
        elif actual_len <= 4:
            len_name = 'len_4'
        elif actual_len <= 8:
            len_name = 'len_8'
        elif actual_len <= 16:
            len_name = 'len_16'
        elif actual_len <= 32:
            len_name = 'len_32'
        else:
            len_name = 'len_256'
        self.axi_write_burst_length.sample(len_name)

    def sample_axi_read_response(self, response: int):
        """Sample AXI read response."""
        resp_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
        self.axi_read_response.sample(resp_names.get(response, 'UNKNOWN'))

    def sample_axi_write_response(self, response: int):
        """Sample AXI write response."""
        resp_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
        self.axi_write_response.sample(resp_names.get(response, 'UNKNOWN'))

    def sample_apb(self, transaction_type: str):
        """Sample APB transaction."""
        self.apb_transactions.sample(transaction_type)

    def sample_scheduler_state(self, state: str):
        """Sample scheduler FSM state."""
        self.scheduler_states.sample(state)

    def sample_desc_engine_state(self, state: str):
        """Sample descriptor engine FSM state."""
        self.desc_engine_states.sample(state)

    def sample_handshake(self, handshake_name: str):
        """Sample a handshake event."""
        self.handshake_coverage.sample(handshake_name)

    def sample_scenario(self, scenario_name: str):
        """Sample a functional scenario."""
        self.scenarios.sample(scenario_name)

    # =========================================================================
    # Reporting Methods
    # =========================================================================

    @property
    def _all_groups(self) -> List[CoverGroup]:
        """Get all coverage groups."""
        return [
            self.axi_read_burst_type,
            self.axi_write_burst_type,
            self.axi_read_burst_size,
            self.axi_write_burst_size,
            self.axi_read_burst_length,
            self.axi_write_burst_length,
            self.axi_read_response,
            self.axi_write_response,
            self.apb_transactions,
            self.scheduler_states,
            self.desc_engine_states,
            self.handshake_coverage,
            self.scenarios,
            self.cross_coverage,
        ]

    def get_coverage_pct(self) -> float:
        """Get overall coverage percentage."""
        total_covered = sum(g.covered_count for g in self._all_groups)
        total_points = sum(g.total_count for g in self._all_groups)
        if total_points == 0:
            return 0.0
        return (total_covered / total_points) * 100

    def get_legal_coverage_pct(self) -> float:
        """Calculate coverage percentage against legal points only."""
        if not self.legal_config:
            return self.get_coverage_pct()

        legal_points = self.legal_config.get_all_legal_points()
        covered = 0
        total = 0

        # Check each category
        for point in legal_points.get('axi_burst_type', set()):
            total += 2  # Read and write
            if point in self.axi_read_burst_type.points:
                if self.axi_read_burst_type.points[point].is_covered:
                    covered += 1
            if point in self.axi_write_burst_type.points:
                if self.axi_write_burst_type.points[point].is_covered:
                    covered += 1

        for point in legal_points.get('axi_burst_size', set()):
            total += 2
            if point in self.axi_read_burst_size.points:
                if self.axi_read_burst_size.points[point].is_covered:
                    covered += 1
            if point in self.axi_write_burst_size.points:
                if self.axi_write_burst_size.points[point].is_covered:
                    covered += 1

        for point in legal_points.get('axi_burst_length', set()):
            total += 2
            if point in self.axi_read_burst_length.points:
                if self.axi_read_burst_length.points[point].is_covered:
                    covered += 1
            if point in self.axi_write_burst_length.points:
                if self.axi_write_burst_length.points[point].is_covered:
                    covered += 1

        for point in legal_points.get('axi_response', set()):
            total += 2
            if point in self.axi_read_response.points:
                if self.axi_read_response.points[point].is_covered:
                    covered += 1
            if point in self.axi_write_response.points:
                if self.axi_write_response.points[point].is_covered:
                    covered += 1

        for point in legal_points.get('apb', set()):
            total += 1
            if point in self.apb_transactions.points:
                if self.apb_transactions.points[point].is_covered:
                    covered += 1

        for point in legal_points.get('scheduler_states', set()):
            total += 1
            if point in self.scheduler_states.points:
                if self.scheduler_states.points[point].is_covered:
                    covered += 1

        for point in legal_points.get('desc_engine_states', set()):
            total += 1
            if point in self.desc_engine_states.points:
                if self.desc_engine_states.points[point].is_covered:
                    covered += 1

        for point in legal_points.get('handshakes', set()):
            total += 1
            if point in self.handshake_coverage.points:
                if self.handshake_coverage.points[point].is_covered:
                    covered += 1

        for scenario_set in ['critical_scenarios', 'important_scenarios']:
            for point in legal_points.get(scenario_set, set()):
                total += 1
                if point in self.scenarios.points:
                    if self.scenarios.points[point].is_covered:
                        covered += 1

        for point in legal_points.get('cross', set()):
            total += 1
            if point in self.cross_coverage.points:
                if self.cross_coverage.points[point].is_covered:
                    covered += 1

        if total == 0:
            return 0.0

        return (covered / total) * 100

    def to_dict(self) -> Dict:
        """Convert coverage data to dictionary."""
        return {
            'name': self.name,
            'overall_pct': self.get_coverage_pct(),
            'legal_pct': self.get_legal_coverage_pct() if self.legal_config else None,
            'groups': {g.name: g.to_dict() for g in self._all_groups},
        }

    def save(self, filepath: str):
        """Save coverage data to JSON file."""
        with open(filepath, 'w') as f:
            json.dump(self.to_dict(), f, indent=2)
        self.log.info(f"Saved protocol coverage to {filepath}")

    def report(self) -> str:
        """Generate coverage report string."""
        lines = [
            f"=== RAPIDS Protocol Coverage: {self.name} ===",
            f"Overall Coverage: {self.get_coverage_pct():.1f}%",
        ]
        if self.legal_config:
            lines.append(f"Legal Coverage: {self.get_legal_coverage_pct():.1f}%")

        lines.append("")
        for group in self._all_groups:
            lines.append(f"{group.name}: {group.covered_count}/{group.total_count} ({group.coverage_pct:.1f}%)")

        return "\n".join(lines)
