# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: protocol_coverage
# Purpose: STREAM-specific protocol coverage collection
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream/dv/coverage
#
# Author: sean galloway
# Created: 2025-01-10

"""
Protocol Coverage Collector for STREAM Component

Extends the shared ProtocolCoverageBase to add STREAM-specific:
- Interface names (desc, axi_mem, network)
- Handshake definitions
- Scenario coverage
- Legal coverage calculation

Tracks coverage of:
- AXI4 transaction types (burst type, size, length, response)
- APB transaction types (read/write, response)
- Address patterns (alignment, ranges)
- Cross-coverage (burst type x size, etc.)
"""

import logging
from typing import Dict, Optional, Any

# Import shared base classes from bin/cov_utils
from bin.cov_utils import (
    ProtocolCoverageBase,
    CoveragePoint,
    CoverGroup,
    AxiBurstType,
    AxiResponse,
    ApbResponse,
)

# Re-export for backward compatibility
__all__ = [
    'ProtocolCoverage',
    'CoveragePoint',
    'CoverGroup',
    'AxiBurstType',
    'AxiResponse',
    'ApbResponse',
]


class ProtocolCoverage(ProtocolCoverageBase):
    """
    Protocol coverage collector for STREAM component.

    Extends ProtocolCoverageBase with STREAM-specific:
    - Interfaces: desc, axi_mem, network
    - Handshakes: descriptor, network, memory interfaces
    - Scenarios: DMA-specific functional scenarios

    Supports "legal coverage" mode where coverage is measured against
    only the legal variations that STREAM supports (from YAML config).
    """

    # STREAM-specific interfaces
    INTERFACES = ['desc', 'axi_mem', 'network', 'generic']

    def __init__(self, name: str = "stream_protocol_coverage",
                 log: Optional[logging.Logger] = None,
                 legal_config: Optional['LegalCoverageConfig'] = None):
        """Initialize STREAM protocol coverage collector.

        Args:
            name: Name for this coverage instance
            log: Optional logger
            legal_config: Optional legal coverage config for STREAM-specific coverage
        """
        # Initialize base class (sets up all standard coverage groups)
        super().__init__(name=name, log=log, legal_config=legal_config)

    def _init_handshake_coverage(self):
        """Initialize STREAM-specific valid/ready handshake coverage points."""
        # Common handshake interfaces in STREAM
        handshakes = [
            # Descriptor interfaces
            ("desc_valid_ready", "Descriptor valid/ready handshake"),
            ("desc_done", "Descriptor done signal"),
            # Network interfaces
            ("network_tx_valid_ready", "Network TX valid/ready"),
            ("network_rx_valid_ready", "Network RX valid/ready"),
            # Memory interfaces
            ("mem_cmd_valid_ready", "Memory command valid/ready"),
            ("mem_data_valid_ready", "Memory data valid/ready"),
            # Internal pipelines
            ("scheduler_to_read_engine", "Scheduler to read engine handshake"),
            ("scheduler_to_write_engine", "Scheduler to write engine handshake"),
            ("read_engine_complete", "Read engine completion"),
            ("write_engine_complete", "Write engine completion"),
            # Backpressure scenarios
            ("backpressure_stall", "Backpressure causing stall"),
            ("pipeline_bubble", "Pipeline bubble (valid low)"),
        ]
        for key, desc in handshakes:
            self.handshake_coverage.add_point(key, desc, goal=1)

    def _init_scenario_coverage(self):
        """Initialize STREAM-specific functional scenario coverage."""
        scenarios = [
            ("single_desc", "Single descriptor operation"),
            ("chained_desc", "Chained descriptor operation"),
            ("concurrent_rw", "Concurrent read and write"),
            ("back_to_back", "Back-to-back transactions"),
            ("error_handling", "Error injection and handling"),
            ("timeout_recovery", "Timeout detection and recovery"),
            ("full_pipeline", "Full pipeline active"),
            ("backpressure", "Backpressure handling"),
            ("max_outstanding", "Maximum outstanding transactions"),
            ("empty_desc", "Empty descriptor handling"),
            ("wrap_burst", "WRAP burst boundary handling"),
            ("narrow_transfer", "Narrow transfer (strobe != all 1s)"),
        ]
        for key, desc in scenarios:
            self.scenarios.add_point(key, desc, goal=1)

    def get_legal_coverage_pct(self) -> float:
        """Calculate coverage percentage against legal points only.

        Returns:
            Coverage percentage (0-100) against legal coverage points
        """
        if not self.legal_config:
            # Fall back to base class implementation
            all_groups = self._all_groups + list(self.cross_coverage.values())
            if not all_groups:
                return 0.0

            total_covered = sum(g.covered_count for g in all_groups)
            total_points = sum(g.total_count for g in all_groups)

            if total_points == 0:
                return 0.0

            return (total_covered / total_points) * 100.0

        legal_points = self.legal_config.get_all_legal_points()
        covered = 0
        total = 0

        # Check AXI read burst type
        for point in legal_points.get('axi_burst_type', set()):
            total += 1
            if point in self.axi_read_burst_type.points:
                if self.axi_read_burst_type.points[point].is_covered:
                    covered += 1

        # Check AXI write burst type
        for point in legal_points.get('axi_burst_type', set()):
            total += 1
            if point in self.axi_write_burst_type.points:
                if self.axi_write_burst_type.points[point].is_covered:
                    covered += 1

        # Check AXI read burst size
        for point in legal_points.get('axi_burst_size', set()):
            total += 1
            if point in self.axi_read_burst_size.points:
                if self.axi_read_burst_size.points[point].is_covered:
                    covered += 1

        # Check AXI write burst size
        for point in legal_points.get('axi_burst_size', set()):
            total += 1
            if point in self.axi_write_burst_size.points:
                if self.axi_write_burst_size.points[point].is_covered:
                    covered += 1

        # Check AXI read burst length
        for point in legal_points.get('axi_burst_length', set()):
            total += 1
            if point in self.axi_read_burst_length.points:
                if self.axi_read_burst_length.points[point].is_covered:
                    covered += 1

        # Check AXI write burst length
        for point in legal_points.get('axi_burst_length', set()):
            total += 1
            if point in self.axi_write_burst_length.points:
                if self.axi_write_burst_length.points[point].is_covered:
                    covered += 1

        # Check AXI read response
        for point in legal_points.get('axi_response', set()):
            total += 1
            if point in self.axi_read_response.points:
                if self.axi_read_response.points[point].is_covered:
                    covered += 1

        # Check AXI write response
        for point in legal_points.get('axi_response', set()):
            total += 1
            if point in self.axi_write_response.points:
                if self.axi_write_response.points[point].is_covered:
                    covered += 1

        # Check APB transactions
        for point in legal_points.get('apb', set()):
            total += 1
            if point in self.apb_transactions.points:
                if self.apb_transactions.points[point].is_covered:
                    covered += 1

        # Check address alignment
        for point in legal_points.get('alignment', set()):
            total += 1
            if point in self.address_alignment.points:
                if self.address_alignment.points[point].is_covered:
                    covered += 1

        # Check handshakes
        for point in legal_points.get('handshake', set()):
            total += 1
            if point in self.handshake_coverage.points:
                if self.handshake_coverage.points[point].is_covered:
                    covered += 1

        # Check scenarios
        for point in legal_points.get('scenario', set()):
            total += 1
            if point in self.scenarios.points:
                if self.scenarios.points[point].is_covered:
                    covered += 1

        # Check cross coverage
        for point in legal_points.get('cross', set()):
            total += 1
            if 'burst_type_x_size' in self.cross_coverage:
                if point in self.cross_coverage['burst_type_x_size'].points:
                    if self.cross_coverage['burst_type_x_size'].points[point].is_covered:
                        covered += 1

        if total == 0:
            return 0.0

        return (covered / total) * 100.0

    def get_legal_coverage_summary(self) -> Dict[str, Any]:
        """Get detailed legal coverage summary.

        Returns:
            Dictionary with coverage details per category
        """
        if not self.legal_config:
            return {'error': 'No legal config loaded'}

        legal_points = self.legal_config.get_all_legal_points()
        summary = {
            'legal_points_total': self.legal_config.count_legal_points(),
            'critical_points_total': self.legal_config.count_critical_points(),
            'categories': {}
        }

        # Map groups to legal categories
        category_groups = {
            'axi_burst_type': [
                ('read', self.axi_read_burst_type),
                ('write', self.axi_write_burst_type)
            ],
            'axi_burst_size': [
                ('read', self.axi_read_burst_size),
                ('write', self.axi_write_burst_size)
            ],
            'axi_burst_length': [
                ('read', self.axi_read_burst_length),
                ('write', self.axi_write_burst_length)
            ],
            'axi_response': [
                ('read', self.axi_read_response),
                ('write', self.axi_write_response)
            ],
            'apb': [('', self.apb_transactions)],
            'alignment': [('', self.address_alignment)],
            'handshake': [('', self.handshake_coverage)],
            'scenario': [('', self.scenarios)],
        }

        for cat_name, legal_pts in legal_points.items():
            if cat_name == 'cross':
                continue  # Handle separately

            cat_summary = {
                'legal_points': list(legal_pts),
                'covered': [],
                'missing': [],
                'coverage_pct': 0.0
            }

            groups = category_groups.get(cat_name, [])
            for prefix, group in groups:
                for point in legal_pts:
                    if point in group.points:
                        if group.points[point].is_covered:
                            cat_summary['covered'].append(f"{prefix}_{point}" if prefix else point)
                        else:
                            cat_summary['missing'].append(f"{prefix}_{point}" if prefix else point)

            total = len(cat_summary['covered']) + len(cat_summary['missing'])
            if total > 0:
                cat_summary['coverage_pct'] = (len(cat_summary['covered']) / total) * 100.0

            summary['categories'][cat_name] = cat_summary

        # Handle cross coverage
        if 'cross' in legal_points and 'burst_type_x_size' in self.cross_coverage:
            cross_summary = {
                'legal_points': list(legal_points['cross']),
                'covered': [],
                'missing': [],
                'coverage_pct': 0.0
            }
            for point in legal_points['cross']:
                if point in self.cross_coverage['burst_type_x_size'].points:
                    if self.cross_coverage['burst_type_x_size'].points[point].is_covered:
                        cross_summary['covered'].append(point)
                    else:
                        cross_summary['missing'].append(point)
            total = len(cross_summary['covered']) + len(cross_summary['missing'])
            if total > 0:
                cross_summary['coverage_pct'] = (len(cross_summary['covered']) / total) * 100.0
            summary['categories']['cross'] = cross_summary

        # Calculate overall
        all_covered = sum(len(c['covered']) for c in summary['categories'].values())
        all_total = sum(
            len(c['covered']) + len(c['missing'])
            for c in summary['categories'].values()
        )
        summary['overall_coverage_pct'] = (all_covered / all_total * 100.0) if all_total > 0 else 0.0
        summary['covered_count'] = all_covered
        summary['total_count'] = all_total

        return summary
