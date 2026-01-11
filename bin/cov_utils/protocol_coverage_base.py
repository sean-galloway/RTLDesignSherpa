# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: protocol_coverage_base
# Purpose: Base classes for protocol-level coverage collection
#
# Author: sean galloway
# Created: 2025-01-10

"""
Protocol Coverage Base Classes

Provides AGNOSTIC base classes for AXI/APB/AXIS protocol coverage that can
be extended by project-specific implementations.

This module contains:
- CoveragePoint: Single coverage point with hit tracking
- CoverGroup: Group of related coverage points
- AxiBurstType, AxiResponse, ApbResponse: Protocol enums
- ProtocolCoverageBase: Base class for protocol coverage collection

Projects extend ProtocolCoverageBase to add component-specific:
- Interface names
- Handshake definitions
- Scenario coverage
- Legal coverage configuration
"""

import json
import logging
from collections import defaultdict
from dataclasses import dataclass, field, asdict
from typing import Dict, List, Optional, Set, Any, TYPE_CHECKING
from enum import Enum

if TYPE_CHECKING:
    from .config_base import LegalCoverageConfigBase


class AxiBurstType(Enum):
    """AXI burst types."""
    FIXED = 0
    INCR = 1
    WRAP = 2


class AxiResponse(Enum):
    """AXI response types."""
    OKAY = 0
    EXOKAY = 1
    SLVERR = 2
    DECERR = 3


class ApbResponse(Enum):
    """APB response types."""
    OKAY = 0
    ERROR = 1


@dataclass
class CoveragePoint:
    """A single coverage point with hit count."""
    name: str
    description: str = ""
    hits: int = 0
    goal: int = 1  # Minimum hits required for "covered"

    @property
    def is_covered(self) -> bool:
        return self.hits >= self.goal

    @property
    def coverage_pct(self) -> float:
        if self.goal == 0:
            return 100.0
        return min(100.0, (self.hits / self.goal) * 100.0)

    def hit(self, count: int = 1):
        """Record hits on this coverage point."""
        self.hits += count


@dataclass
class CoverGroup:
    """A group of related coverage points (like a SystemVerilog covergroup)."""
    name: str
    description: str = ""
    points: Dict[str, CoveragePoint] = field(default_factory=dict)

    def add_point(self, key: str, name: str, description: str = "", goal: int = 1):
        """Add a coverage point to the group."""
        self.points[key] = CoveragePoint(name=name, description=description, goal=goal)

    def sample(self, key: str, count: int = 1):
        """Sample (hit) a coverage point."""
        if key in self.points:
            self.points[key].hit(count)
        else:
            # Auto-create point if not exists
            self.points[key] = CoveragePoint(name=key, hits=count)

    @property
    def coverage_pct(self) -> float:
        """Overall coverage percentage for this group."""
        if not self.points:
            return 0.0
        covered = sum(1 for p in self.points.values() if p.is_covered)
        return (covered / len(self.points)) * 100.0

    @property
    def covered_count(self) -> int:
        return sum(1 for p in self.points.values() if p.is_covered)

    @property
    def total_count(self) -> int:
        return len(self.points)

    def to_dict(self) -> Dict:
        """Convert to dictionary for serialization."""
        return {
            'name': self.name,
            'description': self.description,
            'coverage_pct': self.coverage_pct,
            'covered': self.covered_count,
            'total': self.total_count,
            'points': {k: asdict(v) for k, v in self.points.items()}
        }


class ProtocolCoverageBase:
    """
    Base class for protocol coverage collection.

    Provides standard coverage groups for:
    - AXI4 transactions (burst type, size, length, response)
    - APB transactions (read/write, response)
    - Address alignment
    - Valid/Ready handshakes
    - Functional scenarios

    Projects should extend this class to add:
    - Component-specific interfaces (e.g., STREAM's 'desc', 'axi_mem', 'network')
    - Component-specific handshakes
    - Component-specific scenarios
    - Legal coverage configuration

    Usage:
        class StreamProtocolCoverage(ProtocolCoverageBase):
            INTERFACES = ['desc', 'axi_mem', 'network', 'generic']

            def _init_handshake_coverage(self):
                super()._init_handshake_coverage()
                # Add STREAM-specific handshakes
                self.handshake_coverage.add_point("desc_done", "Descriptor done signal")
    """

    # Default interfaces - override in subclass
    INTERFACES = ['generic']

    def __init__(self, name: str = "protocol_coverage",
                 log: Optional[logging.Logger] = None,
                 legal_config: Optional['LegalCoverageConfigBase'] = None):
        """Initialize protocol coverage collector.

        Args:
            name: Name for this coverage instance
            log: Optional logger
            legal_config: Optional legal coverage config for component-specific coverage
        """
        self.name = name
        self.log = log or logging.getLogger(name)
        self.legal_config = legal_config

        # Standard AXI coverage groups
        self.axi_read_burst_type = self._create_axi_burst_type_group("axi_read_burst_type")
        self.axi_write_burst_type = self._create_axi_burst_type_group("axi_write_burst_type")
        self.axi_read_burst_size = self._create_axi_burst_size_group("axi_read_burst_size")
        self.axi_write_burst_size = self._create_axi_burst_size_group("axi_write_burst_size")
        self.axi_read_burst_length = self._create_axi_burst_length_group("axi_read_burst_length")
        self.axi_write_burst_length = self._create_axi_burst_length_group("axi_write_burst_length")
        self.axi_read_response = self._create_axi_response_group("axi_read_response")
        self.axi_write_response = self._create_axi_response_group("axi_write_response")

        # Standard APB coverage
        self.apb_transactions = self._create_apb_group("apb_transactions")

        # Address alignment coverage
        self.address_alignment = self._create_address_alignment_group("address_alignment")

        # Interface-specific coverage
        self.interface_coverage: Dict[str, Dict[str, CoverGroup]] = {}
        self._init_interface_coverage()

        # Valid/Ready handshake coverage
        self.handshake_coverage = CoverGroup(name="handshakes", description="Valid/Ready interface coverage")
        self._init_handshake_coverage()

        # Functional coverage
        self.scenarios = CoverGroup(name="scenarios", description="Functional scenarios")
        self._init_scenario_coverage()

        # Cross-coverage tracking
        self.cross_coverage: Dict[str, CoverGroup] = {}
        self._init_cross_coverage()

        # All groups for iteration
        self._all_groups: List[CoverGroup] = [
            self.axi_read_burst_type,
            self.axi_write_burst_type,
            self.axi_read_burst_size,
            self.axi_write_burst_size,
            self.axi_read_burst_length,
            self.axi_write_burst_length,
            self.axi_read_response,
            self.axi_write_response,
            self.apb_transactions,
            self.address_alignment,
            self.handshake_coverage,
            self.scenarios,
        ]

    def _init_interface_coverage(self):
        """Initialize per-interface coverage groups. Override in subclass."""
        for iface in self.INTERFACES:
            self.interface_coverage[iface] = {
                'read_burst_type': self._create_axi_burst_type_group(f"{iface}_read_burst_type"),
                'read_burst_size': self._create_axi_burst_size_group(f"{iface}_read_burst_size"),
                'read_burst_length': self._create_axi_burst_length_group(f"{iface}_read_burst_length"),
                'read_response': self._create_axi_response_group(f"{iface}_read_response"),
                'write_burst_type': self._create_axi_burst_type_group(f"{iface}_write_burst_type"),
                'write_burst_size': self._create_axi_burst_size_group(f"{iface}_write_burst_size"),
                'write_burst_length': self._create_axi_burst_length_group(f"{iface}_write_burst_length"),
                'write_response': self._create_axi_response_group(f"{iface}_write_response"),
            }

    def _init_handshake_coverage(self):
        """Initialize valid/ready handshake coverage points. Override to extend."""
        # Base handshakes common to most components
        handshakes = [
            ("backpressure_stall", "Backpressure causing stall"),
            ("pipeline_bubble", "Pipeline bubble (valid low)"),
        ]
        for key, desc in handshakes:
            self.handshake_coverage.add_point(key, desc, goal=1)

    def _init_scenario_coverage(self):
        """Initialize functional scenario coverage. Override to extend."""
        # Base scenarios common to most components
        scenarios = [
            ("single_desc", "Single descriptor/transaction operation"),
            ("back_to_back", "Back-to-back transactions"),
            ("error_handling", "Error injection and handling"),
            ("backpressure", "Backpressure handling"),
        ]
        for key, desc in scenarios:
            self.scenarios.add_point(key, desc, goal=1)

    def _create_axi_burst_type_group(self, name: str) -> CoverGroup:
        """Create coverage group for AXI burst types."""
        group = CoverGroup(name=name, description="AXI burst type coverage")
        for bt in AxiBurstType:
            group.add_point(bt.name, f"Burst type {bt.name}", goal=1)
        return group

    def _create_axi_burst_size_group(self, name: str) -> CoverGroup:
        """Create coverage group for AXI burst sizes."""
        group = CoverGroup(name=name, description="AXI burst size coverage")
        for size_exp in range(8):  # 2^0 to 2^7 = 1 to 128 bytes
            size = 1 << size_exp
            group.add_point(f"size_{size}", f"{size}-byte transfers", goal=1)
        return group

    def _create_axi_burst_length_group(self, name: str) -> CoverGroup:
        """Create coverage group for AXI burst lengths."""
        group = CoverGroup(name=name, description="AXI burst length coverage")
        # Bin burst lengths
        group.add_point("len_1", "Single beat (len=0)", goal=1)
        group.add_point("len_2_4", "Short burst (len=1-3)", goal=1)
        group.add_point("len_5_8", "Medium burst (len=4-7)", goal=1)
        group.add_point("len_9_16", "Long burst (len=8-15)", goal=1)
        group.add_point("len_17_256", "Very long burst (len=16-255)", goal=1)
        return group

    def _create_axi_response_group(self, name: str) -> CoverGroup:
        """Create coverage group for AXI responses."""
        group = CoverGroup(name=name, description="AXI response type coverage")
        for resp in AxiResponse:
            group.add_point(resp.name, f"Response {resp.name}", goal=1)
        return group

    def _create_apb_group(self, name: str) -> CoverGroup:
        """Create coverage group for APB transactions."""
        group = CoverGroup(name=name, description="APB transaction coverage")
        group.add_point("read_okay", "APB read with OKAY response", goal=1)
        group.add_point("read_error", "APB read with ERROR response", goal=1)
        group.add_point("write_okay", "APB write with OKAY response", goal=1)
        group.add_point("write_error", "APB write with ERROR response", goal=1)
        return group

    def _create_address_alignment_group(self, name: str) -> CoverGroup:
        """Create coverage group for address alignment."""
        group = CoverGroup(name=name, description="Address alignment coverage")
        group.add_point("unaligned", "Unaligned address", goal=1)
        group.add_point("halfword", "Halfword aligned (2-byte)", goal=1)
        group.add_point("word", "Word aligned (4-byte)", goal=1)
        group.add_point("dword", "Doubleword aligned (8-byte)", goal=1)
        group.add_point("qword", "Quadword aligned (16-byte)", goal=1)
        group.add_point("cache_line", "Cache line aligned (64-byte)", goal=1)
        return group

    def _init_cross_coverage(self):
        """Initialize cross-coverage groups."""
        # Burst type x burst size cross coverage
        self.cross_coverage['burst_type_x_size'] = CoverGroup(
            name="burst_type_x_size",
            description="Cross: burst type x burst size"
        )
        for bt in AxiBurstType:
            for size_exp in range(4):  # Common sizes: 1, 2, 4, 8 bytes
                size = 1 << size_exp
                key = f"{bt.name}_size{size}"
                self.cross_coverage['burst_type_x_size'].add_point(
                    key, f"{bt.name} burst with {size}-byte size", goal=1
                )

    # =========================================================================
    # Sampling methods - call these from testbench
    # =========================================================================

    def sample_axi_read(self, burst_type: int, burst_size: int, burst_len: int,
                        address: int = 0, response: int = 0, interface: str = None):
        """Sample an AXI read transaction.

        Args:
            burst_type: AXI burst type (0=FIXED, 1=INCR, 2=WRAP)
            burst_size: AXI burst size (2^size bytes per beat)
            burst_len: AXI burst length (0=1 beat, 255=256 beats)
            address: Transaction address (for alignment coverage)
            response: AXI response (0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)
            interface: Optional interface name
        """
        # Sample to legacy groups
        try:
            bt = AxiBurstType(burst_type)
            self.axi_read_burst_type.sample(bt.name)
        except ValueError:
            self.log.warning(f"Unknown burst type: {burst_type}")

        size_bytes = 1 << burst_size
        self.axi_read_burst_size.sample(f"size_{size_bytes}")
        self._sample_burst_length(self.axi_read_burst_length, burst_len)

        try:
            resp = AxiResponse(response)
            self.axi_read_response.sample(resp.name)
        except ValueError:
            pass

        self._sample_address_alignment(address)

        # Cross coverage
        if burst_type < 3 and burst_size < 4:
            bt_name = AxiBurstType(burst_type).name
            self.cross_coverage['burst_type_x_size'].sample(f"{bt_name}_size{size_bytes}")

        # Sample to interface-specific groups if interface specified
        if interface and interface in self.interface_coverage:
            iface_groups = self.interface_coverage[interface]
            try:
                bt = AxiBurstType(burst_type)
                iface_groups['read_burst_type'].sample(bt.name)
            except ValueError:
                pass
            iface_groups['read_burst_size'].sample(f"size_{size_bytes}")
            self._sample_burst_length(iface_groups['read_burst_length'], burst_len)
            try:
                resp = AxiResponse(response)
                iface_groups['read_response'].sample(resp.name)
            except ValueError:
                pass

    def sample_axi_write(self, burst_type: int, burst_size: int, burst_len: int,
                         address: int = 0, response: int = 0, interface: str = None):
        """Sample an AXI write transaction.

        Args:
            burst_type: AXI burst type (0=FIXED, 1=INCR, 2=WRAP)
            burst_size: AXI burst size (2^size bytes per beat)
            burst_len: AXI burst length (0=1 beat, 255=256 beats)
            address: Transaction address (for alignment coverage)
            response: AXI response (0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)
            interface: Optional interface name
        """
        # Sample to legacy groups
        try:
            bt = AxiBurstType(burst_type)
            self.axi_write_burst_type.sample(bt.name)
        except ValueError:
            self.log.warning(f"Unknown burst type: {burst_type}")

        size_bytes = 1 << burst_size
        self.axi_write_burst_size.sample(f"size_{size_bytes}")
        self._sample_burst_length(self.axi_write_burst_length, burst_len)

        try:
            resp = AxiResponse(response)
            self.axi_write_response.sample(resp.name)
        except ValueError:
            pass

        self._sample_address_alignment(address)

        # Cross coverage
        if burst_type < 3 and burst_size < 4:
            bt_name = AxiBurstType(burst_type).name
            self.cross_coverage['burst_type_x_size'].sample(f"{bt_name}_size{size_bytes}")

        # Sample to interface-specific groups if interface specified
        if interface and interface in self.interface_coverage:
            iface_groups = self.interface_coverage[interface]
            try:
                bt = AxiBurstType(burst_type)
                iface_groups['write_burst_type'].sample(bt.name)
            except ValueError:
                pass
            iface_groups['write_burst_size'].sample(f"size_{size_bytes}")
            self._sample_burst_length(iface_groups['write_burst_length'], burst_len)
            try:
                resp = AxiResponse(response)
                iface_groups['write_response'].sample(resp.name)
            except ValueError:
                pass

    def sample_handshake(self, handshake_name: str):
        """Sample a valid/ready handshake event."""
        self.handshake_coverage.sample(handshake_name)

    def sample_apb(self, is_write: bool, is_error: bool = False):
        """Sample an APB transaction."""
        if is_write:
            if is_error:
                self.apb_transactions.sample("write_error")
            else:
                self.apb_transactions.sample("write_okay")
        else:
            if is_error:
                self.apb_transactions.sample("read_error")
            else:
                self.apb_transactions.sample("read_okay")

    def sample_scenario(self, scenario_name: str):
        """Sample a functional scenario."""
        self.scenarios.sample(scenario_name)

    def _sample_burst_length(self, group: CoverGroup, burst_len: int):
        """Bin burst length and sample."""
        if burst_len == 0:
            group.sample("len_1")
        elif burst_len <= 3:
            group.sample("len_2_4")
        elif burst_len <= 7:
            group.sample("len_5_8")
        elif burst_len <= 15:
            group.sample("len_9_16")
        else:
            group.sample("len_17_256")

    def _sample_address_alignment(self, address: int):
        """Sample address alignment coverage."""
        if address % 64 == 0:
            self.address_alignment.sample("cache_line")
        elif address % 16 == 0:
            self.address_alignment.sample("qword")
        elif address % 8 == 0:
            self.address_alignment.sample("dword")
        elif address % 4 == 0:
            self.address_alignment.sample("word")
        elif address % 2 == 0:
            self.address_alignment.sample("halfword")
        else:
            self.address_alignment.sample("unaligned")

    # =========================================================================
    # Reporting methods
    # =========================================================================

    def get_coverage_summary(self) -> Dict[str, Any]:
        """Get coverage summary as dictionary."""
        summary = {
            'name': self.name,
            'overall_coverage_pct': self.overall_coverage_pct,
            'groups': {},
            'interfaces': {}
        }

        for group in self._all_groups:
            summary['groups'][group.name] = group.to_dict()

        for name, group in self.cross_coverage.items():
            summary['groups'][name] = group.to_dict()

        # Add interface-specific coverage
        for iface_name, iface_groups in self.interface_coverage.items():
            summary['interfaces'][iface_name] = {}
            for group_key, group in iface_groups.items():
                summary['interfaces'][iface_name][group_key] = group.to_dict()

        return summary

    def get_interface_summary(self) -> Dict[str, Dict[str, float]]:
        """Get per-interface coverage summary."""
        summary = {}
        for iface_name, iface_groups in self.interface_coverage.items():
            read_groups = [g for k, g in iface_groups.items() if 'read' in k]
            write_groups = [g for k, g in iface_groups.items() if 'write' in k]

            read_covered = sum(g.covered_count for g in read_groups)
            read_total = sum(g.total_count for g in read_groups)
            write_covered = sum(g.covered_count for g in write_groups)
            write_total = sum(g.total_count for g in write_groups)

            read_pct = (read_covered / read_total * 100) if read_total > 0 else 0.0
            write_pct = (write_covered / write_total * 100) if write_total > 0 else 0.0
            total_covered = read_covered + write_covered
            total_points = read_total + write_total
            overall_pct = (total_covered / total_points * 100) if total_points > 0 else 0.0

            summary[iface_name] = {
                'read': read_pct,
                'write': write_pct,
                'overall': overall_pct
            }

        return summary

    @property
    def overall_coverage_pct(self) -> float:
        """Calculate overall coverage percentage."""
        if self.legal_config:
            return self.get_legal_coverage_pct()

        all_groups = self._all_groups + list(self.cross_coverage.values())
        if not all_groups:
            return 0.0

        total_covered = sum(g.covered_count for g in all_groups)
        total_points = sum(g.total_count for g in all_groups)

        if total_points == 0:
            return 0.0

        return (total_covered / total_points) * 100.0

    def get_legal_coverage_pct(self) -> float:
        """Calculate coverage percentage against legal points only.

        Override in subclass to implement component-specific legal coverage.
        """
        if not self.legal_config:
            return self.overall_coverage_pct
        # Default implementation - subclass should override
        return self.overall_coverage_pct

    def report(self, detailed: bool = False) -> str:
        """Generate human-readable coverage report."""
        lines = []
        lines.append("=" * 80)
        lines.append(f"PROTOCOL COVERAGE REPORT: {self.name}")
        lines.append("=" * 80)
        lines.append(f"Overall Coverage: {self.overall_coverage_pct:.1f}%")
        lines.append("")

        # Global coverage groups
        lines.append("GLOBAL COVERAGE:")
        for group in self._all_groups:
            lines.append(f"  {group.name}: {group.coverage_pct:.1f}% ({group.covered_count}/{group.total_count})")
            if detailed:
                for key, point in group.points.items():
                    status = "COVERED" if point.is_covered else "MISSING"
                    lines.append(f"    [{status}] {key}: {point.hits} hits")

        lines.append("")
        lines.append("CROSS COVERAGE:")
        for name, group in self.cross_coverage.items():
            lines.append(f"  {name}: {group.coverage_pct:.1f}% ({group.covered_count}/{group.total_count})")

        # Interface-specific coverage
        lines.append("")
        lines.append("INTERFACE COVERAGE:")
        iface_summary = self.get_interface_summary()
        for iface_name, metrics in iface_summary.items():
            lines.append(f"  {iface_name}:")
            lines.append(f"    Read:  {metrics['read']:.1f}%")
            lines.append(f"    Write: {metrics['write']:.1f}%")
            lines.append(f"    Total: {metrics['overall']:.1f}%")

        lines.append("=" * 80)
        return "\n".join(lines)

    def save_to_file(self, filepath: str):
        """Save coverage data to JSON file."""
        import os
        os.makedirs(os.path.dirname(filepath), exist_ok=True)

        with open(filepath, 'w') as f:
            json.dump(self.get_coverage_summary(), f, indent=2)

        self.log.info(f"Coverage data saved to: {filepath}")

    @classmethod
    def load_from_file(cls, filepath: str) -> 'ProtocolCoverageBase':
        """Load coverage data from JSON file."""
        with open(filepath, 'r') as f:
            data = json.load(f)

        cov = cls(name=data.get('name', 'loaded_coverage'))

        # Restore coverage points from loaded data
        for group_name, group_data in data.get('groups', {}).items():
            target_group = None
            for g in cov._all_groups:
                if g.name == group_name:
                    target_group = g
                    break
            if target_group is None and group_name in cov.cross_coverage:
                target_group = cov.cross_coverage[group_name]

            if target_group and 'points' in group_data:
                for key, point_data in group_data['points'].items():
                    if key in target_group.points:
                        target_group.points[key].hits = point_data.get('hits', 0)
                    else:
                        target_group.add_point(
                            key,
                            point_data.get('name', key),
                            point_data.get('description', ''),
                            point_data.get('goal', 1)
                        )
                        target_group.points[key].hits = point_data.get('hits', 0)

        return cov

    def merge_from(self, other: 'ProtocolCoverageBase'):
        """Merge coverage data from another collector."""
        for i, group in enumerate(self._all_groups):
            if i < len(other._all_groups):
                other_group = other._all_groups[i]
                for key, point in other_group.points.items():
                    if key in group.points:
                        group.points[key].hits += point.hits
                    else:
                        group.points[key] = CoveragePoint(
                            name=point.name,
                            description=point.description,
                            hits=point.hits,
                            goal=point.goal
                        )

        for name, other_group in other.cross_coverage.items():
            if name in self.cross_coverage:
                for key, point in other_group.points.items():
                    if key in self.cross_coverage[name].points:
                        self.cross_coverage[name].points[key].hits += point.hits
