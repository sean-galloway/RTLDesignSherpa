# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: config_base
# Purpose: Base configuration classes for coverage collection
#
# Author: sean galloway
# Created: 2025-01-10

"""
Coverage Configuration Base Classes

Provides AGNOSTIC base classes for coverage configuration that can be
extended by project-specific implementations.

This module contains:
- CoverageConfigBase: Base configuration for coverage collection
- LegalCoverageConfigBase: Base for "legal coverage" specifications

Projects extend these classes to add component-specific:
- Module lists to include/exclude
- Legal coverage point definitions
- Coverage goals
"""

import os
from dataclasses import dataclass, field
from typing import List, Dict, Set, Optional, Any
from pathlib import Path
from enum import Enum, auto


class CoverageType(Enum):
    """Types of coverage collected."""
    LINE = auto()      # Line coverage from Verilator
    TOGGLE = auto()    # Toggle coverage from Verilator
    BRANCH = auto()    # Branch coverage from Verilator
    PROTOCOL = auto()  # Protocol coverage (AXI/APB transactions)
    FUNCTIONAL = auto()  # Functional coverage (FSM states, scenarios)


@dataclass
class CoverageGoals:
    """Coverage goals - can be customized per project."""
    line_coverage_target: float = 80.0
    toggle_coverage_target: float = 70.0
    branch_coverage_target: float = 75.0
    protocol_coverage_target: float = 80.0
    functional_coverage_target: float = 80.0

    # Per-module targets (can override defaults)
    module_targets: Dict[str, Dict[str, float]] = field(default_factory=dict)


@dataclass
class CoverageConfigBase:
    """Base coverage configuration.

    Projects should extend this class to add component-specific settings.

    Example:
        @dataclass
        class StreamCoverageConfig(CoverageConfigBase):
            include_modules: List[str] = field(default_factory=lambda: [
                'scheduler', 'descriptor_engine', 'sram_controller'
            ])
    """
    # Enable/disable coverage types
    enable_line_coverage: bool = True
    enable_toggle_coverage: bool = True
    enable_branch_coverage: bool = True
    enable_protocol_coverage: bool = True
    enable_functional_coverage: bool = True

    # Coverage goals
    goals: CoverageGoals = field(default_factory=CoverageGoals)

    # Output paths (relative to component root)
    coverage_dir: str = "coverage_data"
    per_test_dir: str = "per_test"
    merged_dir: str = "merged"
    report_dir: str = "reports"

    # Verilator-specific settings
    verilator_coverage_flags: List[str] = field(default_factory=lambda: [
        '--coverage',
        '--coverage-line',
        '--coverage-toggle',
    ])

    # Modules to include in coverage (override in subclass)
    include_modules: List[str] = field(default_factory=list)

    # Modules to exclude from coverage
    exclude_modules: List[str] = field(default_factory=list)

    @classmethod
    def from_environment(cls) -> 'CoverageConfigBase':
        """Create config from environment variables."""
        config = cls()

        # Override from environment
        if os.environ.get('COVERAGE_DISABLE', '0') == '1':
            config.enable_line_coverage = False
            config.enable_toggle_coverage = False
            config.enable_branch_coverage = False

        if os.environ.get('COVERAGE_PROTOCOL_ONLY', '0') == '1':
            config.enable_line_coverage = False
            config.enable_toggle_coverage = False
            config.enable_branch_coverage = False
            config.enable_protocol_coverage = True

        if os.environ.get('COVERAGE_DIR'):
            config.coverage_dir = os.environ['COVERAGE_DIR']

        return config

    def get_verilator_compile_args(self) -> List[str]:
        """Get Verilator compile arguments for coverage."""
        args = []

        if self.enable_line_coverage or self.enable_toggle_coverage or self.enable_branch_coverage:
            args.append('--coverage')

        if self.enable_line_coverage:
            args.append('--coverage-line')

        if self.enable_toggle_coverage:
            args.append('--coverage-toggle')

        return args

    def get_coverage_output_path(self, base_dir: str, test_name: str, coverage_type: str) -> str:
        """Get output path for coverage data."""
        return os.path.join(
            base_dir,
            self.coverage_dir,
            self.per_test_dir,
            f"{test_name}_{coverage_type}.dat"
        )


@dataclass
class LegalCoverageConfigBase:
    """Base class for legal coverage configuration.

    "Legal coverage" measures coverage against only the variations that a
    component actually supports, rather than the full protocol space.

    For example, STREAM only uses INCR bursts with 64-byte size, so coverage
    is calculated against that subset rather than all AXI burst combinations.

    Projects should extend this class and define their legal points, or load
    them from a YAML file.

    Example:
        @dataclass
        class StreamLegalConfig(LegalCoverageConfigBase):
            legal_burst_types: Set[str] = field(default_factory=lambda: {'INCR'})
            legal_burst_sizes: Set[int] = field(default_factory=lambda: {64})
    """

    name: str = "base"
    description: str = "Base legal coverage configuration"

    # AXI burst types
    legal_burst_types: Set[str] = field(default_factory=set)
    illegal_burst_types: Set[str] = field(default_factory=set)

    # AXI burst sizes (in bytes)
    legal_burst_sizes: Set[int] = field(default_factory=set)
    illegal_burst_sizes: Set[int] = field(default_factory=set)

    # AXI burst length bins
    legal_burst_lengths: Set[str] = field(default_factory=set)
    optional_burst_lengths: Set[str] = field(default_factory=set)

    # AXI responses
    legal_responses: Set[str] = field(default_factory=set)
    illegal_responses: Set[str] = field(default_factory=set)
    optional_responses: Set[str] = field(default_factory=set)

    # APB transactions
    legal_apb: Set[str] = field(default_factory=set)
    optional_apb: Set[str] = field(default_factory=set)

    # Address alignment
    legal_alignment: Set[str] = field(default_factory=set)
    optional_alignment: Set[str] = field(default_factory=set)
    illegal_alignment: Set[str] = field(default_factory=set)

    # Handshakes
    legal_handshakes: Set[str] = field(default_factory=set)
    optional_handshakes: Set[str] = field(default_factory=set)

    # Scenarios
    critical_scenarios: Set[str] = field(default_factory=set)
    important_scenarios: Set[str] = field(default_factory=set)
    optional_scenarios: Set[str] = field(default_factory=set)

    # Cross coverage
    legal_cross: Set[str] = field(default_factory=set)

    @classmethod
    def load_yaml(cls, yaml_path: str) -> 'LegalCoverageConfigBase':
        """Load legal coverage config from YAML file.

        Args:
            yaml_path: Path to YAML file

        Returns:
            LegalCoverageConfigBase with values from YAML file
        """
        try:
            import yaml
        except ImportError:
            print("Warning: PyYAML not available, returning default config")
            return cls()

        if not os.path.exists(yaml_path):
            print(f"Warning: YAML file not found: {yaml_path}")
            return cls()

        with open(yaml_path, 'r') as f:
            data = yaml.safe_load(f)

        if not data:
            return cls()

        config = cls(
            name=data.get('name', 'loaded'),
            description=data.get('description', '')
        )

        # Parse each section
        config._parse_yaml_section(data, 'axi_burst_types', 'burst_types')
        config._parse_yaml_section(data, 'axi_burst_sizes', 'burst_sizes')
        config._parse_yaml_section(data, 'axi_burst_lengths', 'burst_lengths')
        config._parse_yaml_section(data, 'axi_responses', 'responses')
        config._parse_yaml_section(data, 'apb_transactions', 'apb')
        config._parse_yaml_section(data, 'address_alignment', 'alignment')
        config._parse_yaml_section(data, 'handshakes', 'handshakes')
        config._parse_yaml_section(data, 'scenarios', 'scenarios')
        config._parse_yaml_section(data, 'burst_type_x_size', 'cross')

        return config

    def _parse_yaml_section(self, data: Dict, yaml_key: str, attr_prefix: str):
        """Parse a YAML section into config attributes."""
        if yaml_key not in data:
            return

        section = data[yaml_key]

        # Map YAML keys to attribute names
        mappings = {
            'burst_types': {
                'legal': 'legal_burst_types',
                'illegal': 'illegal_burst_types',
            },
            'burst_sizes': {
                'legal': 'legal_burst_sizes',
                'illegal': 'illegal_burst_sizes',
            },
            'burst_lengths': {
                'legal': 'legal_burst_lengths',
                'optional': 'optional_burst_lengths',
            },
            'responses': {
                'legal': 'legal_responses',
                'illegal': 'illegal_responses',
                'optional': 'optional_responses',
            },
            'apb': {
                'legal': 'legal_apb',
                'optional': 'optional_apb',
            },
            'alignment': {
                'legal': 'legal_alignment',
                'optional': 'optional_alignment',
                'illegal': 'illegal_alignment',
            },
            'handshakes': {
                'legal': 'legal_handshakes',
                'optional': 'optional_handshakes',
            },
            'scenarios': {
                'critical': 'critical_scenarios',
                'important': 'important_scenarios',
                'optional': 'optional_scenarios',
            },
            'cross': {
                'legal': 'legal_cross',
            },
        }

        if attr_prefix not in mappings:
            return

        for yaml_subkey, attr_name in mappings[attr_prefix].items():
            if yaml_subkey in section:
                values = section[yaml_subkey]
                if attr_prefix == 'burst_sizes':
                    # Convert size_XX to integers
                    values = {int(s.replace('size_', '')) for s in values}
                else:
                    values = set(values)
                setattr(self, attr_name, values)

    def get_all_legal_points(self) -> Dict[str, Set[str]]:
        """Get all legal coverage points by category.

        Returns:
            Dictionary mapping category name to set of legal point names
        """
        return {
            'axi_burst_type': self.legal_burst_types,
            'axi_burst_size': {f"size_{s}" for s in self.legal_burst_sizes},
            'axi_burst_length': self.legal_burst_lengths | self.optional_burst_lengths,
            'axi_response': self.legal_responses | self.optional_responses,
            'apb': self.legal_apb | self.optional_apb,
            'alignment': self.legal_alignment | self.optional_alignment,
            'handshake': self.legal_handshakes | self.optional_handshakes,
            'scenario': self.critical_scenarios | self.important_scenarios | self.optional_scenarios,
            'cross': self.legal_cross,
        }

    def get_critical_points(self) -> Dict[str, Set[str]]:
        """Get critical coverage points that MUST be covered."""
        return {
            'axi_burst_type': self.legal_burst_types,
            'axi_burst_size': {f"size_{s}" for s in self.legal_burst_sizes},
            'axi_burst_length': self.legal_burst_lengths,
            'axi_response': self.legal_responses,
            'apb': self.legal_apb,
            'alignment': self.legal_alignment,
            'handshake': self.legal_handshakes,
            'scenario': self.critical_scenarios,
            'cross': self.legal_cross,
        }

    def is_legal(self, category: str, point_name: str) -> bool:
        """Check if a coverage point is legal for this component."""
        legal_points = self.get_all_legal_points()
        if category not in legal_points:
            return True  # Unknown category, assume legal
        return point_name in legal_points[category]

    def count_legal_points(self) -> int:
        """Count total number of legal coverage points."""
        legal = self.get_all_legal_points()
        return sum(len(points) for points in legal.values())

    def count_critical_points(self) -> int:
        """Count number of critical coverage points."""
        critical = self.get_critical_points()
        return sum(len(points) for points in critical.values())
