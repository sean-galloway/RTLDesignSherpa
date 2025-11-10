#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Package: bridge_pkg (V2 - Module-based)
# Purpose: AXI4 Bridge Generator using rtl_generators.Module infrastructure
#
# Author: sean galloway
# Created: 2025-11-01

"""
Bridge Generator Package - V2 (Adapter-first architecture)

This package generates AXI4 crossbar bridges using the proven rtl_generators.Module
infrastructure (same as multipliers). Key features:

- Type-safe module instantiation (Module.instantiate())
- Hierarchical composition (no string concatenation)
- Automatic port/param management
- Jinja2 templates for test generation
- Intelligent width-aware routing (adapter-first, no double conversion)

Architecture:
- config.py - Data structures (PortSpec, BridgeConfig)
- csv_parser.py - Parse CSV configuration files
- components/bridge_module_generator.py - Main bridge generator
- components/ - Sub-component generators (arbiters, adapters, converters)
- generators/ - Adapter and package generators
- templates/ - Jinja2 templates for tests/TB
"""

from .config import PortSpec, BridgeConfig
from .csv_parser import parse_ports_csv, parse_connectivity_csv
from .config_loader import load_config
from .config_validator import validate_config, ValidationError
from .components.bridge_module_generator import BridgeModuleGenerator
from .generators.adapter_generator import MasterConfig, SlaveInfo
from .generators.package_generator import PackageGenerator
from .generators.adapter_generator import AdapterGenerator

__all__ = [
    'PortSpec',
    'BridgeConfig',
    'parse_ports_csv',
    'parse_connectivity_csv',
    'load_config',
    'validate_config',
    'ValidationError',
    'BridgeModuleGenerator',
    'MasterConfig',
    'SlaveInfo',
    'PackageGenerator',
    'AdapterGenerator',
]

__version__ = '2.1.0'
