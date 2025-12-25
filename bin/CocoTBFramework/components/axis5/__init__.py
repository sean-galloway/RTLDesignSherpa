# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIS5 Components Package
# Purpose: AXI5-Stream Protocol Implementation with AMBA5 extensions
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""
AXIS5 Components Package - AXI5-Stream Protocol Implementation

This package provides AXI5-Stream protocol support with AMBA5 extensions:
- TWAKEUP: Wake-up signaling for power management
- TPARITY: Optional parity for TDATA integrity

Components:
- AXIS5Packet: Stream data packet with AXIS5 extensions
- AXIS5Transaction: Transaction generator with randomization
- AXIS5Master: Stream data transmission with wakeup/parity
- AXIS5Slave: Stream data reception with wakeup/parity
- AXIS5Monitor: Stream transaction monitoring with AXIS5 events

Factory Functions:
- create_axis5_master()
- create_axis5_slave()
- create_axis5_monitor()
- create_axis5_testbench()

The API extends AXIS4 components while maintaining backward compatibility.
"""

from .axis5_packet import AXIS5Packet, AXIS5Transaction
from .axis5_master import AXIS5Master
from .axis5_slave import AXIS5Slave
from .axis5_monitor import AXIS5Monitor
from .axis5_field_configs import AXIS5FieldConfigs
from .axis5_factories import (
    create_axis5_master,
    create_axis5_slave,
    create_axis5_monitor,
    create_axis5_testbench,
    create_axis5_master_interface,
    create_axis5_slave_interface,
    create_simple_axis5_master,
    create_simple_axis5_slave,
    get_axis5_signal_map,
    print_axis5_stats_to_log,
    get_axis5_stats_summary,
)

# Version information
__version__ = "1.0.0"
__author__ = "RTL Design Sherpa"

# Export all public components
__all__ = [
    # Core classes
    'AXIS5Packet',
    'AXIS5Transaction',
    'AXIS5Master',
    'AXIS5Slave',
    'AXIS5Monitor',

    # Field Configurations
    'AXIS5FieldConfigs',

    # Factory functions
    'create_axis5_master',
    'create_axis5_slave',
    'create_axis5_monitor',
    'create_axis5_testbench',
    'create_axis5_master_interface',
    'create_axis5_slave_interface',
    'create_simple_axis5_master',
    'create_simple_axis5_slave',

    # Utilities
    'get_axis5_signal_map',
    'print_axis5_stats_to_log',
    'get_axis5_stats_summary',
]
