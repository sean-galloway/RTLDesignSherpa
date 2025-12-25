# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APB5 Components Package
# Purpose: APB5 Protocol components with AMBA5 extensions
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""APB5 Protocol Components with AMBA5 Extensions.

This package provides APB5 protocol support including:
- APB5Packet: Extended packet with user signals, wakeup, parity
- APB5Master: Master BFM with APB5 signal support
- APB5Slave: Slave BFM with APB5 signal support
- APB5Monitor: Protocol monitor with APB5 event tracking
"""

from .apb5_packet import APB5Packet, APB5Transaction
from .apb5_components import APB5Master, APB5Slave, APB5Monitor
from .apb5_factories import create_apb5_master, create_apb5_slave, create_apb5_monitor

__all__ = [
    'APB5Packet',
    'APB5Transaction',
    'APB5Master',
    'APB5Slave',
    'APB5Monitor',
    'create_apb5_master',
    'create_apb5_slave',
    'create_apb5_monitor',
]
