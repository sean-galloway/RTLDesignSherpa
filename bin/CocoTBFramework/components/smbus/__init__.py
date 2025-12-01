# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: smbus package
# Purpose: SMBus/I2C BFM Components Package
#
# Created: 2025-11-29

"""
SMBus/I2C Bus Functional Model Package

This package provides BFM components for SMBus/I2C verification:
- SMBusPacket: Transaction data structure
- SMBusMonitor: Passive bus monitor
- SMBusMaster: Active master device emulation
- SMBusSlave: Active slave device emulation
- SMBusCRC: CRC-8 calculator for PEC
"""

from .smbus_packet import (
    SMBusPacket,
    SMBusTransactionType,
    SMBusCondition,
)

from .smbus_components import (
    SMBusCRC,
    SMBusMonitor,
    SMBusSlave,
    SMBusMaster,
)

__all__ = [
    # Packet
    'SMBusPacket',
    'SMBusTransactionType',
    'SMBusCondition',
    # Components
    'SMBusCRC',
    'SMBusMonitor',
    'SMBusSlave',
    'SMBusMaster',
]
