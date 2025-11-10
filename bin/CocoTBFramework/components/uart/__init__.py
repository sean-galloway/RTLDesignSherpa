# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: UART Components Package
# Purpose: UART BFM components for CocoTB verification
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-11-09

"""
UART Components Package

Provides UART Bus Functional Models (BFMs) for CocoTB verification:
- UARTPacket: Transaction data structure
- UARTMonitor: UART line monitor with packet capture
- UARTMaster: UART transmitter driver
- UARTSlave: UART receiver with auto-response capability

Example Usage:

    from CocoTBFramework.components.uart import UARTMaster, UARTMonitor, UARTPacket

    # Create UART master
    uart_tx = UARTMaster(
        entity=dut,
        title="UART_TX",
        signal_name="uart_tx",
        clock=dut.clk,
        clks_per_bit=868  # 100MHz / 115200 baud
    )

    # Create UART monitor
    uart_rx_mon = UARTMonitor(
        entity=dut,
        title="UART_RX_MON",
        signal_name="uart_rx",
        clock=dut.clk,
        clks_per_bit=868,
        direction='RX'
    )

    # Send data
    await uart_tx.send(0x55)
    await uart_tx.send_string("Hello\\n")

    # Check received
    if uart_rx_mon._recvQ:
        packet = uart_rx_mon._recvQ.popleft()
        assert packet.data == 0x55
"""

from .uart_packet import UARTPacket
from .uart_components import UARTMonitor, UARTMaster, UARTSlave

__all__ = [
    'UARTPacket',
    'UARTMonitor',
    'UARTMaster',
    'UARTSlave',
]
