# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: UARTMonitor, UARTMaster, UARTSlave
# Purpose: UART Monitor, Master, and Slave Classes
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-11-09

"""UART Monitor, Master, and Slave Classes"""

from collections import deque

import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, FallingEdge, Timer, Edge
from cocotb_bus.monitors import BusMonitor
from cocotb_bus.drivers import BusDriver

from .uart_packet import UARTPacket


class UARTMonitor(BusMonitor):
    """
    UART RX/TX Monitor

    Monitors UART signals and captures complete byte transactions.

    Args:
        entity: CocoTB DUT entity
        title: Monitor name for logging
        signal_name: Name of UART signal to monitor ('rx' or 'tx')
        clock: Reference clock (for time correlation, not used for sampling)
        clks_per_bit: Number of clock cycles per UART bit time
        direction: 'TX' or 'RX' for packet labeling
        log: Logger instance (optional)

    Attributes:
        _recvQ: Deque of received UARTPacket objects
    """

    def __init__(self, entity, title, signal_name, clock, clks_per_bit=868,
                 direction='RX', log=None, **kwargs):
        # UART monitor doesn't use bus infrastructure (single wire)
        # So we manually set up the signal
        self.signal = getattr(entity, signal_name)
        self.entity = entity
        self.title = title
        self.log = log or entity._log
        self.clock = clock
        self.clks_per_bit = clks_per_bit
        self.direction = direction
        self.count = 0

        # Receive queue for captured packets
        self._recvQ = deque()

        # Start monitoring
        self._recv_coro = cocotb.start_soon(self._monitor_recv())

    def print(self, packet):
        """Print packet in debug log"""
        msg = f'{self.title} - UART Transaction: {packet.formatted(compact=True)}'
        self.log.debug(msg)

    async def _monitor_recv(self):
        """
        Monitor UART line and capture complete byte transactions

        UART protocol (8N1):
        - Idle state: line high
        - Start bit: line goes low
        - 8 data bits: LSB first
        - Stop bit: line goes high
        """
        while True:
            # Wait for start bit (falling edge on idle line)
            while True:
                await Edge(self.signal)
                if self.signal.value.integer == 0:  # Start bit detected
                    break

            start_time = get_sim_time('ns')

            # Wait to middle of start bit to verify it's stable
            await self._wait_bit_periods(0.5)

            if self.signal.value.integer != 0:
                # False start bit - return to idle detection
                continue

            # Sample 8 data bits (LSB first)
            data = 0
            for bit_idx in range(8):
                await self._wait_bit_periods(1.0)
                bit_val = self.signal.value.integer
                data |= (bit_val << bit_idx)

            # Sample stop bit
            await self._wait_bit_periods(1.0)
            stop_bit = self.signal.value.integer
            framing_error = (stop_bit != 1)

            self.count += 1

            # Create packet
            packet = UARTPacket(
                start_time=start_time,
                count=self.count,
                data=data,
                parity=None,  # No parity for 8N1
                parity_error=False,
                framing_error=framing_error,
                direction=self.direction
            )

            # Add to queue
            self._recvQ.append(packet)
            self.print(packet)

    async def _wait_bit_periods(self, periods):
        """
        Wait for specified number of bit periods

        Args:
            periods: Number of bit periods to wait (can be fractional)
        """
        clocks_to_wait = int(self.clks_per_bit * periods)
        for _ in range(clocks_to_wait):
            await RisingEdge(self.clock)


class UARTMaster(BusDriver):
    """
    UART TX Master (Transmitter)

    Drives UART TX line with byte transactions.

    Args:
        entity: CocoTB DUT entity
        title: Master name for logging
        signal_name: Name of UART TX signal
        clock: Reference clock
        clks_per_bit: Number of clock cycles per UART bit time
        log: Logger instance (optional)

    Methods:
        send(data): Send single byte (0-255)
        send_bytes(data_list): Send list of bytes
        send_string(string): Send ASCII string
    """

    def __init__(self, entity, title, signal_name, clock, clks_per_bit=868,
                 log=None, **kwargs):
        self.signal = getattr(entity, signal_name)
        self.entity = entity
        self.title = title
        self.log = log or entity._log
        self.clock = clock
        self.clks_per_bit = clks_per_bit

        # Initialize TX line to idle (high)
        self.signal.value = 1

    async def send(self, data):
        """
        Send single byte over UART

        Args:
            data: Byte value (0-255) or character

        Returns:
            UARTPacket of transmitted data
        """
        if isinstance(data, str):
            data = ord(data)

        assert 0 <= data <= 0xFF, f"Data out of range: 0x{data:X}"

        start_time = get_sim_time('ns')

        # Start bit (low)
        self.signal.value = 0
        await self._wait_bit_periods(1.0)

        # 8 data bits (LSB first)
        for bit_idx in range(8):
            bit_val = (data >> bit_idx) & 0x1
            self.signal.value = bit_val
            await self._wait_bit_periods(1.0)

        # Stop bit (high)
        self.signal.value = 1
        await self._wait_bit_periods(1.0)

        packet = UARTPacket(
            start_time=start_time,
            count=0,  # Master doesn't track count
            data=data,
            direction='TX'
        )

        self.log.debug(f'{self.title} - Sent: {packet.formatted(compact=True)}')

        return packet

    async def send_bytes(self, data_list):
        """
        Send list of bytes over UART

        Args:
            data_list: List of byte values or bytes object

        Returns:
            List of UARTPacket for each transmitted byte
        """
        packets = []
        for byte_val in data_list:
            if isinstance(byte_val, str):
                byte_val = ord(byte_val)
            packet = await self.send(byte_val)
            packets.append(packet)
        return packets

    async def send_string(self, string):
        """
        Send ASCII string over UART

        Args:
            string: String to transmit

        Returns:
            List of UARTPacket for each character
        """
        return await self.send_bytes([ord(c) for c in string])

    async def _wait_bit_periods(self, periods):
        """Wait for specified number of bit periods"""
        clocks_to_wait = int(self.clks_per_bit * periods)
        for _ in range(clocks_to_wait):
            await RisingEdge(self.clock)


class UARTSlave(BusDriver):
    """
    UART RX Slave (Responder)

    Receives UART data and can respond with programmed sequences.
    Useful for testing UART command-response protocols.

    Args:
        entity: CocoTB DUT entity
        rx_signal_name: Name of UART RX input signal (DUT receives on this)
        tx_signal_name: Name of UART TX output signal (DUT transmits on this)
        clock: Reference clock
        clks_per_bit: Number of clock cycles per UART bit time
        log: Logger instance (optional)

    Attributes:
        rx_queue: Deque of received bytes (integers 0-255)
        response_map: Dictionary mapping received bytes to response sequences

    Methods:
        add_response(trigger, response): Add auto-response for received byte
        get_received(): Get next received byte (non-blocking)
        wait_for_byte(expected, timeout): Wait for specific byte with timeout
    """

    def __init__(self, entity, title, rx_signal_name, tx_signal_name, clock,
                 clks_per_bit=868, log=None, **kwargs):
        self.rx_signal = getattr(entity, rx_signal_name)
        self.tx_signal = getattr(entity, tx_signal_name)
        self.entity = entity
        self.title = title
        self.log = log or entity._log
        self.clock = clock
        self.clks_per_bit = clks_per_bit

        # RX monitoring
        self.rx_queue = deque()
        self._rx_coro = cocotb.start_soon(self._monitor_rx())

        # Auto-response capability
        self.response_map = {}

        # Initialize TX line to idle
        self.tx_signal.value = 1

    async def _monitor_rx(self):
        """Monitor RX line and capture received bytes"""
        while True:
            # Wait for start bit
            while True:
                await Edge(self.rx_signal)
                if self.rx_signal.value.integer == 0:
                    break

            # Wait to middle of start bit
            await self._wait_bit_periods(0.5)

            if self.rx_signal.value.integer != 0:
                continue  # False start

            # Sample 8 data bits
            data = 0
            for bit_idx in range(8):
                await self._wait_bit_periods(1.0)
                bit_val = self.rx_signal.value.integer
                data |= (bit_val << bit_idx)

            # Wait for stop bit
            await self._wait_bit_periods(1.0)

            # Add to queue
            self.rx_queue.append(data)
            self.log.debug(f'{self.title} - Received: 0x{data:02X} ({chr(data) if 32 <= data <= 126 else "?"})')

            # Check for auto-response
            if data in self.response_map:
                response = self.response_map[data]
                cocotb.start_soon(self._send_response(response))

    async def _send_response(self, response):
        """Send auto-response (can be byte, list, or string)"""
        if isinstance(response, int):
            await self._send_byte(response)
        elif isinstance(response, str):
            for char in response:
                await self._send_byte(ord(char))
        else:  # List or bytes
            for byte_val in response:
                if isinstance(byte_val, str):
                    byte_val = ord(byte_val)
                await self._send_byte(byte_val)

    async def _send_byte(self, data):
        """Send single byte on TX line"""
        # Start bit
        self.tx_signal.value = 0
        await self._wait_bit_periods(1.0)

        # Data bits
        for bit_idx in range(8):
            bit_val = (data >> bit_idx) & 0x1
            self.tx_signal.value = bit_val
            await self._wait_bit_periods(1.0)

        # Stop bit
        self.tx_signal.value = 1
        await self._wait_bit_periods(1.0)

    def add_response(self, trigger, response):
        """
        Add auto-response for received byte

        Args:
            trigger: Received byte value (0-255) that triggers response
            response: Response to send (byte, list of bytes, or string)
        """
        if isinstance(trigger, str):
            trigger = ord(trigger)
        self.response_map[trigger] = response

    def get_received(self):
        """
        Get next received byte (non-blocking)

        Returns:
            Received byte value (0-255) or None if queue empty
        """
        if self.rx_queue:
            return self.rx_queue.popleft()
        return None

    async def wait_for_byte(self, expected, timeout_cycles=1000):
        """
        Wait for specific byte with timeout

        Args:
            expected: Expected byte value or character
            timeout_cycles: Timeout in clock cycles

        Returns:
            True if byte received, False if timeout

        Raises:
            AssertionError if received byte doesn't match expected
        """
        if isinstance(expected, str):
            expected = ord(expected)

        for _ in range(timeout_cycles):
            if self.rx_queue:
                received = self.rx_queue.popleft()
                assert received == expected, f"Expected 0x{expected:02X}, got 0x{received:02X}"
                return True
            await RisingEdge(self.clock)

        return False  # Timeout

    async def _wait_bit_periods(self, periods):
        """Wait for specified number of bit periods"""
        clocks_to_wait = int(self.clks_per_bit * periods)
        for _ in range(clocks_to_wait):
            await RisingEdge(self.clock)
