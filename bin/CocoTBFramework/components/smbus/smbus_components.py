# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: smbus_components
# Purpose: SMBus/I2C BFM Components (Monitor, Master, Slave)
#
# Documentation: projects/components/retro_legacy_blocks/rtl/smbus/README.md
# Subsystem: CocoTBFramework/components/smbus
#
# Created: 2025-11-29

"""
SMBus/I2C Bus Functional Model Components

This module provides BFM components for SMBus/I2C verification:
- SMBusMonitor: Passive bus monitor for transaction capture
- SMBusMaster: Active master device emulation
- SMBusSlave: Active slave device emulation

The SMBus interface uses tristate signals:
- scl_i: Clock input (from bus)
- scl_o: Clock output (drive low)
- scl_t: Clock tristate (1=input/release, 0=drive)
- sda_i: Data input (from bus)
- sda_o: Data output (drive low)
- sda_t: Data tristate (1=input/release, 0=drive)

Open-drain semantics: To release a line, set _t=1.
To drive low, set _t=0 and _o=0.
"""

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Edge, Timer, First
from cocotb.utils import get_sim_time
from collections import deque
from typing import Optional, List, Callable, Dict, Any
import logging

from .smbus_packet import SMBusPacket, SMBusTransactionType, SMBusCondition


class SMBusCRC:
    """CRC-8 calculator for SMBus PEC (Packet Error Checking)"""

    # CRC-8 polynomial: x^8 + x^2 + x + 1 = 0x07
    POLY = 0x07

    @staticmethod
    def calculate(data: List[int]) -> int:
        """
        Calculate CRC-8 for SMBus PEC.

        Args:
            data: List of bytes to calculate CRC over

        Returns:
            8-bit CRC value
        """
        crc = 0
        for byte in data:
            crc ^= byte
            for _ in range(8):
                if crc & 0x80:
                    crc = ((crc << 1) ^ SMBusCRC.POLY) & 0xFF
                else:
                    crc = (crc << 1) & 0xFF
        return crc


class SMBusMonitor:
    """
    SMBus Bus Monitor

    Passively monitors the SMBus interface and captures transactions.
    Works with tristate interface signals (scl_i, sda_i for monitoring).

    Attributes:
        recv_queue: Queue of received SMBusPacket objects
        transaction_count: Number of transactions captured
    """

    def __init__(self, entity, title: str,
                 scl_signal: str = 'smb_scl_i',
                 sda_signal: str = 'smb_sda_i',
                 clock: Optional[Any] = None,
                 log: Optional[logging.Logger] = None,
                 callback: Optional[Callable[[SMBusPacket], None]] = None):
        """
        Initialize SMBus Monitor.

        Args:
            entity: DUT handle
            title: Monitor title for logging
            scl_signal: Name of SCL input signal
            sda_signal: Name of SDA input signal
            clock: Optional reference clock for timing
            log: Optional logger
            callback: Optional callback for received packets
        """
        self.entity = entity
        self.title = title
        self.scl = getattr(entity, scl_signal)
        self.sda = getattr(entity, sda_signal)
        self.clock = clock
        self.callback = callback

        self.log = log or logging.getLogger(f"cocotb.smbus.{title}")

        self._recv_queue: deque = deque()
        self._transaction_count: int = 0
        self._running: bool = False
        self._monitor_task = None

        # Current transaction state
        self._current_packet: Optional[SMBusPacket] = None
        self._bit_position: int = 0
        self._current_byte: int = 0
        self._bytes_received: List[int] = []

    @property
    def recv_queue(self) -> deque:
        return self._recv_queue

    @property
    def transaction_count(self) -> int:
        return self._transaction_count

    def start(self):
        """Start the monitor"""
        if not self._running:
            self._running = True
            self._monitor_task = cocotb.start_soon(self._monitor_recv())
            self.log.info(f"SMBus Monitor '{self.title}' started")

    def stop(self):
        """Stop the monitor"""
        self._running = False
        if self._monitor_task:
            self._monitor_task.kill()
            self._monitor_task = None
        self.log.info(f"SMBus Monitor '{self.title}' stopped")

    async def _wait_for_start(self):
        """Wait for START condition (SDA falling while SCL high)"""
        while self._running:
            # Wait for SDA falling edge
            await FallingEdge(self.sda)
            # Check if SCL is high (START condition)
            if self.scl.value.integer == 1:
                return True
        return False

    async def _wait_for_stop(self) -> bool:
        """Wait for STOP condition (SDA rising while SCL high)"""
        # Wait for SDA rising edge
        await RisingEdge(self.sda)
        # Check if SCL is high (STOP condition)
        return self.scl.value.integer == 1

    async def _receive_bit(self) -> int:
        """Receive a single bit on SDA, sampled on SCL rising edge"""
        await RisingEdge(self.scl)
        return self.sda.value.integer

    async def _receive_byte(self, with_ack: bool = True) -> tuple:
        """
        Receive a byte and optional ACK.

        Args:
            with_ack: If True, also receive the ACK/NAK bit

        Returns:
            Tuple of (byte_value, ack_received)
        """
        byte_val = 0
        # Receive 8 bits, MSB first
        for i in range(8):
            bit = await self._receive_bit()
            byte_val = (byte_val << 1) | bit

        ack = True
        if with_ack:
            # ACK bit (0 = ACK, 1 = NAK)
            ack_bit = await self._receive_bit()
            ack = (ack_bit == 0)

        return byte_val, ack

    async def _monitor_recv(self):
        """Main monitor receive coroutine"""
        self.log.debug(f"Monitor '{self.title}' starting receive loop")

        while self._running:
            try:
                # Wait for START condition
                if not await self._wait_for_start():
                    break

                start_time = get_sim_time('ns')
                self.log.debug(f"START detected at {start_time}ns")

                # Create new packet
                self._current_packet = SMBusPacket(start_time=start_time)
                self._bytes_received = []

                # Receive address byte
                addr_byte, ack = await self._receive_byte(with_ack=True)
                self._current_packet.slave_addr = (addr_byte >> 1) & 0x7F
                self._current_packet.read_write = addr_byte & 0x01
                self._current_packet.ack_received = ack
                self._bytes_received.append(addr_byte)

                if not ack:
                    # No ACK - transaction aborted
                    self._current_packet.completed = False
                    self._finalize_packet()
                    continue

                # Set direction based on R/W bit
                self._current_packet.direction = 'RX' if self._current_packet.read_write else 'TX'

                # Continue receiving bytes until STOP or repeated START
                transaction_complete = False
                while not transaction_complete:
                    # Try to receive next byte, watching for STOP/START
                    byte_val, ack, condition = await self._receive_byte_with_conditions()

                    if condition == SMBusCondition.STOP:
                        transaction_complete = True
                    elif condition == SMBusCondition.START:
                        # Repeated START - treat as new transaction
                        transaction_complete = True
                    else:
                        self._bytes_received.append(byte_val)
                        if not ack:
                            # NAK typically ends the data phase
                            break

                # Parse the transaction
                self._parse_transaction()
                self._finalize_packet()

            except Exception as e:
                self.log.error(f"Monitor error: {e}")
                if self._current_packet:
                    self._current_packet.completed = False
                    self._finalize_packet()

    async def _receive_byte_with_conditions(self) -> tuple:
        """
        Receive byte while watching for START/STOP conditions.

        Returns:
            Tuple of (byte_value, ack, condition)
        """
        byte_val = 0
        condition = SMBusCondition.IDLE

        for i in range(8):
            # Wait for SCL rising, but check for START/STOP
            result = await self._wait_scl_or_condition()
            if result == SMBusCondition.STOP:
                return byte_val, False, SMBusCondition.STOP
            elif result == SMBusCondition.START:
                return byte_val, False, SMBusCondition.START

            bit = self.sda.value.integer
            byte_val = (byte_val << 1) | bit

            # Wait for SCL falling
            await FallingEdge(self.scl)

        # Receive ACK
        result = await self._wait_scl_or_condition()
        if result == SMBusCondition.STOP:
            return byte_val, False, SMBusCondition.STOP
        elif result == SMBusCondition.START:
            return byte_val, False, SMBusCondition.START

        ack = (self.sda.value.integer == 0)
        await FallingEdge(self.scl)

        return byte_val, ack, SMBusCondition.IDLE

    async def _wait_scl_or_condition(self) -> SMBusCondition:
        """Wait for SCL rising or START/STOP condition"""
        while True:
            # Create combined trigger
            scl_rise = RisingEdge(self.scl)
            sda_edge = Edge(self.sda)

            result = await First(scl_rise, sda_edge)

            # Check what triggered
            if self.scl.value.integer == 1:
                # SCL went high
                # Check if SDA also changed (START/STOP)
                # For now, just return that we got SCL rising
                return SMBusCondition.IDLE

            # SDA changed while SCL high = START or STOP
            if self.scl.value.integer == 1:
                if self.sda.value.integer == 1:
                    return SMBusCondition.STOP
                else:
                    return SMBusCondition.START

    def _parse_transaction(self):
        """Parse received bytes to determine transaction type"""
        if not self._bytes_received or not self._current_packet:
            return

        # First byte is always address
        # Subsequent bytes depend on transaction type
        data_bytes = self._bytes_received[1:]  # Skip address byte

        if len(data_bytes) == 0:
            # Quick Command
            self._current_packet.trans_type = SMBusTransactionType.QUICK_CMD
        elif len(data_bytes) == 1:
            # Send/Receive Byte
            if self._current_packet.is_write:
                self._current_packet.trans_type = SMBusTransactionType.SEND_BYTE
            else:
                self._current_packet.trans_type = SMBusTransactionType.RECV_BYTE
            self._current_packet.data = data_bytes
        elif len(data_bytes) == 2:
            # Write/Read Byte Data
            if self._current_packet.is_write:
                self._current_packet.trans_type = SMBusTransactionType.WRITE_BYTE
                self._current_packet.command = data_bytes[0]
                self._current_packet.data = [data_bytes[1]]
            else:
                self._current_packet.trans_type = SMBusTransactionType.READ_BYTE
                self._current_packet.command = data_bytes[0]
                self._current_packet.data = [data_bytes[1]]
        elif len(data_bytes) == 3:
            # Write/Read Word Data
            if self._current_packet.is_write:
                self._current_packet.trans_type = SMBusTransactionType.WRITE_WORD
                self._current_packet.command = data_bytes[0]
                self._current_packet.data = data_bytes[1:3]
            else:
                self._current_packet.trans_type = SMBusTransactionType.READ_WORD
                self._current_packet.command = data_bytes[0]
                self._current_packet.data = data_bytes[1:3]
        else:
            # Block transfer
            if self._current_packet.is_write:
                self._current_packet.trans_type = SMBusTransactionType.BLOCK_WRITE
            else:
                self._current_packet.trans_type = SMBusTransactionType.BLOCK_READ
            self._current_packet.command = data_bytes[0]
            self._current_packet.byte_count = data_bytes[1] if len(data_bytes) > 1 else 0
            self._current_packet.data = data_bytes[2:] if len(data_bytes) > 2 else []

    def _finalize_packet(self):
        """Finalize and queue the current packet"""
        if self._current_packet:
            self._current_packet.end_time = get_sim_time('ns')
            self._recv_queue.append(self._current_packet)
            self._transaction_count += 1

            self.log.info(f"[{self.title}] {self._current_packet.formatted()}")

            if self.callback:
                self.callback(self._current_packet)

            self._current_packet = None
            self._bytes_received = []


class SMBusSlave:
    """
    SMBus Slave Device Emulation

    Emulates an SMBus slave device that responds to master transactions.
    Uses tristate interface to drive responses.

    Features:
    - Configurable slave address
    - Memory-mapped register model
    - PEC support
    - Clock stretching support
    """

    def __init__(self, entity, title: str,
                 scl_i: str = 'smb_scl_i',
                 scl_o: str = 'smb_scl_o',
                 scl_t: str = 'smb_scl_t',
                 sda_i: str = 'smb_sda_i',
                 sda_o: str = 'smb_sda_o',
                 sda_t: str = 'smb_sda_t',
                 slave_addr: int = 0x50,
                 memory_size: int = 256,
                 clock_stretch_cycles: int = 0,
                 support_pec: bool = False,
                 log: Optional[logging.Logger] = None):
        """
        Initialize SMBus Slave.

        Args:
            entity: DUT handle
            title: Slave title for logging
            scl_i/o/t: SCL signal names
            sda_i/o/t: SDA signal names
            slave_addr: 7-bit slave address
            memory_size: Size of internal memory (bytes)
            clock_stretch_cycles: Cycles to stretch clock (0=disabled)
            support_pec: Enable PEC support
            log: Optional logger
        """
        self.entity = entity
        self.title = title

        # Get signal handles
        self.scl_i = getattr(entity, scl_i)
        self.scl_o = getattr(entity, scl_o)
        self.scl_t = getattr(entity, scl_t)
        self.sda_i = getattr(entity, sda_i)
        self.sda_o = getattr(entity, sda_o)
        self.sda_t = getattr(entity, sda_t)

        self.slave_addr = slave_addr
        self.memory_size = memory_size
        self.clock_stretch_cycles = clock_stretch_cycles
        self.support_pec = support_pec

        self.log = log or logging.getLogger(f"cocotb.smbus_slave.{title}")

        # Internal memory
        self.memory: Dict[int, int] = {}
        self._current_addr: int = 0

        # State
        self._running: bool = False
        self._slave_task = None

        # Statistics
        self.transaction_count: int = 0
        self.ack_count: int = 0
        self.nak_count: int = 0

    def start(self):
        """Start the slave"""
        if not self._running:
            self._running = True
            # Release bus
            self._release_scl()
            self._release_sda()
            self._slave_task = cocotb.start_soon(self._slave_loop())
            self.log.info(f"SMBus Slave '{self.title}' started at address 0x{self.slave_addr:02X}")

    def stop(self):
        """Stop the slave"""
        self._running = False
        if self._slave_task:
            self._slave_task.kill()
            self._slave_task = None
        self._release_scl()
        self._release_sda()
        self.log.info(f"SMBus Slave '{self.title}' stopped")

    def _release_scl(self):
        """Release SCL (tristate)"""
        self.scl_t.value = 1
        self.scl_o.value = 1

    def _drive_scl_low(self):
        """Drive SCL low"""
        self.scl_t.value = 0
        self.scl_o.value = 0

    def _release_sda(self):
        """Release SDA (tristate)"""
        self.sda_t.value = 1
        self.sda_o.value = 1

    def _drive_sda_low(self):
        """Drive SDA low"""
        self.sda_t.value = 0
        self.sda_o.value = 0

    def _drive_sda(self, value: int):
        """Drive SDA to specific value"""
        if value:
            self._release_sda()
        else:
            self._drive_sda_low()

    async def _send_ack(self):
        """Send ACK (drive SDA low)"""
        self._drive_sda_low()
        await RisingEdge(self.scl_i)
        await FallingEdge(self.scl_i)
        self._release_sda()
        self.ack_count += 1

    async def _send_nak(self):
        """Send NAK (release SDA)"""
        self._release_sda()
        await RisingEdge(self.scl_i)
        await FallingEdge(self.scl_i)
        self.nak_count += 1

    async def _receive_bit(self) -> int:
        """Receive a bit from the bus"""
        await RisingEdge(self.scl_i)
        bit = self.sda_i.value.integer
        await FallingEdge(self.scl_i)
        return bit

    async def _send_bit(self, bit: int):
        """Send a bit to the bus"""
        self._drive_sda(bit)
        await RisingEdge(self.scl_i)
        await FallingEdge(self.scl_i)

    async def _receive_byte(self) -> int:
        """Receive a byte from master"""
        byte_val = 0
        for _ in range(8):
            bit = await self._receive_bit()
            byte_val = (byte_val << 1) | bit
        return byte_val

    async def _send_byte(self, byte_val: int) -> bool:
        """Send a byte to master, return True if ACK received"""
        # Send 8 bits MSB first
        for i in range(7, -1, -1):
            bit = (byte_val >> i) & 1
            await self._send_bit(bit)

        # Release SDA for ACK
        self._release_sda()

        # Receive ACK
        await RisingEdge(self.scl_i)
        ack = (self.sda_i.value.integer == 0)
        await FallingEdge(self.scl_i)

        return ack

    async def _wait_for_start(self) -> bool:
        """Wait for START condition"""
        while self._running:
            await FallingEdge(self.sda_i)
            if self.scl_i.value.integer == 1:
                return True
        return False

    async def _check_for_stop(self) -> bool:
        """Check if STOP condition occurred"""
        # STOP is SDA rising while SCL high
        return (self.scl_i.value.integer == 1 and
                self.sda_i.value.integer == 1)

    async def _slave_loop(self):
        """Main slave processing loop"""
        self.log.debug(f"Slave '{self.title}' starting main loop")

        while self._running:
            try:
                # Wait for START
                if not await self._wait_for_start():
                    break

                self.log.debug("START detected")

                # Receive address byte
                addr_byte = await self._receive_byte()
                recv_addr = (addr_byte >> 1) & 0x7F
                is_read = addr_byte & 0x01

                self.log.debug(f"Address: 0x{recv_addr:02X}, R/W: {is_read}")

                # Check if address matches
                if recv_addr != self.slave_addr:
                    self.log.debug(f"Address mismatch (expected 0x{self.slave_addr:02X})")
                    continue

                # Send ACK
                await self._send_ack()
                self.transaction_count += 1

                if is_read:
                    # Master read - slave sends data
                    await self._handle_read()
                else:
                    # Master write - slave receives data
                    await self._handle_write()

            except Exception as e:
                self.log.error(f"Slave error: {e}")

    async def _handle_write(self):
        """Handle master write transaction"""
        bytes_received = []

        # First byte after address is typically command/register address
        byte = await self._receive_byte()
        self._current_addr = byte
        bytes_received.append(byte)
        await self._send_ack()

        # Receive remaining data bytes
        while True:
            # Check for STOP before receiving
            await Timer(10, units='ns')  # Small delay to check bus state

            try:
                byte = await self._receive_byte()
                bytes_received.append(byte)

                # Store in memory
                self.memory[self._current_addr] = byte
                self._current_addr = (self._current_addr + 1) % self.memory_size

                await self._send_ack()
            except Exception:
                # Likely STOP condition
                break

        self.log.info(f"[{self.title}] Write: cmd=0x{bytes_received[0]:02X}, "
                      f"data={[f'0x{b:02X}' for b in bytes_received[1:]]}")

    async def _handle_read(self):
        """Handle master read transaction"""
        bytes_sent = []

        while True:
            # Get data from memory
            data = self.memory.get(self._current_addr, 0xFF)
            bytes_sent.append(data)

            # Send byte
            ack = await self._send_byte(data)
            self._current_addr = (self._current_addr + 1) % self.memory_size

            if not ack:
                # Master sent NAK - end of read
                break

        self.log.info(f"[{self.title}] Read: addr=0x{self._current_addr:02X}, "
                      f"data={[f'0x{b:02X}' for b in bytes_sent]}")

    def write_memory(self, addr: int, data: List[int]):
        """Pre-load data into slave memory"""
        for i, byte in enumerate(data):
            self.memory[(addr + i) % self.memory_size] = byte

    def read_memory(self, addr: int, length: int = 1) -> List[int]:
        """Read data from slave memory"""
        return [self.memory.get((addr + i) % self.memory_size, 0xFF)
                for i in range(length)]

    def clear_memory(self):
        """Clear all memory"""
        self.memory.clear()


class SMBusMaster:
    """
    SMBus Master Device Emulation

    Emulates an SMBus master that can initiate transactions.
    Used for testing slave devices or protocol verification.

    Note: For testing the apb_smbus RTL which is a master, you typically
    need the SMBusSlave to respond to it. This SMBusMaster is useful for
    testing scenarios where external master access is needed.
    """

    def __init__(self, entity, title: str,
                 scl_i: str = 'smb_scl_i',
                 scl_o: str = 'smb_scl_o',
                 scl_t: str = 'smb_scl_t',
                 sda_i: str = 'smb_sda_i',
                 sda_o: str = 'smb_sda_o',
                 sda_t: str = 'smb_sda_t',
                 clock_period_ns: int = 10000,  # 100kHz default
                 support_pec: bool = False,
                 log: Optional[logging.Logger] = None):
        """
        Initialize SMBus Master.

        Args:
            entity: DUT handle
            title: Master title for logging
            scl_i/o/t: SCL signal names
            sda_i/o/t: SDA signal names
            clock_period_ns: SCL clock period in nanoseconds
            support_pec: Enable PEC support
            log: Optional logger
        """
        self.entity = entity
        self.title = title

        # Get signal handles
        self.scl_i = getattr(entity, scl_i)
        self.scl_o = getattr(entity, scl_o)
        self.scl_t = getattr(entity, scl_t)
        self.sda_i = getattr(entity, sda_i)
        self.sda_o = getattr(entity, sda_o)
        self.sda_t = getattr(entity, sda_t)

        self.clock_period_ns = clock_period_ns
        self.half_period_ns = clock_period_ns // 2
        self.support_pec = support_pec

        self.log = log or logging.getLogger(f"cocotb.smbus_master.{title}")

        # Statistics
        self.transaction_count: int = 0

    def _release_scl(self):
        """Release SCL"""
        self.scl_t.value = 1
        self.scl_o.value = 1

    def _drive_scl_low(self):
        """Drive SCL low"""
        self.scl_t.value = 0
        self.scl_o.value = 0

    def _release_sda(self):
        """Release SDA"""
        self.sda_t.value = 1
        self.sda_o.value = 1

    def _drive_sda_low(self):
        """Drive SDA low"""
        self.sda_t.value = 0
        self.sda_o.value = 0

    def _drive_sda(self, value: int):
        """Drive SDA to value"""
        if value:
            self._release_sda()
        else:
            self._drive_sda_low()

    async def _delay(self, ns: int = None):
        """Wait for specified nanoseconds"""
        if ns is None:
            ns = self.half_period_ns
        await Timer(ns, units='ns')

    async def _generate_start(self):
        """Generate START condition"""
        # Ensure bus is idle (both high)
        self._release_sda()
        self._release_scl()
        await self._delay()

        # SDA falling while SCL high = START
        self._drive_sda_low()
        await self._delay()

        # Pull SCL low to begin
        self._drive_scl_low()
        await self._delay()

    async def _generate_stop(self):
        """Generate STOP condition"""
        # Ensure SCL is low, SDA is low
        self._drive_scl_low()
        self._drive_sda_low()
        await self._delay()

        # Release SCL
        self._release_scl()
        await self._delay()

        # SDA rising while SCL high = STOP
        self._release_sda()
        await self._delay()

    async def _generate_repeated_start(self):
        """Generate repeated START condition"""
        # Release SDA while SCL low
        self._release_sda()
        await self._delay()

        # Release SCL
        self._release_scl()
        await self._delay()

        # SDA falling while SCL high = repeated START
        self._drive_sda_low()
        await self._delay()

        # Pull SCL low
        self._drive_scl_low()
        await self._delay()

    async def _send_bit(self, bit: int):
        """Send a single bit"""
        # Set SDA while SCL low
        self._drive_sda(bit)
        await self._delay()

        # Clock high
        self._release_scl()
        await self._delay()

        # Clock low
        self._drive_scl_low()
        await self._delay()

    async def _receive_bit(self) -> int:
        """Receive a single bit"""
        # Release SDA
        self._release_sda()
        await self._delay()

        # Clock high
        self._release_scl()
        await self._delay()

        # Sample SDA
        bit = self.sda_i.value.integer

        # Clock low
        self._drive_scl_low()
        await self._delay()

        return bit

    async def _send_byte(self, byte_val: int) -> bool:
        """Send a byte and receive ACK, return True if ACK received"""
        # Send 8 bits MSB first
        for i in range(7, -1, -1):
            bit = (byte_val >> i) & 1
            await self._send_bit(bit)

        # Receive ACK
        ack_bit = await self._receive_bit()
        return ack_bit == 0  # ACK = 0

    async def _receive_byte(self, send_ack: bool = True) -> int:
        """Receive a byte and send ACK/NAK"""
        byte_val = 0
        for _ in range(8):
            bit = await self._receive_bit()
            byte_val = (byte_val << 1) | bit

        # Send ACK (0) or NAK (1)
        await self._send_bit(0 if send_ack else 1)

        return byte_val

    async def quick_command(self, slave_addr: int, read: bool = False) -> SMBusPacket:
        """
        Execute Quick Command transaction.

        Args:
            slave_addr: 7-bit slave address
            read: True for read, False for write

        Returns:
            SMBusPacket with transaction result
        """
        packet = SMBusPacket(
            start_time=get_sim_time('ns'),
            trans_type=SMBusTransactionType.QUICK_CMD,
            slave_addr=slave_addr,
            read_write=1 if read else 0
        )

        await self._generate_start()

        addr_byte = (slave_addr << 1) | (1 if read else 0)
        packet.ack_received = await self._send_byte(addr_byte)

        await self._generate_stop()

        packet.end_time = get_sim_time('ns')
        packet.completed = True
        self.transaction_count += 1

        self.log.info(f"[{self.title}] {packet.formatted()}")
        return packet

    async def write_byte_data(self, slave_addr: int, command: int,
                               data: int) -> SMBusPacket:
        """
        Execute Write Byte Data transaction.

        Args:
            slave_addr: 7-bit slave address
            command: Command byte
            data: Data byte to write

        Returns:
            SMBusPacket with transaction result
        """
        packet = SMBusPacket(
            start_time=get_sim_time('ns'),
            trans_type=SMBusTransactionType.WRITE_BYTE,
            slave_addr=slave_addr,
            read_write=0,
            command=command,
            data=[data]
        )

        await self._generate_start()

        # Send address (write)
        addr_byte = (slave_addr << 1) | 0
        packet.ack_received = await self._send_byte(addr_byte)

        if packet.ack_received:
            # Send command
            await self._send_byte(command)
            # Send data
            await self._send_byte(data)

        await self._generate_stop()

        packet.end_time = get_sim_time('ns')
        packet.completed = True
        self.transaction_count += 1

        self.log.info(f"[{self.title}] {packet.formatted()}")
        return packet

    async def read_byte_data(self, slave_addr: int, command: int) -> SMBusPacket:
        """
        Execute Read Byte Data transaction.

        Args:
            slave_addr: 7-bit slave address
            command: Command byte

        Returns:
            SMBusPacket with transaction result (data in packet.data)
        """
        packet = SMBusPacket(
            start_time=get_sim_time('ns'),
            trans_type=SMBusTransactionType.READ_BYTE,
            slave_addr=slave_addr,
            read_write=1,
            command=command
        )

        await self._generate_start()

        # Send address (write) for command
        addr_byte = (slave_addr << 1) | 0
        packet.ack_received = await self._send_byte(addr_byte)

        if packet.ack_received:
            # Send command
            await self._send_byte(command)

            # Repeated START
            await self._generate_repeated_start()

            # Send address (read)
            addr_byte = (slave_addr << 1) | 1
            await self._send_byte(addr_byte)

            # Receive data byte (NAK to end)
            data = await self._receive_byte(send_ack=False)
            packet.data = [data]

        await self._generate_stop()

        packet.end_time = get_sim_time('ns')
        packet.completed = True
        self.transaction_count += 1

        self.log.info(f"[{self.title}] {packet.formatted()}")
        return packet

    async def block_write(self, slave_addr: int, command: int,
                          data: List[int]) -> SMBusPacket:
        """
        Execute Block Write transaction.

        Args:
            slave_addr: 7-bit slave address
            command: Command byte
            data: List of data bytes to write

        Returns:
            SMBusPacket with transaction result
        """
        packet = SMBusPacket(
            start_time=get_sim_time('ns'),
            trans_type=SMBusTransactionType.BLOCK_WRITE,
            slave_addr=slave_addr,
            read_write=0,
            command=command,
            data=data.copy(),
            byte_count=len(data)
        )

        await self._generate_start()

        # Send address (write)
        addr_byte = (slave_addr << 1) | 0
        packet.ack_received = await self._send_byte(addr_byte)

        if packet.ack_received:
            # Send command
            await self._send_byte(command)

            # Send byte count
            await self._send_byte(len(data))

            # Send data bytes
            for byte in data:
                await self._send_byte(byte)

        await self._generate_stop()

        packet.end_time = get_sim_time('ns')
        packet.completed = True
        self.transaction_count += 1

        self.log.info(f"[{self.title}] {packet.formatted()}")
        return packet

    async def block_read(self, slave_addr: int, command: int,
                         max_bytes: int = 32) -> SMBusPacket:
        """
        Execute Block Read transaction.

        Args:
            slave_addr: 7-bit slave address
            command: Command byte
            max_bytes: Maximum bytes to read

        Returns:
            SMBusPacket with transaction result (data in packet.data)
        """
        packet = SMBusPacket(
            start_time=get_sim_time('ns'),
            trans_type=SMBusTransactionType.BLOCK_READ,
            slave_addr=slave_addr,
            read_write=1,
            command=command
        )

        await self._generate_start()

        # Send address (write) for command
        addr_byte = (slave_addr << 1) | 0
        packet.ack_received = await self._send_byte(addr_byte)

        if packet.ack_received:
            # Send command
            await self._send_byte(command)

            # Repeated START
            await self._generate_repeated_start()

            # Send address (read)
            addr_byte = (slave_addr << 1) | 1
            await self._send_byte(addr_byte)

            # Receive byte count
            byte_count = await self._receive_byte(send_ack=True)
            packet.byte_count = min(byte_count, max_bytes)

            # Receive data bytes
            packet.data = []
            for i in range(packet.byte_count):
                # NAK on last byte
                is_last = (i == packet.byte_count - 1)
                data = await self._receive_byte(send_ack=not is_last)
                packet.data.append(data)

        await self._generate_stop()

        packet.end_time = get_sim_time('ns')
        packet.completed = True
        self.transaction_count += 1

        self.log.info(f"[{self.title}] {packet.formatted()}")
        return packet
