# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SMBusRegisterMap, SMBusTB
# Purpose: SMBus 2.0 Controller Testbench
#
# Documentation: projects/components/retro_legacy_blocks/rtl/smbus/README.md
# Subsystem: retro_legacy_blocks/smbus
#
# Created: 2025-11-29

"""
SMBus 2.0 Controller Testbench

Comprehensive testbench for the APB SMBus module providing:
- APB register access verification
- SMBus master transaction testing
- SMBus slave response handling
- PEC (Packet Error Checking) verification
- FIFO operation testing
- Timeout detection verification
- Multiple transaction type support

Features:
- APB register access
- SMBus slave BFM for response
- Transaction type programming
- Status monitoring
- FIFO operations
"""

import os
import random
import asyncio
from typing import Dict, List, Optional, Tuple

import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, Timer, FallingEdge, ClockCycles, Edge
from cocotb.clock import Clock

from CocoTBFramework.components.apb.apb_packet import APBPacket
from CocoTBFramework.components.apb.apb_components import APBMaster
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.amba.amba_random_configs import APB_MASTER_RANDOMIZER_CONFIGS
from CocoTBFramework.components.smbus import SMBusSlave, SMBusMonitor, SMBusPacket


class SMBusRegisterMap:
    """SMBus Register address definitions."""

    # Configuration and control registers
    SMBUS_CONTROL = 0x000      # Global control (enable, mode, PEC)
    SMBUS_STATUS = 0x004       # Status flags (busy, errors, state)
    SMBUS_COMMAND = 0x008      # Transaction command and trigger
    SMBUS_SLAVE_ADDR = 0x00C   # Target slave address
    SMBUS_DATA = 0x010         # Single byte data register
    SMBUS_TX_FIFO = 0x014      # Transmit FIFO write port
    SMBUS_RX_FIFO = 0x018      # Receive FIFO read port
    SMBUS_FIFO_STATUS = 0x01C  # FIFO levels and flags
    SMBUS_CLK_DIV = 0x020      # Clock divider configuration
    SMBUS_TIMEOUT = 0x024      # Timeout threshold
    SMBUS_OWN_ADDR = 0x028     # Own slave address (slave mode)
    SMBUS_INT_ENABLE = 0x02C   # Interrupt enable mask
    SMBUS_INT_STATUS = 0x030   # Interrupt status (W1C)
    SMBUS_PEC = 0x034          # PEC value register
    SMBUS_BLOCK_COUNT = 0x038  # Block transfer count

    # SMBUS_CONTROL bit definitions
    CONTROL_MASTER_EN = (1 << 0)       # Enable master mode
    CONTROL_SLAVE_EN = (1 << 1)        # Enable slave mode
    CONTROL_PEC_EN = (1 << 2)          # Enable PEC
    CONTROL_FAST_MODE = (1 << 3)       # 400kHz mode (vs 100kHz)
    CONTROL_FIFO_RESET = (1 << 4)      # Reset FIFOs

    # SMBUS_STATUS bit definitions
    STATUS_BUSY = (1 << 0)             # Transaction in progress
    STATUS_BUS_ERROR = (1 << 1)        # Bus error detected
    STATUS_TIMEOUT_ERROR = (1 << 2)    # Timeout occurred
    STATUS_PEC_ERROR = (1 << 3)        # PEC mismatch
    STATUS_ARB_LOST = (1 << 4)         # Arbitration lost
    STATUS_NAK_RECEIVED = (1 << 5)     # NAK from slave
    STATUS_SLAVE_ADDRESSED = (1 << 6)  # Own address matched
    STATUS_COMPLETE = (1 << 7)         # Transaction complete
    STATUS_FSM_STATE_MASK = (0xF << 8) # FSM state bits

    # SMBUS_COMMAND bit definitions
    COMMAND_TRANS_TYPE_MASK = 0x0F     # Transaction type (0-9)
    COMMAND_CODE_MASK = 0xFF00         # Command byte
    COMMAND_CODE_SHIFT = 8
    COMMAND_START = (1 << 16)          # Start transaction
    COMMAND_STOP = (1 << 17)           # Generate stop

    # Transaction types
    TRANS_QUICK_CMD = 0       # Quick command
    TRANS_SEND_BYTE = 1       # Send byte
    TRANS_RECV_BYTE = 2       # Receive byte
    TRANS_WRITE_BYTE = 3      # Write byte data
    TRANS_READ_BYTE = 4       # Read byte data
    TRANS_WRITE_WORD = 5      # Write word data
    TRANS_READ_WORD = 6       # Read word data
    TRANS_BLOCK_WRITE = 7     # Block write
    TRANS_BLOCK_READ = 8      # Block read
    TRANS_BLOCK_PROC = 9      # Block process call

    # SMBUS_FIFO_STATUS bit definitions
    FIFO_TX_LEVEL_MASK = 0x003F        # TX FIFO level (0-32)
    FIFO_TX_FULL = (1 << 6)            # TX FIFO full
    FIFO_TX_EMPTY = (1 << 7)           # TX FIFO empty
    FIFO_RX_LEVEL_MASK = 0x3F00        # RX FIFO level (shifted)
    FIFO_RX_LEVEL_SHIFT = 8
    FIFO_RX_FULL = (1 << 14)           # RX FIFO full
    FIFO_RX_EMPTY = (1 << 15)          # RX FIFO empty

    # SMBUS_INT_ENABLE bit definitions
    INT_COMPLETE_EN = (1 << 0)         # Transaction complete
    INT_ERROR_EN = (1 << 1)            # Any error
    INT_TX_THRESH_EN = (1 << 2)        # TX FIFO threshold
    INT_RX_THRESH_EN = (1 << 3)        # RX FIFO threshold
    INT_SLAVE_ADDR_EN = (1 << 4)       # Slave addressed


class SMBusTB(TBBase):
    """
    SMBus Testbench class.

    Provides comprehensive testing infrastructure for the APB SMBus module.
    """

    def __init__(self, dut, **kwargs):
        """
        Initialize SMBus testbench.

        Args:
            dut: DUT (Device Under Test) handle
            **kwargs: Additional arguments for TBBase
        """
        super().__init__(dut)

        self.dut = dut
        self.pclk = dut.pclk
        self.presetn = dut.presetn

        # Components will be initialized in setup_components
        self.apb_master = None
        self.smbus_slave = None
        self.smbus_monitor = None

        # Track transactions
        self.completed_transactions = []
        self.error_events = []

    async def setup_clocks_and_reset(self):
        """Complete initialization - clocks and reset (MANDATORY METHOD)."""
        # Start APB clock (100 MHz = 10ns period)
        await self.start_clock('pclk', freq=10, units='ns')

        # Start SMBus clock (for testing, use same as pclk when CDC_ENABLE=0)
        await self.start_clock('smbus_clk', freq=10, units='ns')

        # Perform reset sequence
        await self.assert_reset()
        await self.wait_clocks('pclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('pclk', 5)

    async def setup_components(self):
        """Initialize APB and SMBus components (call after setup_clocks_and_reset)."""
        self.log.info("Setting up SMBus testbench components")

        try:
            # Create APB Master
            self.apb_master = APBMaster(
                entity=self.dut,
                title='SMBus APB Master',
                prefix='s_apb_',  # Consistent s_apb_* naming
                clock=self.dut.pclk,
                bus_width=32,
                addr_width=12,
                randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
                log=self.log
            )

            # Properly initialize the APB master
            await self.apb_master.reset_bus()
            self.log.info(f"APB Master created and initialized")

            # Create SMBus Slave BFM (to respond to DUT master transactions)
            self.smbus_slave = SMBusSlave(
                entity=self.dut,
                title='SMBus Slave BFM',
                scl_i='smb_scl_o',   # DUT output -> BFM input
                scl_o='smb_scl_i',   # BFM output -> DUT input (stub, we'll use tristate)
                scl_t='smb_scl_t',   # Not used directly
                sda_i='smb_sda_o',   # DUT output -> BFM input
                sda_o='smb_sda_i',   # BFM output -> DUT input
                sda_t='smb_sda_t',   # Not used directly
                slave_addr=0x50,     # Default EEPROM-like address
                memory_size=256,
                log=self.log
            )

            # Create SMBus Monitor
            self.smbus_monitor = SMBusMonitor(
                entity=self.dut,
                title='SMBus Monitor',
                scl_signal='smb_scl_i',
                sda_signal='smb_sda_i',
                clock=self.dut.pclk,
                log=self.log,
                callback=self._on_transaction_complete
            )

        except Exception as e:
            self.log.error(f"Failed to create testbench components: {e}")
            raise

        self.log.info("SMBus testbench components setup complete")

    async def assert_reset(self):
        """Assert reset (MANDATORY METHOD)."""
        self.presetn.value = 0                 # Active-low APB reset
        self.dut.smbus_resetn.value = 0        # Active-low SMBus reset

        # Initialize SMBus signals to idle state (both lines high)
        self.dut.smb_scl_i.value = 1
        self.dut.smb_sda_i.value = 1

    async def deassert_reset(self):
        """Deassert reset (MANDATORY METHOD)."""
        self.presetn.value = 1                 # Release active-low APB reset
        self.dut.smbus_resetn.value = 1        # Release active-low SMBus reset

    def _on_transaction_complete(self, packet: SMBusPacket):
        """Callback when transaction is captured by monitor."""
        self.completed_transactions.append(packet)
        self.log.debug(f"Transaction captured: {packet.formatted()}")

    # ========================================================================
    # Register Access Methods
    # ========================================================================

    async def write_register(self, addr: int, data: int) -> APBPacket:
        """Write to SMBus register using APB master."""
        try:
            write_packet = APBPacket(
                pwrite=1,
                paddr=addr,
                pwdata=data,
                pstrb=0xF,
                pprot=0,
                data_width=32,
                addr_width=12,
                strb_width=4
            )

            write_packet.direction = 'WRITE'

            if not hasattr(self.apb_master, 'transmit_coroutine'):
                self.apb_master.transmit_coroutine = None

            await self.apb_master.send(write_packet)

            # Wait for transaction to complete
            timeout = 0
            while timeout < 100:
                await RisingEdge(self.dut.pclk)
                if (self.dut.s_apb_PSEL.value and
                    self.dut.s_apb_PENABLE.value and
                    self.dut.s_apb_PREADY.value):
                    break
                timeout += 1

            await RisingEdge(self.dut.pclk)
            return write_packet

        except Exception as e:
            self.log.error(f"Write register failed: {e}")
            raise

    async def read_register(self, addr: int) -> Tuple[APBPacket, int]:
        """Read from SMBus register using APB master."""
        try:
            read_packet = APBPacket(
                pwrite=0,
                paddr=addr,
                pwdata=0,
                pstrb=0xF,
                pprot=0,
                data_width=32,
                addr_width=12,
                strb_width=4
            )

            read_packet.direction = 'READ'

            if not hasattr(self.apb_master, 'transmit_coroutine'):
                self.apb_master.transmit_coroutine = None

            await self.apb_master.send(read_packet)

            # Wait for transaction to complete
            timeout = 0
            while timeout < 100:
                await RisingEdge(self.dut.pclk)
                if (self.dut.s_apb_PSEL.value and
                    self.dut.s_apb_PENABLE.value and
                    self.dut.s_apb_PREADY.value):
                    break
                timeout += 1

            # Capture read data
            read_data = int(self.dut.s_apb_PRDATA.value)
            read_packet.fields['prdata'] = read_data

            await RisingEdge(self.dut.pclk)
            return read_packet, read_data

        except Exception as e:
            self.log.error(f"Read register failed: {e}")
            raise

    # ========================================================================
    # SMBus Configuration Helpers
    # ========================================================================

    async def enable_master_mode(self, enable: bool = True, use_pec: bool = False,
                                  fast_mode: bool = False):
        """
        Enable SMBus master mode.

        Args:
            enable: True to enable master mode
            use_pec: Enable Packet Error Checking
            fast_mode: Enable 400kHz mode (vs 100kHz)
        """
        control = 0
        if enable:
            control |= SMBusRegisterMap.CONTROL_MASTER_EN
        if use_pec:
            control |= SMBusRegisterMap.CONTROL_PEC_EN
        if fast_mode:
            control |= SMBusRegisterMap.CONTROL_FAST_MODE

        await self.write_register(SMBusRegisterMap.SMBUS_CONTROL, control)

    async def enable_slave_mode(self, enable: bool = True, own_addr: int = 0x50):
        """
        Enable SMBus slave mode.

        Args:
            enable: True to enable slave mode
            own_addr: Own slave address (7-bit)
        """
        control = 0
        if enable:
            control |= SMBusRegisterMap.CONTROL_SLAVE_EN

        await self.write_register(SMBusRegisterMap.SMBUS_CONTROL, control)
        await self.write_register(SMBusRegisterMap.SMBUS_OWN_ADDR, own_addr & 0x7F)

    async def configure_clock(self, clk_div: int = 249):
        """
        Configure SCL clock divider.

        SCL_freq = SYS_CLK / (4 * (CLK_DIV + 1))
        For 100MHz system clock:
          - 100kHz: CLK_DIV = 249
          - 400kHz: CLK_DIV = 62

        Args:
            clk_div: Clock divider value (16-bit)
        """
        await self.write_register(SMBusRegisterMap.SMBUS_CLK_DIV, clk_div & 0xFFFF)

    async def configure_timeout(self, timeout: int = 2500000):
        """
        Configure timeout threshold.

        SMBus requires 25-35ms timeout.
        For 100MHz: 25ms = 2,500,000 cycles

        Args:
            timeout: Timeout counter value (24-bit)
        """
        await self.write_register(SMBusRegisterMap.SMBUS_TIMEOUT, timeout & 0xFFFFFF)

    async def reset_fifos(self):
        """Reset TX and RX FIFOs."""
        _, control = await self.read_register(SMBusRegisterMap.SMBUS_CONTROL)
        await self.write_register(SMBusRegisterMap.SMBUS_CONTROL,
                                   control | SMBusRegisterMap.CONTROL_FIFO_RESET)
        await ClockCycles(self.pclk, 5)
        await self.write_register(SMBusRegisterMap.SMBUS_CONTROL, control)

    # ========================================================================
    # Transaction Methods
    # ========================================================================

    async def start_transaction(self, trans_type: int, slave_addr: int,
                                  command: int = 0, generate_stop: bool = True) -> bool:
        """
        Start an SMBus transaction.

        Args:
            trans_type: Transaction type (TRANS_*)
            slave_addr: Target slave address (7-bit)
            command: Command byte (for byte/word/block transactions)
            generate_stop: Generate STOP at end

        Returns:
            True if transaction started successfully
        """
        # Set slave address
        await self.write_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR, slave_addr & 0x7F)

        # Build command register value
        cmd_val = (trans_type & 0xF) | ((command & 0xFF) << 8)
        cmd_val |= SMBusRegisterMap.COMMAND_START
        if generate_stop:
            cmd_val |= SMBusRegisterMap.COMMAND_STOP

        await self.write_register(SMBusRegisterMap.SMBUS_COMMAND, cmd_val)
        return True

    async def wait_for_complete(self, timeout_cycles: int = 10000) -> bool:
        """
        Wait for transaction to complete.

        Args:
            timeout_cycles: Maximum cycles to wait

        Returns:
            True if completed successfully, False if timeout or error
        """
        for _ in range(timeout_cycles):
            _, status = await self.read_register(SMBusRegisterMap.SMBUS_STATUS)

            if status & SMBusRegisterMap.STATUS_COMPLETE:
                return True

            if status & (SMBusRegisterMap.STATUS_BUS_ERROR |
                        SMBusRegisterMap.STATUS_TIMEOUT_ERROR |
                        SMBusRegisterMap.STATUS_PEC_ERROR |
                        SMBusRegisterMap.STATUS_ARB_LOST |
                        SMBusRegisterMap.STATUS_NAK_RECEIVED):
                self.log.warning(f"Transaction error: status=0x{status:08X}")
                return False

            await RisingEdge(self.pclk)

        self.log.error("Transaction timeout waiting for complete")
        return False

    async def read_status(self) -> Dict[str, bool]:
        """
        Read status register.

        Returns:
            Dictionary with status flags
        """
        _, status = await self.read_register(SMBusRegisterMap.SMBUS_STATUS)

        return {
            'busy': bool(status & SMBusRegisterMap.STATUS_BUSY),
            'bus_error': bool(status & SMBusRegisterMap.STATUS_BUS_ERROR),
            'timeout_error': bool(status & SMBusRegisterMap.STATUS_TIMEOUT_ERROR),
            'pec_error': bool(status & SMBusRegisterMap.STATUS_PEC_ERROR),
            'arb_lost': bool(status & SMBusRegisterMap.STATUS_ARB_LOST),
            'nak_received': bool(status & SMBusRegisterMap.STATUS_NAK_RECEIVED),
            'slave_addressed': bool(status & SMBusRegisterMap.STATUS_SLAVE_ADDRESSED),
            'complete': bool(status & SMBusRegisterMap.STATUS_COMPLETE),
            'fsm_state': (status >> 8) & 0xF
        }

    async def read_fifo_status(self) -> Dict[str, int]:
        """
        Read FIFO status register.

        Returns:
            Dictionary with FIFO status
        """
        _, fifo_status = await self.read_register(SMBusRegisterMap.SMBUS_FIFO_STATUS)

        return {
            'tx_level': fifo_status & SMBusRegisterMap.FIFO_TX_LEVEL_MASK,
            'tx_full': bool(fifo_status & SMBusRegisterMap.FIFO_TX_FULL),
            'tx_empty': bool(fifo_status & SMBusRegisterMap.FIFO_TX_EMPTY),
            'rx_level': (fifo_status >> SMBusRegisterMap.FIFO_RX_LEVEL_SHIFT) & 0x3F,
            'rx_full': bool(fifo_status & SMBusRegisterMap.FIFO_RX_FULL),
            'rx_empty': bool(fifo_status & SMBusRegisterMap.FIFO_RX_EMPTY),
        }

    # ========================================================================
    # Data Access Methods
    # ========================================================================

    async def write_data_byte(self, data: int):
        """Write single byte to data register."""
        await self.write_register(SMBusRegisterMap.SMBUS_DATA, data & 0xFF)

    async def read_data_byte(self) -> int:
        """Read single byte from data register."""
        _, data = await self.read_register(SMBusRegisterMap.SMBUS_DATA)
        return data & 0xFF

    async def write_tx_fifo(self, data: List[int]):
        """
        Write data bytes to TX FIFO.

        Args:
            data: List of bytes to write
        """
        for byte in data:
            await self.write_register(SMBusRegisterMap.SMBUS_TX_FIFO, byte & 0xFF)

    async def read_rx_fifo(self, count: int) -> List[int]:
        """
        Read data bytes from RX FIFO.

        Args:
            count: Number of bytes to read

        Returns:
            List of data bytes
        """
        data = []
        for _ in range(count):
            _, byte = await self.read_register(SMBusRegisterMap.SMBUS_RX_FIFO)
            data.append(byte & 0xFF)
        return data

    async def set_block_count(self, count: int):
        """Set block transfer count."""
        await self.write_register(SMBusRegisterMap.SMBUS_BLOCK_COUNT, count & 0x3F)

    # ========================================================================
    # High-Level Transaction Methods
    # ========================================================================

    async def quick_command(self, slave_addr: int, read: bool = False) -> bool:
        """
        Execute Quick Command transaction.

        Args:
            slave_addr: Target slave address
            read: True for read, False for write

        Returns:
            True if successful
        """
        trans_type = SMBusRegisterMap.TRANS_QUICK_CMD
        if read:
            trans_type |= 0x10  # Set read bit in address

        await self.start_transaction(trans_type, slave_addr)
        return await self.wait_for_complete()

    async def write_byte_data(self, slave_addr: int, command: int, data: int) -> bool:
        """
        Execute Write Byte Data transaction.

        Args:
            slave_addr: Target slave address
            command: Command byte
            data: Data byte to write

        Returns:
            True if successful
        """
        await self.write_data_byte(data)
        await self.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE, slave_addr, command)
        return await self.wait_for_complete()

    async def read_byte_data(self, slave_addr: int, command: int) -> Tuple[bool, int]:
        """
        Execute Read Byte Data transaction.

        Args:
            slave_addr: Target slave address
            command: Command byte

        Returns:
            Tuple of (success, data_byte)
        """
        await self.start_transaction(SMBusRegisterMap.TRANS_READ_BYTE, slave_addr, command)
        success = await self.wait_for_complete()
        if success:
            data = await self.read_data_byte()
            return True, data
        return False, 0

    async def write_word_data(self, slave_addr: int, command: int, data: int) -> bool:
        """
        Execute Write Word Data transaction.

        Args:
            slave_addr: Target slave address
            command: Command byte
            data: 16-bit data word (LSB first)

        Returns:
            True if successful
        """
        # Write low byte and high byte to TX FIFO
        await self.write_tx_fifo([data & 0xFF, (data >> 8) & 0xFF])
        await self.start_transaction(SMBusRegisterMap.TRANS_WRITE_WORD, slave_addr, command)
        return await self.wait_for_complete()

    async def read_word_data(self, slave_addr: int, command: int) -> Tuple[bool, int]:
        """
        Execute Read Word Data transaction.

        Args:
            slave_addr: Target slave address
            command: Command byte

        Returns:
            Tuple of (success, 16-bit_word)
        """
        await self.start_transaction(SMBusRegisterMap.TRANS_READ_WORD, slave_addr, command)
        success = await self.wait_for_complete()
        if success:
            data = await self.read_rx_fifo(2)
            word = data[0] | (data[1] << 8) if len(data) >= 2 else 0
            return True, word
        return False, 0

    async def block_write(self, slave_addr: int, command: int, data: List[int]) -> bool:
        """
        Execute Block Write transaction.

        Args:
            slave_addr: Target slave address
            command: Command byte
            data: List of data bytes (max 32)

        Returns:
            True if successful
        """
        # Limit to 32 bytes
        data = data[:32]

        # Write block count and data to TX FIFO
        await self.set_block_count(len(data))
        await self.write_tx_fifo(data)

        await self.start_transaction(SMBusRegisterMap.TRANS_BLOCK_WRITE, slave_addr, command)
        return await self.wait_for_complete()

    async def block_read(self, slave_addr: int, command: int) -> Tuple[bool, List[int]]:
        """
        Execute Block Read transaction.

        Args:
            slave_addr: Target slave address
            command: Command byte

        Returns:
            Tuple of (success, list of data bytes)
        """
        await self.start_transaction(SMBusRegisterMap.TRANS_BLOCK_READ, slave_addr, command)
        success = await self.wait_for_complete()
        if success:
            # Read byte count first
            _, count_reg = await self.read_register(SMBusRegisterMap.SMBUS_BLOCK_COUNT)
            count = count_reg & 0x3F

            # Read data from RX FIFO
            data = await self.read_rx_fifo(count)
            return True, data
        return False, []

    # ========================================================================
    # Interrupt Control
    # ========================================================================

    async def enable_interrupts(self, complete: bool = False, error: bool = False,
                                 tx_thresh: bool = False, rx_thresh: bool = False,
                                 slave_addr: bool = False):
        """
        Enable interrupt sources.

        Args:
            complete: Enable transaction complete interrupt
            error: Enable error interrupt
            tx_thresh: Enable TX FIFO threshold interrupt
            rx_thresh: Enable RX FIFO threshold interrupt
            slave_addr: Enable slave addressed interrupt
        """
        int_enable = 0
        if complete:
            int_enable |= SMBusRegisterMap.INT_COMPLETE_EN
        if error:
            int_enable |= SMBusRegisterMap.INT_ERROR_EN
        if tx_thresh:
            int_enable |= SMBusRegisterMap.INT_TX_THRESH_EN
        if rx_thresh:
            int_enable |= SMBusRegisterMap.INT_RX_THRESH_EN
        if slave_addr:
            int_enable |= SMBusRegisterMap.INT_SLAVE_ADDR_EN

        await self.write_register(SMBusRegisterMap.SMBUS_INT_ENABLE, int_enable)

    async def clear_interrupts(self, mask: int = 0xFFFFFFFF):
        """Clear interrupt status (write 1 to clear)."""
        await self.write_register(SMBusRegisterMap.SMBUS_INT_STATUS, mask)

    async def read_interrupt_status(self) -> int:
        """Read interrupt status register."""
        _, status = await self.read_register(SMBusRegisterMap.SMBUS_INT_STATUS)
        return status
