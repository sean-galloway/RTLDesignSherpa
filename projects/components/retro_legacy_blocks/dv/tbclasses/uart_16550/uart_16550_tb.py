# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: UART16550RegisterMap, UART16550TB
# Purpose: UART 16550 Testbench with APB access and UART BFM integration
#
# Documentation: projects/components/retro_legacy_blocks/rtl/uart_16550/README.md
# Subsystem: retro_legacy_blocks/uart_16550
#
# Created: 2025-11-30
# Updated: 2025-11-30 - Changed to 32-bit data width, s_apb_* naming

"""
UART 16550 Testbench

Comprehensive testbench for the APB UART 16550 module providing:
- APB register access for configuration
- UART Master (TX) for sending data to DUT
- UART Monitor for capturing DUT output
- Loopback mode testing
- Baud rate configuration
- Modem control signal testing
- Interrupt verification

Features:
- APB register access
- UART TX/RX via BFM
- Interrupt monitoring
- Modem signal simulation
"""

import os
import random
import asyncio
from typing import Dict, List, Optional, Tuple

import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, Timer, FallingEdge, ClockCycles
from cocotb.clock import Clock

from CocoTBFramework.components.apb.apb_packet import APBPacket
from CocoTBFramework.components.apb.apb_components import APBMaster
from CocoTBFramework.components.uart.uart_components import UARTMaster, UARTMonitor, UARTSlave
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.amba.amba_random_configs import APB_MASTER_RANDOMIZER_CONFIGS


class UART16550RegisterMap:
    """UART 16550 Register address definitions (PeakRDL generated, 32-bit aligned).

    NOTE: These addresses match the PeakRDL-generated register file.
    Unlike traditional NS16550, IIR and FCR have separate addresses.
    All registers are 32-bit aligned (4-byte spacing).
    """

    # Data Register (TX/RX)
    UART_DATA = 0x000           # TX data (write), RX data (read)

    # Interrupt Enable Register
    UART_IER = 0x004            # Interrupt enables

    # Interrupt Identification (read-only)
    UART_IIR = 0x008            # Interrupt ID (read)

    # FIFO Control Register (write-only)
    UART_FCR = 0x00C            # FIFO control (separate from IIR in PeakRDL)

    # Line Control Register
    UART_LCR = 0x010            # Line control (word length, stop bits, parity)

    # Modem Control Register
    UART_MCR = 0x014            # Modem control (DTR, RTS, loopback)

    # Line Status Register
    UART_LSR = 0x018            # Line status (data ready, errors)

    # Modem Status Register
    UART_MSR = 0x01C            # Modem status (CTS, DSR, RI, DCD)

    # Scratch Register
    UART_SCR = 0x020            # Scratch (general purpose)

    # Divisor Latch Registers (fixed addresses, no DLAB bit needed)
    UART_DLL = 0x024            # Divisor Latch Low
    UART_DLM = 0x028            # Divisor Latch High

    # IER bit definitions
    IER_RX_DATA_AVAIL   = (1 << 0)  # Enable RX data available interrupt
    IER_TX_HOLD_EMPTY   = (1 << 1)  # Enable TX holding empty interrupt
    IER_RX_LINE_STATUS  = (1 << 2)  # Enable RX line status interrupt
    IER_MODEM_STATUS    = (1 << 3)  # Enable modem status interrupt

    # IIR bit definitions
    IIR_INT_NOT_PENDING = (1 << 0)  # 0=interrupt pending, 1=no interrupt
    IIR_INT_ID_MASK     = 0x06      # Interrupt ID bits [2:1]
    IIR_TIMEOUT_PENDING = (1 << 3)  # Character timeout pending
    IIR_FIFO_STATUS     = 0xC0      # FIFO status bits [7:6]

    # FCR bit definitions
    FCR_FIFO_ENABLE     = (1 << 0)  # Enable FIFOs
    FCR_RX_FIFO_RESET   = (1 << 1)  # Reset RX FIFO
    FCR_TX_FIFO_RESET   = (1 << 2)  # Reset TX FIFO
    FCR_RX_TRIGGER_1    = 0x00      # RX trigger at 1 byte
    FCR_RX_TRIGGER_4    = 0x40      # RX trigger at 4 bytes
    FCR_RX_TRIGGER_8    = 0x80      # RX trigger at 8 bytes
    FCR_RX_TRIGGER_14   = 0xC0      # RX trigger at 14 bytes

    # LCR bit definitions
    LCR_WORD_5BIT       = 0x00      # 5-bit word
    LCR_WORD_6BIT       = 0x01      # 6-bit word
    LCR_WORD_7BIT       = 0x02      # 7-bit word
    LCR_WORD_8BIT       = 0x03      # 8-bit word
    LCR_STOP_1          = 0x00      # 1 stop bit
    LCR_STOP_2          = 0x04      # 2 stop bits (1.5 for 5-bit)
    LCR_PARITY_ENABLE   = (1 << 3)  # Enable parity
    LCR_EVEN_PARITY     = (1 << 4)  # Even parity (if enabled)
    LCR_STICK_PARITY    = (1 << 5)  # Stick parity
    LCR_SET_BREAK       = (1 << 6)  # Set break
    LCR_DLAB            = (1 << 7)  # Divisor Latch Access Bit

    # MCR bit definitions
    MCR_DTR             = (1 << 0)  # Data Terminal Ready
    MCR_RTS             = (1 << 1)  # Request To Send
    MCR_OUT1            = (1 << 2)  # OUT1 signal
    MCR_OUT2            = (1 << 3)  # OUT2 signal (gates IRQ)
    MCR_LOOPBACK        = (1 << 4)  # Loopback mode

    # LSR bit definitions
    LSR_DATA_READY      = (1 << 0)  # Data ready
    LSR_OVERRUN_ERROR   = (1 << 1)  # Overrun error
    LSR_PARITY_ERROR    = (1 << 2)  # Parity error
    LSR_FRAMING_ERROR   = (1 << 3)  # Framing error
    LSR_BREAK_INT       = (1 << 4)  # Break interrupt
    LSR_TX_HOLD_EMPTY   = (1 << 5)  # TX holding register empty
    LSR_TX_EMPTY        = (1 << 6)  # TX empty (shift reg empty)
    LSR_RX_FIFO_ERROR   = (1 << 7)  # Error in RX FIFO

    # MSR bit definitions
    MSR_DELTA_CTS       = (1 << 0)  # Delta CTS
    MSR_DELTA_DSR       = (1 << 1)  # Delta DSR
    MSR_TRAILING_RI     = (1 << 2)  # Trailing edge RI
    MSR_DELTA_DCD       = (1 << 3)  # Delta DCD
    MSR_CTS             = (1 << 4)  # CTS state
    MSR_DSR             = (1 << 5)  # DSR state
    MSR_RI              = (1 << 6)  # RI state
    MSR_DCD             = (1 << 7)  # DCD state


class UART16550TB(TBBase):
    """
    UART 16550 Testbench class.

    Provides comprehensive testing infrastructure for the APB UART 16550 module.
    """

    def __init__(self, dut, **kwargs):
        """
        Initialize UART 16550 testbench.

        Args:
            dut: DUT (Device Under Test) handle
            **kwargs: Additional arguments for TBBase
        """
        super().__init__(dut)

        self.dut = dut
        self.pclk = dut.pclk
        self.presetn = dut.presetn

        # Default baud rate settings (100 MHz clock, 115200 baud)
        # Divisor = 100_000_000 / (16 * 115200) = 54.25 -> 54
        self.clock_freq = 100_000_000  # 100 MHz
        self.baud_rate = 115200
        self.clks_per_bit = self.clock_freq // self.baud_rate  # ~868 cycles at 100MHz

        # Components will be initialized in setup_clocks_and_reset
        self.apb_master = None
        self.uart_tx_master = None    # Sends data TO DUT RX
        self.uart_rx_monitor = None   # Monitors DUT TX output
        self.uart_slave = None        # Full slave (optional)

        # Test tracking
        self.tx_packets = []
        self.rx_packets = []

    async def setup_clocks_and_reset(self):
        """Complete initialization - clocks and reset (MANDATORY METHOD)."""
        # Start APB clock (100 MHz = 10ns period)
        await self.start_clock('pclk', freq=10, units='ns')

        # For CDC mode, start UART clock
        if hasattr(self.dut, 'uart_clk'):
            await self.start_clock('uart_clk', freq=10, units='ns')

        # Initialize UART RX input to idle (high)
        self.dut.uart_rx.value = 1

        # Initialize modem inputs (active low, so set high for inactive)
        self.dut.cts_n.value = 1
        self.dut.dsr_n.value = 1
        self.dut.ri_n.value = 1
        self.dut.dcd_n.value = 1

        # Perform reset sequence
        await self.assert_reset()
        await self.wait_clocks('pclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('pclk', 5)

    async def setup_components(self):
        """Initialize APB and UART components (call after setup_clocks_and_reset)."""
        self.log.info("Setting up UART 16550 testbench components")

        try:
            # Create APB Master
            self.apb_master = APBMaster(
                entity=self.dut,
                title='UART APB Master',
                prefix='s_apb_',  # Consistent s_apb_* naming
                clock=self.dut.pclk,
                bus_width=32,
                addr_width=12,
                randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
                log=self.log
            )

            # Properly initialize the APB master
            await self.apb_master.reset_bus()
            self.log.info(f"APB Master created and initialized: {type(self.apb_master)}")

            # Create UART Master (sends data TO DUT's RX pin)
            self.uart_tx_master = UARTMaster(
                entity=self.dut,
                title='UART TX Master',
                signal_name='uart_rx',  # We drive DUT's RX input
                clock=self.dut.pclk,
                clks_per_bit=self.clks_per_bit,
                log=self.log
            )
            self.log.info(f"UART TX Master created (clks_per_bit={self.clks_per_bit})")

            # Create UART Monitor (monitors DUT's TX output)
            self.uart_rx_monitor = UARTMonitor(
                entity=self.dut,
                title='UART RX Monitor',
                signal_name='uart_tx',  # We monitor DUT's TX output
                clock=self.dut.pclk,
                clks_per_bit=self.clks_per_bit,
                direction='RX',
                log=self.log
            )
            self.log.info(f"UART RX Monitor created (clks_per_bit={self.clks_per_bit})")

        except Exception as e:
            self.log.error(f"Failed to create components: {e}")
            raise

        self.log.info("UART 16550 testbench components setup complete")

    async def assert_reset(self):
        """Assert reset (MANDATORY METHOD)."""
        self.presetn.value = 0           # Active-low APB reset
        if hasattr(self.dut, 'uart_rstn'):
            self.dut.uart_rstn.value = 0 # Active-low UART reset for CDC mode

    async def deassert_reset(self):
        """Deassert reset (MANDATORY METHOD)."""
        self.presetn.value = 1           # Release active-low APB reset
        if hasattr(self.dut, 'uart_rstn'):
            self.dut.uart_rstn.value = 1 # Release active-low UART reset

    # ========================================================================
    # Register Access Methods
    # ========================================================================

    async def write_register(self, addr: int, data: int) -> APBPacket:
        """Write to UART register using correct APB master API (32-bit)."""
        try:
            # Create APB packet
            write_packet = APBPacket(
                pwrite=1,
                paddr=addr,
                pwdata=data,
                pstrb=0xF,  # 32-bit access
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
        """Read from UART register using correct APB master API (32-bit)."""
        try:
            # Create APB packet
            read_packet = APBPacket(
                pwrite=0,
                paddr=addr,
                pwdata=0,
                pstrb=0xF,  # 32-bit access
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
    # UART Configuration Helpers
    # ========================================================================

    async def set_baud_divisor(self, divisor: int):
        """
        Set baud rate divisor.

        Args:
            divisor: 16-bit divisor value (0x0001-0xFFFF)
        """
        await self.write_register(UART16550RegisterMap.UART_DLL, divisor & 0xFF)
        await self.write_register(UART16550RegisterMap.UART_DLM, (divisor >> 8) & 0xFF)
        self.log.info(f"Set baud divisor: {divisor} (0x{divisor:04X})")

    async def configure_line(self, word_length: int = 8, stop_bits: int = 1,
                             parity: str = 'none'):
        """
        Configure line control.

        Args:
            word_length: 5, 6, 7, or 8 bits
            stop_bits: 1 or 2
            parity: 'none', 'odd', 'even', 'mark', 'space'
        """
        lcr = 0

        # Word length
        if word_length == 5:
            lcr |= UART16550RegisterMap.LCR_WORD_5BIT
        elif word_length == 6:
            lcr |= UART16550RegisterMap.LCR_WORD_6BIT
        elif word_length == 7:
            lcr |= UART16550RegisterMap.LCR_WORD_7BIT
        else:  # 8 (default)
            lcr |= UART16550RegisterMap.LCR_WORD_8BIT

        # Stop bits
        if stop_bits == 2:
            lcr |= UART16550RegisterMap.LCR_STOP_2

        # Parity
        if parity == 'odd':
            lcr |= UART16550RegisterMap.LCR_PARITY_ENABLE
        elif parity == 'even':
            lcr |= UART16550RegisterMap.LCR_PARITY_ENABLE | UART16550RegisterMap.LCR_EVEN_PARITY
        elif parity == 'mark':
            lcr |= UART16550RegisterMap.LCR_PARITY_ENABLE | UART16550RegisterMap.LCR_STICK_PARITY
        elif parity == 'space':
            lcr |= (UART16550RegisterMap.LCR_PARITY_ENABLE |
                    UART16550RegisterMap.LCR_EVEN_PARITY |
                    UART16550RegisterMap.LCR_STICK_PARITY)

        await self.write_register(UART16550RegisterMap.UART_LCR, lcr)
        self.log.info(f"Line config: {word_length}N{stop_bits} parity={parity} (LCR=0x{lcr:02X})")

    async def enable_fifos(self, rx_trigger: int = 1):
        """
        Enable FIFOs with optional RX trigger level.

        Args:
            rx_trigger: RX FIFO trigger level (1, 4, 8, or 14)
        """
        fcr = UART16550RegisterMap.FCR_FIFO_ENABLE

        if rx_trigger == 4:
            fcr |= UART16550RegisterMap.FCR_RX_TRIGGER_4
        elif rx_trigger == 8:
            fcr |= UART16550RegisterMap.FCR_RX_TRIGGER_8
        elif rx_trigger == 14:
            fcr |= UART16550RegisterMap.FCR_RX_TRIGGER_14
        # else: trigger at 1 (default)

        await self.write_register(UART16550RegisterMap.UART_FCR, fcr)
        self.log.info(f"FIFOs enabled, RX trigger={rx_trigger}")

    async def reset_fifos(self):
        """Reset both TX and RX FIFOs."""
        fcr = (UART16550RegisterMap.FCR_FIFO_ENABLE |
               UART16550RegisterMap.FCR_RX_FIFO_RESET |
               UART16550RegisterMap.FCR_TX_FIFO_RESET)
        await self.write_register(UART16550RegisterMap.UART_FCR, fcr)
        self.log.info("FIFOs reset")

    async def enable_loopback(self, enable: bool = True):
        """
        Enable/disable loopback mode.

        Args:
            enable: True to enable loopback
        """
        _, mcr = await self.read_register(UART16550RegisterMap.UART_MCR)
        if enable:
            mcr |= UART16550RegisterMap.MCR_LOOPBACK
        else:
            mcr &= ~UART16550RegisterMap.MCR_LOOPBACK
        await self.write_register(UART16550RegisterMap.UART_MCR, mcr)
        self.log.info(f"Loopback mode: {'enabled' if enable else 'disabled'}")

    async def enable_irq(self, rx_data: bool = False, tx_empty: bool = False,
                        line_status: bool = False, modem_status: bool = False):
        """
        Enable interrupt sources.

        Args:
            rx_data: Enable RX data available interrupt
            tx_empty: Enable TX holding empty interrupt
            line_status: Enable RX line status interrupt
            modem_status: Enable modem status interrupt
        """
        ier = 0
        if rx_data:
            ier |= UART16550RegisterMap.IER_RX_DATA_AVAIL
        if tx_empty:
            ier |= UART16550RegisterMap.IER_TX_HOLD_EMPTY
        if line_status:
            ier |= UART16550RegisterMap.IER_RX_LINE_STATUS
        if modem_status:
            ier |= UART16550RegisterMap.IER_MODEM_STATUS
        await self.write_register(UART16550RegisterMap.UART_IER, ier)

        # Also need to enable OUT2 to gate IRQ
        _, mcr = await self.read_register(UART16550RegisterMap.UART_MCR)
        mcr |= UART16550RegisterMap.MCR_OUT2
        await self.write_register(UART16550RegisterMap.UART_MCR, mcr)

        self.log.info(f"Interrupts enabled: IER=0x{ier:02X}")

    async def set_modem_control(self, dtr: bool = False, rts: bool = False,
                                out1: bool = False, out2: bool = False,
                                loopback: bool = None):
        """
        Set modem control signals.

        Args:
            dtr: Data Terminal Ready
            rts: Request To Send
            out1: OUT1 signal
            out2: OUT2 signal (gates IRQ)
            loopback: Loopback mode (None=preserve existing, True/False=set)
        """
        # Read current MCR to preserve loopback bit if not specified
        if loopback is None:
            _, current_mcr = await self.read_register(UART16550RegisterMap.UART_MCR)
            loopback = bool(current_mcr & UART16550RegisterMap.MCR_LOOPBACK)

        mcr = 0
        if dtr:
            mcr |= UART16550RegisterMap.MCR_DTR
        if rts:
            mcr |= UART16550RegisterMap.MCR_RTS
        if out1:
            mcr |= UART16550RegisterMap.MCR_OUT1
        if out2:
            mcr |= UART16550RegisterMap.MCR_OUT2
        if loopback:
            mcr |= UART16550RegisterMap.MCR_LOOPBACK
        await self.write_register(UART16550RegisterMap.UART_MCR, mcr)
        self.log.info(f"Modem control: MCR=0x{mcr:02X}")

    # ========================================================================
    # TX/RX Operations
    # ========================================================================

    async def tx_byte(self, data: int):
        """
        Transmit a byte via THR (TX Holding Register).

        Args:
            data: Byte to transmit (0-255)
        """
        # Wait for TX holding register to be empty
        for _ in range(1000):
            _, lsr = await self.read_register(UART16550RegisterMap.UART_LSR)
            if lsr & UART16550RegisterMap.LSR_TX_HOLD_EMPTY:
                break
            await ClockCycles(self.pclk, 10)

        await self.write_register(UART16550RegisterMap.UART_DATA, data)
        self.log.debug(f"TX byte: 0x{data:02X}")

    async def tx_bytes(self, data_list: List[int]):
        """
        Transmit multiple bytes.

        Args:
            data_list: List of bytes to transmit
        """
        for byte_val in data_list:
            await self.tx_byte(byte_val)

    async def tx_string(self, string: str):
        """
        Transmit a string.

        Args:
            string: String to transmit
        """
        await self.tx_bytes([ord(c) for c in string])

    async def rx_byte(self, timeout_cycles: int = 10000) -> Optional[int]:
        """
        Receive a byte from RBR (RX Buffer Register).

        Args:
            timeout_cycles: Maximum clock cycles to wait

        Returns:
            Received byte or None if timeout
        """
        for _ in range(timeout_cycles // 10):
            _, lsr = await self.read_register(UART16550RegisterMap.UART_LSR)
            if lsr & UART16550RegisterMap.LSR_DATA_READY:
                # Debug: print FIFO state BEFORE the read
                try:
                    core = self.dut.u_uart_config_regs.u_uart_core
                    rd_ptr = int(core.r_rx_rd_ptr.value)
                    wr_ptr = int(core.r_rx_wr_ptr.value)
                    rx_data_sig = int(core.rx_data.value)
                    rx_shift = int(core.r_rx_shift.value)
                    rx_state = int(core.r_rx_state.value)
                    self.log.info(f"FIFO STATE PRE-READ: rd_ptr={rd_ptr}, wr_ptr={wr_ptr}, rx_data=0x{rx_data_sig:02X}, rx_shift=0x{rx_shift:02X}, rx_state={rx_state}")
                except Exception as e:
                    self.log.warning(f"Could not read FIFO state: {e}")

                _, data = await self.read_register(UART16550RegisterMap.UART_DATA)
                # RX data is in bits [15:8] of UART_DATA register
                rx_byte = (data >> 8) & 0xFF
                tx_byte = data & 0xFF
                self.log.info(f"RX raw data=0x{data:04X}, rx_byte=0x{rx_byte:02X}, tx_byte=0x{tx_byte:02X}")

                # Debug: print FIFO state AFTER the read
                try:
                    core = self.dut.u_uart_config_regs.u_uart_core
                    rd_ptr = int(core.r_rx_rd_ptr.value)
                    wr_ptr = int(core.r_rx_wr_ptr.value)
                    self.log.info(f"FIFO STATE POST-READ: rd_ptr={rd_ptr}, wr_ptr={wr_ptr}")
                except Exception as e:
                    self.log.warning(f"Could not read FIFO state: {e}")

                return rx_byte
            await ClockCycles(self.pclk, 10)
        return None

    async def rx_bytes(self, count: int, timeout_cycles: int = 100000) -> List[int]:
        """
        Receive multiple bytes.

        Args:
            count: Number of bytes to receive
            timeout_cycles: Timeout per byte

        Returns:
            List of received bytes
        """
        received = []
        for _ in range(count):
            byte_val = await self.rx_byte(timeout_cycles)
            if byte_val is None:
                break
            received.append(byte_val)
        return received

    # ========================================================================
    # UART BFM Operations (External TX/RX)
    # ========================================================================

    async def send_to_dut(self, data: int):
        """
        Send a byte TO the DUT's RX via UART master.

        Args:
            data: Byte to send (0-255)
        """
        if self.uart_tx_master:
            packet = await self.uart_tx_master.send(data)
            self.tx_packets.append(packet)
            self.log.debug(f"Sent to DUT RX: 0x{data:02X}")
        else:
            self.log.error("UART TX Master not initialized")

    async def send_bytes_to_dut(self, data_list: List[int]):
        """
        Send multiple bytes to DUT's RX.

        Args:
            data_list: List of bytes to send
        """
        if self.uart_tx_master:
            packets = await self.uart_tx_master.send_bytes(data_list)
            self.tx_packets.extend(packets)

    async def send_string_to_dut(self, string: str):
        """
        Send a string to DUT's RX.

        Args:
            string: String to send
        """
        if self.uart_tx_master:
            packets = await self.uart_tx_master.send_string(string)
            self.tx_packets.extend(packets)

    def get_received_packets(self) -> list:
        """
        Get packets received from DUT's TX.

        Returns:
            List of UARTPacket objects
        """
        if self.uart_rx_monitor:
            packets = list(self.uart_rx_monitor._recvQ)
            return packets
        return []

    def clear_rx_queue(self):
        """Clear the RX monitor queue."""
        if self.uart_rx_monitor:
            self.uart_rx_monitor._recvQ.clear()

    # ========================================================================
    # Status Methods
    # ========================================================================

    async def get_line_status(self) -> int:
        """
        Get line status register.

        Returns:
            LSR value
        """
        _, lsr = await self.read_register(UART16550RegisterMap.UART_LSR)
        return lsr

    async def get_modem_status(self) -> int:
        """
        Get modem status register.

        Returns:
            MSR value
        """
        _, msr = await self.read_register(UART16550RegisterMap.UART_MSR)
        return msr

    async def get_interrupt_id(self) -> int:
        """
        Get interrupt identification register.

        Returns:
            IIR value
        """
        _, iir = await self.read_register(UART16550RegisterMap.UART_IIR)
        return iir

    def get_irq(self) -> bool:
        """
        Get interrupt request state.

        Returns:
            True if IRQ is asserted
        """
        return bool(self.dut.irq.value)

    async def is_tx_empty(self) -> bool:
        """Check if TX is completely empty (shift register too)."""
        _, lsr = await self.read_register(UART16550RegisterMap.UART_LSR)
        return bool(lsr & UART16550RegisterMap.LSR_TX_EMPTY)

    async def is_rx_data_ready(self) -> bool:
        """Check if RX data is available."""
        _, lsr = await self.read_register(UART16550RegisterMap.UART_LSR)
        return bool(lsr & UART16550RegisterMap.LSR_DATA_READY)

    # ========================================================================
    # Modem Signal Simulation
    # ========================================================================

    def set_cts(self, active: bool):
        """Set CTS input (active low signal)."""
        self.dut.cts_n.value = 0 if active else 1

    def set_dsr(self, active: bool):
        """Set DSR input (active low signal)."""
        self.dut.dsr_n.value = 0 if active else 1

    def set_ri(self, active: bool):
        """Set RI input (active low signal)."""
        self.dut.ri_n.value = 0 if active else 1

    def set_dcd(self, active: bool):
        """Set DCD input (active low signal)."""
        self.dut.dcd_n.value = 0 if active else 1

    def get_dtr(self) -> bool:
        """Get DTR output state (active low, returns True if active)."""
        return not bool(self.dut.dtr_n.value)

    def get_rts(self) -> bool:
        """Get RTS output state (active low, returns True if active)."""
        return not bool(self.dut.rts_n.value)

    def get_out1(self) -> bool:
        """Get OUT1 output state (active low, returns True if active)."""
        return not bool(self.dut.out1_n.value)

    def get_out2(self) -> bool:
        """Get OUT2 output state (active low, returns True if active)."""
        return not bool(self.dut.out2_n.value)

    # ========================================================================
    # Test Utilities
    # ========================================================================

    async def wait_for_tx_complete(self, timeout_cycles: int = 100000) -> bool:
        """
        Wait for TX to complete (shift register empty).

        Args:
            timeout_cycles: Maximum cycles to wait

        Returns:
            True if TX completed, False if timeout
        """
        for _ in range(timeout_cycles // 10):
            if await self.is_tx_empty():
                return True
            await ClockCycles(self.pclk, 10)
        return False

    async def wait_for_rx_data(self, timeout_cycles: int = 100000) -> bool:
        """
        Wait for RX data available.

        Args:
            timeout_cycles: Maximum cycles to wait

        Returns:
            True if data available, False if timeout
        """
        for _ in range(timeout_cycles // 10):
            if await self.is_rx_data_ready():
                return True
            await ClockCycles(self.pclk, 10)
        return False

    async def basic_init(self, divisor: int = 54):
        """
        Perform basic UART initialization.

        Args:
            divisor: Baud rate divisor (default 54 for 115200 @ 100MHz)
        """
        # Set baud rate
        await self.set_baud_divisor(divisor)

        # Configure 8N1
        await self.configure_line(word_length=8, stop_bits=1, parity='none')

        # Enable FIFOs
        await self.enable_fifos(rx_trigger=1)

        # Reset FIFOs
        await self.reset_fifos()

        self.log.info("Basic UART initialization complete")
