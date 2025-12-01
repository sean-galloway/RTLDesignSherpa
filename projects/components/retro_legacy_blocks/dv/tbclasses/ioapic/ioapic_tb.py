# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: IOAPICTB
# Purpose: Testbench class for APB IOAPIC module
#
# Documentation: projects/components/retro_legacy_blocks/rtl/ioapic/README.md
# Subsystem: retro_legacy_blocks/ioapic
#
# Created: 2025-11-16

"""
IOAPIC Testbench Class

Provides testbench infrastructure for validating the APB IOAPIC module.

Features:
- APB master driver for register access
- Indirect register access via IOREGSEL/IOWIN
- IRQ stimulus generation (24 inputs)
- Redirection table configuration
- Interrupt output monitoring
- Edge and level-triggered modes

Architecture:
    APB Master → apb_ioapic → IOAPIC Core
                     ↓
                  24 IRQ inputs
                     ↓
                  Interrupt delivery interface
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb.handle import SimHandleBase
from typing import List, Optional, Tuple

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.apb.apb_components import APBMaster
from CocoTBFramework.components.apb.apb_packet import APBPacket
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.tbclasses.amba.amba_random_configs import APB_MASTER_RANDOMIZER_CONFIGS

# Import project-specific helper
import sys
from pathlib import Path
repo_root = Path(__file__).resolve().parents[6]
sys.path.insert(0, str(repo_root))


class IOAPICRegisterMap:
    """IOAPIC Register address definitions."""

    # Direct APB access registers
    IOREGSEL = 0x00  # Register select (write offset here)
    IOWIN = 0x04     # Register window (data access)

    # Internal register offsets (accessed via IOREGSEL/IOWIN)
    # These are written to IOREGSEL, then data accessed via IOWIN
    OFFSET_IOAPICID = 0x00   # IOAPIC ID
    OFFSET_IOAPICVER = 0x01  # IOAPIC version
    OFFSET_IOAPICARB = 0x02  # IOAPIC arbitration

    # Redirection table base (internal offset)
    OFFSET_IOREDTBL_BASE = 0x10  # First redirection entry

    # Redirection table entry field definitions
    REDIR_VECTOR_MASK = 0xFF           # bits[7:0]
    REDIR_DELIV_MODE_SHIFT = 8         # bits[10:8]
    REDIR_DEST_MODE_BIT = 11           # bit[11]
    REDIR_DELIV_STATUS_BIT = 12        # bit[12] (read-only)
    REDIR_POLARITY_BIT = 13            # bit[13]
    REDIR_REMOTE_IRR_BIT = 14          # bit[14] (read-only)
    REDIR_TRIGGER_MODE_BIT = 15        # bit[15]
    REDIR_MASK_BIT = 16                # bit[16]
    REDIR_DEST_SHIFT = 24              # bits[31:24] in HI register

    # Delivery modes
    DELIV_MODE_FIXED = 0x0
    DELIV_MODE_LOWPRI = 0x1
    DELIV_MODE_SMI = 0x2
    DELIV_MODE_NMI = 0x4
    DELIV_MODE_INIT = 0x5
    DELIV_MODE_EXTINT = 0x7

    @staticmethod
    def get_redirection_offset(irq: int, high: bool = False) -> int:
        """
        Get internal offset for redirection table entry.

        Args:
            irq: IRQ number (0-23)
            high: True for high 32 bits, False for low 32 bits

        Returns:
            Internal offset value to write to IOREGSEL
        """
        if not 0 <= irq < 24:
            raise ValueError(f"IRQ must be 0-23, got {irq}")

        base_offset = IOAPICRegisterMap.OFFSET_IOREDTBL_BASE + (irq * 2)
        return base_offset + (1 if high else 0)


class IOAPICTB(TBBase):
    """
    Testbench class for APB IOAPIC module.

    Provides infrastructure for testing the I/O Advanced Programmable
    Interrupt Controller with APB interface, 24 IRQ inputs, and interrupt
    delivery interface.
    """

    def __init__(self, dut: SimHandleBase):
        """
        Initialize IOAPIC testbench.

        Args:
            dut: DUT instance from CocoTB
        """
        super().__init__(dut)

        self.dut = dut
        self.pclk = dut.pclk
        self.presetn = dut.presetn
        self.num_irqs = 24

        # APB configuration
        self.apb_data_width = 32
        self.apb_addr_width = 12  # 4KB address window
        self.apb_master = None  # Will be created in setup_components()

        # Captured interrupt info (set by wait_for_interrupt)
        self._last_int_vector = None
        self._last_int_dest = None

        self.log.info("IOAPIC testbench initialized")
        self.log.info(f"  Data width: {self.apb_data_width}")
        self.log.info(f"  Addr width: {self.apb_addr_width}")
        self.log.info(f"  IRQ inputs: {self.num_irqs}")

    async def setup_clocks_and_reset(self):
        """
        Setup clocks and perform reset sequence.

        Required by TBBase contract.
        """
        # Start APB clock (100 MHz, 10ns period)
        await self.start_clock('pclk', freq=10, units='ns')

        # Start IOAPIC clock (100 MHz, 10ns period)
        await self.start_clock('ioapic_clk', freq=10, units='ns')

        # Assert reset
        await self.assert_reset()

        # Wait for reset propagation
        await self.wait_clocks('pclk', 10)

        # Deassert reset
        await self.deassert_reset()

        # Wait for design to stabilize
        await self.wait_clocks('pclk', 5)

        self.log.info("Clock and reset setup complete")

    async def assert_reset(self):
        """
        Assert reset signal (active-low).

        Required by TBBase contract.
        """
        self.dut.presetn.value = 0
        self.dut.ioapic_resetn.value = 0
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """
        Deassert reset signal.

        Required by TBBase contract.
        """
        self.dut.presetn.value = 1
        self.dut.ioapic_resetn.value = 1
        self.log.info("Reset deasserted")

    async def setup_components(self):
        """
        Setup and initialize components after reset.

        This is called after reset to initialize the design to a known state.
        """
        self.log.info("Setting up IOAPIC testbench components")

        try:
            # Create APB Master - pattern from RTC/PIT/HPET
            self.apb_master = APBMaster(
                entity=self.dut,
                title="IOAPIC APB Master",
                prefix="s_apb",  # Constructs s_apb_PADDR, s_apb_PWRITE, etc.
                clock=self.dut.pclk,
                bus_width=self.apb_data_width,
                addr_width=self.apb_addr_width,
                randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
                log=self.log
            )

            # Initialize the APB master (starts transmit coroutine)
            await self.apb_master.reset_bus()
            self.log.info(f"✓ APB Master created and initialized: {type(self.apb_master)}")

        except Exception as e:
            self.log.error(f"Failed to create APB Master: {e}")
            raise

        # Initialize IRQ inputs to inactive (0 for edge-triggered, high/low depends on polarity)
        self.dut.irq_in.value = 0x000000

        # Initialize interrupt delivery NOT ready (TB controls delivery timing)
        # This prevents the IOAPIC from completing delivery before TB is ready to observe it
        self.dut.irq_out_ready.value = 0

        # Initialize EOI input
        self.dut.eoi_in.value = 0

        # Wait for initialization to complete
        await self.wait_clocks('pclk', 2)

        self.log.info("Components setup complete")

    async def write_apb_register(self, addr: int, data: int) -> APBPacket:
        """
        Write to a direct APB register (IOREGSEL or IOWIN).

        Args:
            addr: APB address offset (0x00 for IOREGSEL, 0x04 for IOWIN)
            data: Value to write (32-bit)

        Returns:
            APBPacket containing the write transaction
        """
        write_packet = APBPacket(
            pwrite=1,
            paddr=addr,
            pwdata=data,
            pstrb=0xF,
            pprot=0,
            data_width=self.apb_data_width,
            addr_width=self.apb_addr_width,
            strb_width=4
        )
        write_packet.direction = 'WRITE'

        # Send the packet
        await self.apb_master.send(write_packet)

        # Wait for transaction to complete (PSEL & PENABLE & PREADY)
        timeout = 0
        while timeout < 100:
            await RisingEdge(self.dut.pclk)
            if (self.dut.s_apb_PSEL.value and
                self.dut.s_apb_PENABLE.value and
                self.dut.s_apb_PREADY.value):
                break
            timeout += 1

        if timeout >= 100:
            self.log.error(f"APB write timeout at address 0x{addr:03X}")

        await RisingEdge(self.dut.pclk)
        self.log.debug(f"APB Write 0x{addr:03X} = 0x{data:08X}")

        return write_packet

    async def read_apb_register(self, addr: int) -> Tuple[APBPacket, int]:
        """
        Read from a direct APB register (IOREGSEL or IOWIN).

        Args:
            addr: APB address offset (0x00 for IOREGSEL, 0x04 for IOWIN)

        Returns:
            Tuple of (APBPacket, read_value)
        """
        read_packet = APBPacket(
            pwrite=0,
            paddr=addr,
            pwdata=0,
            pstrb=0xF,
            pprot=0,
            data_width=self.apb_data_width,
            addr_width=self.apb_addr_width,
            strb_width=4
        )
        read_packet.direction = 'READ'

        # Send the packet
        await self.apb_master.send(read_packet)

        # Wait for transaction to complete and capture read data
        timeout = 0
        read_data = 0
        while timeout < 100:
            await RisingEdge(self.dut.pclk)
            if (self.dut.s_apb_PSEL.value and
                self.dut.s_apb_PENABLE.value and
                self.dut.s_apb_PREADY.value):
                read_data = self.dut.s_apb_PRDATA.value.integer
                break
            timeout += 1

        if timeout >= 100:
            self.log.error(f"APB read timeout at address 0x{addr:03X}")

        await RisingEdge(self.dut.pclk)
        read_packet.prdata = read_data
        self.log.debug(f"APB Read 0x{addr:03X} = 0x{read_data:08X}")

        return read_packet, read_data

    async def write_ioapic_register(self, offset: int, data: int):
        """
        Write to an IOAPIC internal register via IOREGSEL/IOWIN.

        This is the indirect access method:
        1. Write offset to IOREGSEL (0x00)
        2. Write data to IOWIN (0x04)

        Args:
            offset: Internal register offset (0x00-0x3F)
            data: Value to write (32-bit)
        """
        # Step 1: Select register by writing offset to IOREGSEL
        await self.write_apb_register(IOAPICRegisterMap.IOREGSEL, offset)

        # Step 2: Write data to IOWIN
        await self.write_apb_register(IOAPICRegisterMap.IOWIN, data)

        self.log.info(f"IOAPIC Write [0x{offset:02X}] = 0x{data:08X}")

    async def read_ioapic_register(self, offset: int) -> int:
        """
        Read from an IOAPIC internal register via IOREGSEL/IOWIN.

        This is the indirect access method:
        1. Write offset to IOREGSEL (0x00)
        2. Read data from IOWIN (0x04)

        Args:
            offset: Internal register offset (0x00-0x3F)

        Returns:
            Register value (32-bit)
        """
        # Step 1: Select register by writing offset to IOREGSEL
        await self.write_apb_register(IOAPICRegisterMap.IOREGSEL, offset)

        # Step 2: Read data from IOWIN
        _, data = await self.read_apb_register(IOAPICRegisterMap.IOWIN)

        self.log.info(f"IOAPIC Read [0x{offset:02X}] = 0x{data:08X}")
        return data

    async def write_redirection_entry(self, irq: int, vector: int,
                                     dest: int = 0,
                                     delivery_mode: int = 0,
                                     dest_mode: int = 0,
                                     polarity: int = 0,
                                     trigger_mode: int = 0,
                                     mask: int = 0):
        """
        Configure a redirection table entry for an IRQ.

        Args:
            irq: IRQ number (0-23)
            vector: Interrupt vector (0x00-0xFF)
            dest: Destination CPU (0-255)
            delivery_mode: Delivery mode (0=Fixed, 1=LowestPri, etc.)
            dest_mode: Destination mode (0=Physical, 1=Logical)
            polarity: Interrupt polarity (0=Active High, 1=Active Low)
            trigger_mode: Trigger mode (0=Edge, 1=Level)
            mask: Mask bit (0=Enabled, 1=Masked)
        """
        # Build low 32 bits
        redir_lo = (
            (vector & 0xFF) |
            ((delivery_mode & 0x7) << 8) |
            ((dest_mode & 0x1) << 11) |
            ((polarity & 0x1) << 13) |
            ((trigger_mode & 0x1) << 15) |
            ((mask & 0x1) << 16)
        )

        # Build high 32 bits
        redir_hi = ((dest & 0xFF) << 24)

        # Write low 32 bits
        offset_lo = IOAPICRegisterMap.get_redirection_offset(irq, high=False)
        await self.write_ioapic_register(offset_lo, redir_lo)

        # Write high 32 bits
        offset_hi = IOAPICRegisterMap.get_redirection_offset(irq, high=True)
        await self.write_ioapic_register(offset_hi, redir_hi)

        self.log.info(f"Configured IRQ{irq}: vec=0x{vector:02X}, dest={dest}, "
                     f"mode={'level' if trigger_mode else 'edge'}, "
                     f"{'masked' if mask else 'enabled'}")

    async def read_redirection_entry(self, irq: int) -> Tuple[int, int]:
        """
        Read a redirection table entry.

        Args:
            irq: IRQ number (0-23)

        Returns:
            Tuple of (redir_lo, redir_hi)
        """
        offset_lo = IOAPICRegisterMap.get_redirection_offset(irq, high=False)
        offset_hi = IOAPICRegisterMap.get_redirection_offset(irq, high=True)

        redir_lo = await self.read_ioapic_register(offset_lo)
        redir_hi = await self.read_ioapic_register(offset_hi)

        return redir_lo, redir_hi

    async def assert_irq(self, irq_num: int):
        """
        Assert (raise) an IRQ input.

        Args:
            irq_num: IRQ number (0-23)
        """
        if not 0 <= irq_num < self.num_irqs:
            raise ValueError(f"IRQ must be 0-{self.num_irqs-1}")

        current = self.dut.irq_in.value.integer
        new_value = current | (1 << irq_num)
        self.dut.irq_in.value = new_value

        self.log.info(f"IRQ{irq_num} asserted (irq_in=0x{new_value:06X})")

    async def deassert_irq(self, irq_num: int):
        """
        Deassert (lower) an IRQ input.

        Args:
            irq_num: IRQ number (0-23)
        """
        if not 0 <= irq_num < self.num_irqs:
            raise ValueError(f"IRQ must be 0-{self.num_irqs-1}")

        current = self.dut.irq_in.value.integer
        new_value = current & ~(1 << irq_num)
        self.dut.irq_in.value = new_value

        self.log.info(f"IRQ{irq_num} deasserted (irq_in=0x{new_value:06X})")

    async def pulse_irq(self, irq_num: int, pulse_cycles: int = 5):
        """
        Generate an IRQ pulse (edge-triggered).

        Args:
            irq_num: IRQ number (0-23)
            pulse_cycles: Number of clock cycles for pulse width
        """
        await self.assert_irq(irq_num)
        await self.wait_clocks('pclk', pulse_cycles)
        await self.deassert_irq(irq_num)

        self.log.info(f"IRQ{irq_num} pulsed ({pulse_cycles} cycles)")

    async def wait_for_interrupt(self, timeout_cycles: int = 100) -> bool:
        """
        Wait for interrupt delivery (irq_out_valid assertion).

        Args:
            timeout_cycles: Maximum cycles to wait

        Returns:
            True if interrupt delivered within timeout, False otherwise
        """
        for _ in range(timeout_cycles):
            if self.dut.irq_out_valid.value == 1:
                self.log.info("Interrupt delivery asserted (irq_out_valid=1)")
                # Capture interrupt info BEFORE acknowledging
                self._last_int_vector = self.dut.irq_out_vector.value.integer
                self._last_int_dest = self.dut.irq_out_dest.value.integer
                # Acknowledge the interrupt to complete delivery
                self.dut.irq_out_ready.value = 1
                await self.wait_clocks('pclk', 1)
                self.dut.irq_out_ready.value = 0
                return True
            await self.wait_clocks('pclk', 1)

        self.log.warning(f"Interrupt delivery not asserted within {timeout_cycles} cycles")
        return False

    async def send_eoi(self, vector: int):
        """
        Send End-of-Interrupt signal.

        Args:
            vector: Interrupt vector that was serviced
        """
        self.dut.eoi_in.value = 1
        self.dut.eoi_vector.value = vector
        await self.wait_clocks('pclk', 1)
        self.dut.eoi_in.value = 0
        self.dut.eoi_vector.value = 0

        self.log.info(f"EOI sent for vector 0x{vector:02X}")

    async def get_interrupt_delivery(self) -> Tuple[int, int, int]:
        """
        Get interrupt delivery information.

        If an interrupt was captured by wait_for_interrupt(), returns the captured values.
        Otherwise reads current signal values.

        Returns:
            Tuple of (valid, vector, dest)
        """
        # If we captured interrupt info in wait_for_interrupt, return those values
        if hasattr(self, '_last_int_vector') and self._last_int_vector is not None:
            vector = self._last_int_vector
            dest = self._last_int_dest
            # Clear captured values
            self._last_int_vector = None
            self._last_int_dest = None
            return 1, vector, dest

        # Otherwise read current signal values
        valid = self.dut.irq_out_valid.value.integer
        vector = self.dut.irq_out_vector.value.integer
        dest = self.dut.irq_out_dest.value.integer

        return valid, vector, dest

    async def drain_pending_interrupts(self, max_count: int = 10, timeout_per_int: int = 20) -> int:
        """
        Drain any pending interrupts from previous test operations.

        This acknowledges and sends EOI for any pending interrupts to ensure
        a clean state for subsequent tests.

        Args:
            max_count: Maximum number of interrupts to drain
            timeout_per_int: Cycles to wait for each interrupt

        Returns:
            Number of interrupts drained
        """
        drained = 0
        for _ in range(max_count):
            # Check if there's a pending interrupt
            if self.dut.irq_out_valid.value != 1:
                # Wait a few cycles to see if one appears
                for _ in range(timeout_per_int):
                    if self.dut.irq_out_valid.value == 1:
                        break
                    await self.wait_clocks('pclk', 1)
                else:
                    # No interrupt appeared, we're done
                    break

            if self.dut.irq_out_valid.value == 1:
                # Capture vector for EOI
                vector = self.dut.irq_out_vector.value.integer
                # Acknowledge the interrupt
                self.dut.irq_out_ready.value = 1
                await self.wait_clocks('pclk', 1)
                self.dut.irq_out_ready.value = 0
                # Send EOI to clear any level-triggered interrupts
                await self.send_eoi(vector)
                drained += 1
                self.log.info(f"Drained pending interrupt: vector=0x{vector:02X}")

        if drained > 0:
            self.log.info(f"Drained {drained} pending interrupt(s)")
        return drained
