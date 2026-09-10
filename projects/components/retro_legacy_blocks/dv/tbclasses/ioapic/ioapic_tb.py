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
    APB Master → apb4_ioapic → IOAPIC Core
                     ↓
                  24 IRQ inputs
                     ↓
                  Interrupt delivery interface
"""

import os

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb.handle import SimHandleBase
from typing import List, Optional, Tuple

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.apb.apb_components import APBMaster
from CocoTBFramework.components.apb.apb_packet import APBPacket
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.amba.amba_random_configs import APB_MASTER_RANDOMIZER_CONFIGS

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
        self.apb4_master = None  # Will be created in setup_components()

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

        Clock periods are read from TEST_APB_CLOCK_PERIOD / TEST_IOAPIC_CLOCK_PERIOD
        (plumbed by the test runner in dv/tests/test_apb4_ioapic.py), same pattern
        as the GPIO TB's TEST_APB_CLOCK_PERIOD/TEST_GPIO_CLOCK_PERIOD.

        Review finding (GitHub #48 qc round_3, item 2): an earlier version of
        this TB started pclk and ioapic_clk both at 10ns from the same sim
        time, so every CDC_ENABLE=1 configuration ran with edge-identical
        clocks - eoi_in/eoi_vector (which have no synchronizer into the
        ioapic_clk domain; they pass combinationally through
        ioapic_config_regs) were exercised as if synchronous, which made the
        CDC arm of the matrix unable to expose a missed/metastable EOI. The
        runner now drives ioapic_clk at a non-unity, non-integer ratio to
        pclk (10ns:7ns) whenever CDC_ENABLE=1, matching gpio_tb.py's
        TEST_GPIO_CLOCK_PERIOD precedent. When CDC_ENABLE=0 the RTL ties the
        core/config-regs clock to pclk internally, so the runner sets
        ioapic_clk to the same period as pclk to match.
        """
        apb_clock_period_ns = int(os.environ.get('TEST_APB_CLOCK_PERIOD', '10'))
        ioapic_clock_period_ns = int(os.environ.get('TEST_IOAPIC_CLOCK_PERIOD', str(apb_clock_period_ns)))

        # Start APB clock
        await self.start_clock('pclk', freq=apb_clock_period_ns, units='ns')

        # Start IOAPIC clock (possibly a different, non-integer-ratio period)
        await self.start_clock('ioapic_clk', freq=ioapic_clock_period_ns, units='ns')

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
            self.apb4_master = APBMaster(
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
            await self.apb4_master.reset_bus()
            self.log.info(f"✓ APB Master created and initialized: {type(self.apb4_master)}")

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
        Write to a direct APB register (IOREGSEL or IOWIN, or any other
        offset in the 4KB window - GitHub #48 review M1 exercises the rest
        of the window directly).

        Args:
            addr: APB address offset (0x00 for IOREGSEL, 0x04 for IOWIN)
            data: Value to write (32-bit)

        Returns:
            APBPacket containing the write transaction. ``.pslverr`` (and
            equivalently ``.fields['pslverr']``) carries the APB slave error
            response sampled by the framework APB master BFM
            (APBMaster._finish_xmit) once the transaction completes - it is
            NOT read by poking ``s_apb_PSLVERR`` here.
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
        await self.apb4_master.send(write_packet)

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

        # GitHub #48 review M1: expose the completed transaction's PSLVERR
        # response as a plain attribute. write_packet is the exact object
        # queued into APBMaster.send() above, and APBMaster._finish_xmit
        # already wrote fields['pslverr'] from s_apb_PSLVERR before the
        # PSEL&&PENABLE&&PREADY handshake this method waited for above
        # completed, so it is settled by this point.
        write_packet.pslverr = write_packet.fields.get('pslverr', 0)
        self.log.debug(
            f"APB Write 0x{addr:03X} = 0x{data:08X} (pslverr={write_packet.pslverr})")

        return write_packet

    async def read_apb_register(self, addr: int) -> Tuple[APBPacket, int]:
        """
        Read from a direct APB register (IOREGSEL or IOWIN, or any other
        offset in the 4KB window - GitHub #48 review M1 exercises the rest
        of the window directly).

        Args:
            addr: APB address offset (0x00 for IOREGSEL, 0x04 for IOWIN)

        Returns:
            Tuple of (APBPacket, read_value). The packet's ``.pslverr``
            (and equivalently ``.fields['pslverr']``) carries the APB slave
            error response sampled by the framework APB master BFM
            (APBMaster._finish_xmit) once the transaction completes - it is
            NOT read by poking ``s_apb_PSLVERR`` here.
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
        await self.apb4_master.send(read_packet)

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

        # GitHub #48 review M1: expose the completed transaction's PSLVERR
        # response as a plain attribute (see write_apb_register for the
        # same-timing rationale - fields['pslverr'] is settled by this
        # point because APBMaster._finish_xmit wrote it before the
        # PSEL&&PENABLE&&PREADY handshake this method waited for above).
        read_packet.pslverr = read_packet.fields.get('pslverr', 0)
        self.log.debug(
            f"APB Read 0x{addr:03X} = 0x{read_data:08X} (pslverr={read_packet.pslverr})")

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
                # The mode says how the receiver must read the destination;
                # capture it with the rest of the payload, before the ack
                # returns the interface to its idle (all-zero) state.
                self._last_int_dest_mode = int(self.dut.irq_out_dest_mode.value)
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

    async def reset_dut(self):
        """
        Perform a full DUT reset and re-initialize inputs to a known idle state.

        The delivery path has no state machine to wedge: it is a one-entry
        valid/ready pipeline stage with a per-pin Remote IRR block, and EOI
        is honoured in any state (see ioapic_core.sv). Even so, the
        ioapic_tests_medium.py suite starts every test from a guaranteed-clean
        DUT rather than relying on drain_pending_interrupts() to recover
        arbitrary IRQ/Remote-IRR state left over from the previous test.

        History: prior to the GitHub #48 fix, delivery was a single global
        FSM whose WAIT_EOI state blocked every IRQ (not just the one
        missing its EOI), which is why this method exists as a hard reset
        rather than a best-effort drain.
        """
        await self.assert_reset()
        await self.wait_clocks('pclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('pclk', 5)

        self.dut.irq_in.value = 0x000000
        self.dut.irq_out_ready.value = 0
        self.dut.eoi_in.value = 0
        self.dut.eoi_vector.value = 0

        await self.wait_clocks('pclk', 2)

        self._last_int_vector = None
        self._last_int_dest = None

        self.log.info("IOAPIC DUT reset (defect-test clean state)")

    async def count_irq_out_handshakes(self, window_cycles: int, ready: int = 1,
                                        vector_filter: Optional[int] = None) -> List[int]:
        """
        Observe irq_out_valid/irq_out_vector for window_cycles pclk cycles while
        driving irq_out_ready to a fixed value, and record the vector delivered
        on every cycle where a valid&ready handshake is seen.

        Unlike wait_for_interrupt(), which captures the FIRST handshake and then
        actively pulses irq_out_ready low again, this keeps ready fixed for the
        whole window and counts every handshake in it - the only way to observe
        a duplicate delivery (GitHub #48 C1) rather than accidentally
        terminating the window right after the first one.

        Args:
            window_cycles: number of pclk cycles to observe
            ready: value to drive on irq_out_ready for the whole window
            vector_filter: if set, only record handshakes for this vector

        Returns:
            List of vectors seen, one entry per handshake (len() == count)
        """
        self.dut.irq_out_ready.value = ready
        handshakes = []
        for _ in range(window_cycles):
            await RisingEdge(self.dut.pclk)
            if self.dut.irq_out_valid.value == 1 and self.dut.irq_out_ready.value == 1:
                vec = self.dut.irq_out_vector.value.integer
                if vector_filter is None or vec == vector_filter:
                    handshakes.append(vec)
        return handshakes

    async def read_remote_irr(self, irq: int) -> int:
        """Read the Remote IRR (bit 14) of a redirection table entry."""
        redir_lo, _ = await self.read_redirection_entry(irq)
        return (redir_lo >> IOAPICRegisterMap.REDIR_REMOTE_IRR_BIT) & 0x1
