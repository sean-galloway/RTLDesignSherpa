# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PIC8259TB
# Purpose: Testbench class for APB PIC 8259 module
#
# Documentation: projects/components/retro_legacy_blocks/rtl/pic_8259/README.md
# Subsystem: retro_legacy_blocks/pic_8259
#
# Created: 2025-11-16

"""
PIC 8259 Testbench Class

Provides testbench infrastructure for validating the APB PIC 8259 module.

Features:
- APB master driver for register access
- IRQ stimulus generation
- Register map integration
- Helper methods for PIC configuration
- Interrupt monitoring

Architecture:
    APB Master → apb_pic_8259 → PIC Core
                     ↓
                  8 IRQ inputs
                     ↓
                  INT output
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


class PIC8259RegisterMap:
    """PIC 8259 Register address definitions."""

    # Configuration and initialization registers
    PIC_CONFIG = 0x000  # Global configuration
    PIC_ICW1 = 0x004    # Initialization Command Word 1
    PIC_ICW2 = 0x008    # Initialization Command Word 2 (vector base)
    PIC_ICW3 = 0x00C    # Initialization Command Word 3 (cascade)
    PIC_ICW4 = 0x010    # Initialization Command Word 4 (modes)

    # Operation Command Words
    PIC_OCW1 = 0x014    # Operation Command Word 1 (IMR - Interrupt Mask Register)
    PIC_OCW2 = 0x018    # Operation Command Word 2 (EOI/priority commands)
    PIC_OCW3 = 0x01C    # Operation Command Word 3 (special modes)

    # Status registers (read-only)
    PIC_IRR = 0x020     # Interrupt Request Register
    PIC_ISR = 0x024     # In-Service Register
    PIC_STATUS = 0x028  # Status and diagnostics

    @staticmethod
    def get_register_offset(reg_name: str) -> int:
        """Get register offset by name."""
        return getattr(PIC8259RegisterMap, reg_name)


class PIC8259TB(TBBase):
    """
    Testbench class for APB PIC 8259 module.

    Provides infrastructure for testing the Programmable Interrupt Controller
    with APB interface, IRQ inputs, and interrupt output monitoring.
    """

    def __init__(self, dut: SimHandleBase):
        """
        Initialize PIC 8259 testbench.

        Args:
            dut: DUT instance from CocoTB
        """
        super().__init__(dut)

        self.dut = dut
        self.pclk = dut.pclk
        self.presetn = dut.presetn
        self.num_irqs = 8

        # APB configuration
        self.apb_data_width = 32
        self.apb_addr_width = 12  # 4KB address window
        self.apb_master = None  # Will be created in setup_components()

        self.log.info("PIC 8259 testbench initialized")
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
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """
        Deassert reset signal.

        Required by TBBase contract.
        """
        self.dut.presetn.value = 1
        self.log.info("Reset deasserted")

    async def setup_components(self):
        """
        Setup and initialize components after reset.

        This is called after reset to initialize the design to a known state.
        """
        self.log.info("Setting up PIC 8259 testbench components")

        try:
            # Create APB Master - pattern from RTC/PIT/HPET
            self.apb_master = APBMaster(
                entity=self.dut,
                title="PIC_8259 APB Master",
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

        # Initialize IRQ inputs to inactive (0 for edge-triggered)
        self.dut.irq_in.value = 0x00

        # Wait for initialization to complete
        await self.wait_clocks('pclk', 2)

        self.log.info("Components setup complete")

    async def write_register(self, addr: int, data: int) -> APBPacket:
        """
        Write to a PIC register using APB.

        Args:
            addr: Register address offset
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
        self.log.info(f"Write 0x{addr:03X} = 0x{data:08X}")

        return write_packet

    async def read_register(self, addr: int) -> Tuple[APBPacket, int]:
        """
        Read from a PIC register using APB.

        Args:
            addr: Register address offset

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
        self.log.info(f"Read 0x{addr:03X} = 0x{read_data:08X}")

        return read_packet, read_data

    async def assert_irq(self, irq_num: int):
        """
        Assert (raise) an IRQ input.

        Args:
            irq_num: IRQ number (0-7)
        """
        if not 0 <= irq_num < self.num_irqs:
            raise ValueError(f"IRQ must be 0-{self.num_irqs-1}")

        current = self.dut.irq_in.value.integer
        new_value = current | (1 << irq_num)
        self.dut.irq_in.value = new_value

        self.log.info(f"IRQ{irq_num} asserted (irq_in=0x{new_value:02X})")

    async def deassert_irq(self, irq_num: int):
        """
        Deassert (lower) an IRQ input.

        Args:
            irq_num: IRQ number (0-7)
        """
        if not 0 <= irq_num < self.num_irqs:
            raise ValueError(f"IRQ must be 0-{self.num_irqs-1}")

        current = self.dut.irq_in.value.integer
        new_value = current & ~(1 << irq_num)
        self.dut.irq_in.value = new_value

        self.log.info(f"IRQ{irq_num} deasserted (irq_in=0x{new_value:02X})")

    async def pulse_irq(self, irq_num: int, pulse_cycles: int = 5):
        """
        Generate an IRQ pulse (edge-triggered).

        Args:
            irq_num: IRQ number (0-7)
            pulse_cycles: Number of clock cycles for pulse width
        """
        await self.assert_irq(irq_num)
        await self.wait_clocks('pclk', pulse_cycles)
        await self.deassert_irq(irq_num)

        self.log.info(f"IRQ{irq_num} pulsed ({pulse_cycles} cycles)")

    async def wait_for_int(self, timeout_cycles: int = 100) -> bool:
        """
        Wait for INT output to assert.

        Args:
            timeout_cycles: Maximum cycles to wait

        Returns:
            True if INT asserted within timeout, False otherwise
        """
        for _ in range(timeout_cycles):
            if self.dut.int_out.value == 1:  # Output port is 'int_out' not 'int_output'
                self.log.info("INT output asserted")
                return True
            await self.wait_clocks('pclk', 1)

        self.log.warning(f"INT output did not assert within {timeout_cycles} cycles")
        return False

    async def read_irr(self) -> int:
        """
        Read Interrupt Request Register.

        Returns:
            IRR value (8-bit, each bit represents IRQ0-7)
        """
        _, value = await self.read_register(PIC8259RegisterMap.PIC_IRR)
        return value & 0xFF

    async def read_isr(self) -> int:
        """
        Read In-Service Register.

        Returns:
            ISR value (8-bit, each bit represents IRQ0-7)
        """
        _, value = await self.read_register(PIC8259RegisterMap.PIC_ISR)
        return value & 0xFF

    async def read_imr(self) -> int:
        """
        Read Interrupt Mask Register.

        Returns:
            IMR value (8-bit, 1=masked, 0=enabled)
        """
        _, value = await self.read_register(PIC8259RegisterMap.PIC_OCW1)
        return value & 0xFF

    async def initialize_pic(self, vector_base: int = 0x20,
                           edge_triggered: bool = True,
                           auto_eoi: bool = False):
        """
        Initialize PIC with standard configuration.

        Args:
            vector_base: Interrupt vector base address
            edge_triggered: True for edge, False for level
            auto_eoi: True to enable auto-EOI mode
        """
        self.log.info("Initializing PIC...")
        self.log.info(f"  Vector base: 0x{vector_base:02X}")
        self.log.info(f"  Trigger mode: {'edge' if edge_triggered else 'level'}")
        self.log.info(f"  Auto-EOI: {auto_eoi}")

        # Enable PIC and enter init mode with auto_reset_init
        # auto_reset_init will automatically clear init_mode after ICW4 is written
        await self.write_register(PIC8259RegisterMap.PIC_CONFIG, 0x00000007)  # pic_enable=1, init_mode=1, auto_reset_init=1

        # ICW1: edge/level, single mode, ICW4 needed
        icw1 = 0x10  # ICW1 marker bit
        if edge_triggered:
            icw1 |= 0x00  # LTIM=0 for edge-triggered
        else:
            icw1 |= 0x08  # LTIM=1 for level-triggered
        icw1 |= 0x02  # SNGL=1 (single mode)
        icw1 |= 0x01  # IC4=1 (ICW4 needed)

        await self.write_register(PIC8259RegisterMap.PIC_ICW1, icw1)
        await self.wait_clocks('pclk', 2)

        # ICW2: vector base
        await self.write_register(PIC8259RegisterMap.PIC_ICW2, vector_base)
        await self.wait_clocks('pclk', 2)

        # ICW4: 8086 mode, auto-EOI
        icw4 = 0x01  # UPM=1 (8086/8088 mode)
        if auto_eoi:
            icw4 |= 0x02  # AEOI=1

        await self.write_register(PIC8259RegisterMap.PIC_ICW4, icw4)
        await self.wait_clocks('pclk', 2)

        # Verify initialization complete
        _, status = await self.read_register(PIC8259RegisterMap.PIC_STATUS)
        init_complete = status & 1  # init_complete is bit 0

        if init_complete:
            self.log.info("✓ PIC initialization complete")
        else:
            self.log.error("✗ PIC initialization failed!")

        return init_complete == 1

    async def set_imr(self, mask: int):
        """
        Set Interrupt Mask Register.

        Args:
            mask: Mask value (1=masked/disabled, 0=enabled)
        """
        await self.write_register(PIC8259RegisterMap.PIC_OCW1, mask)
        self.log.info(f"IMR set to 0x{mask:02X}")

    async def send_eoi(self, irq: Optional[int] = None, specific: bool = False):
        """
        Send End-of-Interrupt command.

        Args:
            irq: IRQ number for specific EOI (0-7), None for non-specific
            specific: True for specific EOI, False for non-specific
        """
        if specific and irq is None:
            raise ValueError("Specific EOI requires IRQ number")

        if specific and irq is not None:
            # Specific EOI: eoi_cmd=011, irq_level=irq
            ocw2_value = 0x60 | irq  # 0b01100000 | irq[2:0]
            self.log.info(f"Sending specific EOI for IRQ{irq}")
        else:
            # Non-specific EOI: eoi_cmd=001, irq_level=0
            ocw2_value = 0x20  # 0b00100000
            self.log.info("Sending non-specific EOI")

        await self.write_register(PIC8259RegisterMap.PIC_OCW2, ocw2_value)
        await self.wait_clocks('pclk', 2)
