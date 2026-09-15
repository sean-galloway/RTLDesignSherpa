# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rlb_top_tb
# Purpose: Testbench for rlb_top -- the whole RLB subsystem behind its APB
#          crossbar (light integration smoke tests).
#
# Created: 2026-09-14

"""Testbench for the RLB subsystem top.

NINE CLOCK/RESET PAIRS, all driven at the same period on purpose. This is an
integration smoke test, not a CDC test: every block's CDC arm is already
exercised in its own suite, and running the peripheral clocks at skewed
periods here would buy coverage that exists elsewhere while making a decode
failure harder to read. Note the naming is NOT uniform -- gpio and uart use
`_rstn` where every other block uses `_resetn`.

IDLE VALUES ARE NOT COSMETIC. Active-low inputs are tied INACTIVE (high),
`uart_rx` idles high because a low idle is a break condition, the SMBus lines
idle high because they are open-drain with pull-ups, and
`pm_power_domain_ack` ties high exactly as its port comment instructs. Getting
any of these wrong injects activity that would make an unrelated test fail.
"""

import os
from typing import Dict, Optional, Tuple

from cocotb.triggers import RisingEdge
from cocotb.handle import SimHandleBase

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.apb.apb_components import APBMaster
from CocoTBFramework.components.apb.apb_packet import APBPacket
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.amba.amba_random_configs import APB_MASTER_RANDOMIZER_CONFIGS

import sys
from pathlib import Path
repo_root = Path(__file__).resolve().parents[6]
sys.path.insert(0, str(repo_root))

from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_tb import (
    IOAPICRegisterMap,
)
from projects.components.retro_legacy_blocks.dv.tbclasses.pic_8259.pic_8259_tb import (
    PIC8259RegisterMap,
)


class RLBTopTB(TBBase):
    """Testbench for rlb_top: the nine peripherals behind the APB crossbar."""

    BASE_ADDR = 0xFEC00000
    WINDOW = 0x1000

    # Slave index == PADDR[15:12], per apbx_xbar_rlb_1to10.
    SLAVE_HPET, SLAVE_PIC, SLAVE_PIT, SLAVE_RTC, SLAVE_SMBUS = 0, 1, 2, 3, 4
    SLAVE_PM, SLAVE_IOAPIC, SLAVE_GPIO, SLAVE_UART = 5, 6, 7, 8
    SLAVE_RESERVED = 9

    # Read-safe probe register per window. The UART is probed at its SCRATCH
    # register, NOT offset 0x000: reading 0x000 there pops the RX FIFO.
    PROBE: Dict[str, Tuple[int, int]] = {
        'hpet':   (SLAVE_HPET,   0x000),   # HPET_ID, read-only identity
        'pic':    (SLAVE_PIC,    0x000),   # PIC_CONFIG
        'pit':    (SLAVE_PIT,    0x000),   # PIT_CONFIG
        'rtc':    (SLAVE_RTC,    0x000),   # RTC_CONFIG
        'smbus':  (SLAVE_SMBUS,  0x000),   # SMBUS_CONTROL
        'pm':     (SLAVE_PM,     0x000),   # ACPI_CONTROL
        'ioapic': (SLAVE_IOAPIC, 0x000),   # IOREGSEL
        'gpio':   (SLAVE_GPIO,   0x000),   # GPIO_CONTROL
        'uart':   (SLAVE_UART,   0x020),   # UART_SCR -- see above
    }

    # Isolation sweep targets: ONLY registers whose writable width is
    # confirmed in the RDL, and only the low byte is compared. A mask guessed
    # from a field list I never checked could pass while proving nothing.
    WRITABLE: Dict[str, Tuple[int, int]] = {
        'ioapic': (SLAVE_IOAPIC, 0x000),   # IOREGSEL, 8-bit selector storage
        'uart':   (SLAVE_UART,   0x020),   # UART_SCR, scratch[7:0]
        'gpio':   (SLAVE_GPIO,   0x010),   # GPIO_INT_ENABLE, low byte
    }
    WRITE_MASK: Dict[str, int] = {'ioapic': 0xFF, 'uart': 0xFF, 'gpio': 0xFF}

    CLOCKS = ('pclk', 'hpet_clk', 'pit_clk', 'rtc_clk', 'smbus_clk',
              'pm_clk', 'ioapic_clk', 'gpio_clk', 'uart_clk')
    RESETS = ('presetn', 'hpet_resetn', 'pit_resetn', 'rtc_resetn',
              'smbus_resetn', 'pm_resetn', 'ioapic_resetn',
              'gpio_rstn', 'uart_rstn')

    def __init__(self, dut: SimHandleBase):
        super().__init__(dut)
        self.dut = dut
        self.pclk = dut.pclk
        self.presetn = dut.presetn
        self.apb_data_width = 32
        # 32, not the blocks' 12: rlb_top's PADDR is the full system address.
        self.apb_addr_width = 32
        self.apb4_master = None
        self.log.info("RLB top testbench initialized (9 windows behind the xbar)")

    # ------------------------------------------------------------------
    # Address helpers
    # ------------------------------------------------------------------
    def window_addr(self, slave: int, offset: int) -> int:
        return self.BASE_ADDR + slave * self.WINDOW + offset

    @staticmethod
    def isolation_value(name: str, index: int) -> int:
        """A distinct low byte per window, so an alias shows as a collision."""
        return (0xA1 + index * 0x11) & 0xFF

    # ------------------------------------------------------------------
    # Clocks and reset
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self):
        period = int(os.environ.get('TEST_APB_CLOCK_PERIOD', '10'))
        for clk in self.CLOCKS:
            await self.start_clock(clk, freq=period, units='ns')
        await self.assert_reset()
        await self.wait_clocks('pclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('pclk', 10)
        self.log.info(f"Clocks ({len(self.CLOCKS)}) and reset ready")

    async def assert_reset(self):
        for rst in self.RESETS:
            getattr(self.dut, rst).value = 0
        self.log.info("Reset asserted on all nine domains")

    async def deassert_reset(self):
        for rst in self.RESETS:
            getattr(self.dut, rst).value = 1
        self.log.info("Reset released")

    # ------------------------------------------------------------------
    # Components
    # ------------------------------------------------------------------
    async def setup_components(self):
        self.apb4_master = APBMaster(
            entity=self.dut,
            title="RLB Top APB Master",
            prefix="s_apb",
            clock=self.dut.pclk,
            bus_width=self.apb_data_width,
            addr_width=self.apb_addr_width,
            randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
            log=self.log,
        )
        await self.apb4_master.reset_bus()
        self._idle_inputs()
        await self.wait_clocks('pclk', 2)
        self.log.info("APB master created, all peripheral inputs idled")

    def _idle_inputs(self):
        """Idle every non-APB input. Active-low pins go HIGH (inactive)."""
        d = self.dut
        d.pic_irq_in.value = 0
        d.pit_gate_in.value = 0
        d.ioapic_irq_in.value = 0
        d.ioapic_irq_out_ready.value = 1     # receiver always accepts
        d.ioapic_irq_out_retry.value = 0
        d.ioapic_eoi_in.value = 0
        d.ioapic_eoi_vector.value = 0
        d.gpio_in.value = 0
        d.pm_gpe_events.value = 0
        d.pm_gpe1_events.value = 0
        # Buttons, wake and reset sources are ACTIVE LOW: idle high.
        d.pm_power_button_n.value = 1
        d.pm_sleep_button_n.value = 1
        d.pm_rtc_alarm.value = 0
        d.pm_ext_wake_n.value = 1
        d.pm_wdt_reset_n.value = 1
        d.pm_ext_reset_n.value = 1
        d.pm_power_domain_ack.value = 0xFF   # tie high, per the port comment
        # SMBus is open-drain with pull-ups: released lines read high.
        d.smb_scl_i.value = 1
        d.smb_sda_i.value = 1
        # UART idle is MARK (high). A low idle would be a break condition.
        d.uart_rx.value = 1
        d.uart_cts_n.value = 1
        d.uart_dsr_n.value = 1
        d.uart_ri_n.value = 1
        d.uart_dcd_n.value = 1

    # ------------------------------------------------------------------
    # APB access (bounded, modelled on IOAPICTB)
    # ------------------------------------------------------------------
    async def _xfer(self, pwrite: int, addr: int, data: int = 0):
        pkt = APBPacket(
            pwrite=pwrite, paddr=addr, pwdata=data, pstrb=0xF, pprot=0,
            data_width=self.apb_data_width,
            addr_width=self.apb_addr_width, strb_width=4,
        )
        pkt.direction = 'WRITE' if pwrite else 'READ'
        await self.apb4_master.send(pkt)

        read_data, done = 0, False
        for _ in range(100):
            await RisingEdge(self.dut.pclk)
            if (self.dut.s_apb_PSEL.value and self.dut.s_apb_PENABLE.value
                    and self.dut.s_apb_PREADY.value):
                read_data = self.dut.s_apb_PRDATA.value.integer
                done = True
                break
        if not done:
            # An access outside the 40KB window never completes -- the xbar
            # only drives m_cmd_ready when addr_in_range, so apb4_slave never
            # leaves IDLE. Say so rather than returning a silent zero.
            self.log.error(
                f"APB {'write' if pwrite else 'read'} at 0x{addr:08X} never "
                "completed -- PREADY did not assert within 100 cycles")
        await RisingEdge(self.dut.pclk)
        pkt.pslverr = pkt.fields.get('pslverr', 0)
        return pkt, read_data, int(pkt.pslverr)

    async def apb_write(self, addr: int, data: int):
        return await self._xfer(1, addr, data)

    async def apb_read(self, addr: int):
        return await self._xfer(0, addr)

    # ------------------------------------------------------------------
    # IOAPIC indirect access, through the subsystem window
    # ------------------------------------------------------------------
    async def ioapic_write(self, selector: int, value: int):
        base = self.window_addr(self.SLAVE_IOAPIC, 0x000)
        await self.apb_write(base + IOAPICRegisterMap.IOREGSEL, selector)
        await self.apb_write(base + IOAPICRegisterMap.IOWIN, value)

    async def arm_ioapic_pin(self, irq: int, masked: bool, boot_intx_en: bool):
        """Program one redirection entry and the boot-interrupt enable."""
        redir_lo = ((0x40 + irq) & 0xFF) | ((1 if masked else 0) << 16)
        await self.ioapic_write(
            IOAPICRegisterMap.get_redirection_offset(irq, high=False), redir_lo)
        await self.ioapic_write(
            IOAPICRegisterMap.get_redirection_offset(irq, high=True), 0)
        await self.ioapic_write(
            IOAPICRegisterMap.OFFSET_BOOTINTX, 1 if boot_intx_en else 0)
        await self.wait_clocks('pclk', 10)

    # ------------------------------------------------------------------
    # Interrupt observation
    # ------------------------------------------------------------------
    async def _pulse_and_watch(self, sig, irq: int, cycles: int = 40) -> bool:
        sig.value = (1 << irq)
        seen = False
        for _ in range(cycles):
            await RisingEdge(self.dut.pclk)
            if int(self.dut.pic_int_out.value):
                seen = True
                break
        sig.value = 0
        await self.wait_clocks('pclk', 5)
        return seen

    # ------------------------------------------------------------------
    # 8259 bring-up
    # ------------------------------------------------------------------
    async def pic_write(self, offset: int, value: int):
        await self.apb_write(self.window_addr(self.SLAVE_PIC, offset), value)
        await self.wait_clocks('pclk', 5)

    async def init_pic(self, vector_base: int = 0x20) -> bool:
        """Bring the 8259 up far enough to assert INT.

        This is PIC8259TB.initialize_pic's sequence, driven through the
        subsystem window instead of the block's own APB port. Reusing the
        block's recipe rather than inventing one from the datasheet matters:
        PIC_CONFIG must set pic_enable WITHOUT init_mode, because init_mode
        sends the FSM back to INIT_IDLE after it completes. ICW3 is not
        written -- ICW1 sets SNGL, so there is no cascade word.
        """
        await self.pic_write(PIC8259RegisterMap.PIC_CONFIG, 0x1)
        # ICW1: marker | SNGL | IC4, edge-triggered (LTIM=0)
        await self.pic_write(PIC8259RegisterMap.PIC_ICW1, 0x10 | 0x02 | 0x01)
        await self.pic_write(PIC8259RegisterMap.PIC_ICW2, vector_base)
        await self.pic_write(PIC8259RegisterMap.PIC_ICW4, 0x01)  # 8086 mode
        await self.pic_write(PIC8259RegisterMap.PIC_OCW1, 0x00)  # unmask all
        await self.wait_clocks('pclk', 10)
        _, status, _ = await self.apb_read(
            self.window_addr(self.SLAVE_PIC, PIC8259RegisterMap.PIC_STATUS))
        ok = bool(status & 1)
        self.log.info(f"PIC init {'complete' if ok else 'FAILED'} "
                      f"(PIC_STATUS=0x{status:08X})")
        return ok

    async def reset_and_init_pic(self) -> bool:
        """Full reset, then re-init the PIC.

        Between phases the whole DUT is reset rather than acknowledging the
        interrupt. In edge mode int_out LATCHES high until cleared, and the
        acknowledge/EOI paths are what pic_8259's own C3/C4 tests describe as
        expected-RED -- so an acknowledge-based clear would make this
        integration test fail on someone else's known defect. Reset is
        unambiguous. It also drops the IOAPIC programming, so callers must
        re-arm after calling this.
        """
        await self.assert_reset()
        await self.wait_clocks('pclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('pclk', 10)
        self._idle_inputs()
        await self.wait_clocks('pclk', 5)
        return await self.init_pic()

    def pic_int_out(self) -> int:
        return int(self.dut.pic_int_out.value)

    async def pulse_pic_irq(self, irq: int) -> bool:
        """Drive the legacy input directly; did the 8259 raise INT?"""
        return await self._pulse_and_watch(self.dut.pic_irq_in, irq)

    async def pulse_ioapic_irq(self, irq: int) -> bool:
        """Drive the IOAPIC pin; did it reach the 8259 by rerouting?"""
        return await self._pulse_and_watch(self.dut.ioapic_irq_in, irq)
