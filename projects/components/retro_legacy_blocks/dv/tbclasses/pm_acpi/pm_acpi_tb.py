# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PMACPIRegisterMap, PMACPITB
# Purpose: PM_ACPI (Power Management ACPI) Testbench
#
# Documentation: projects/components/retro_legacy_blocks/docs/pm_acpi_spec/
# Subsystem: retro_legacy_blocks/pm_acpi
#
# Created: 2025-11-29

"""
PM_ACPI (Power Management ACPI) Testbench

Comprehensive testbench for the APB PM_ACPI module providing:
- 32-bit PM Timer verification
- Power state FSM testing (S0/S1/S3)
- GPE (General Purpose Events) handling
- Clock gating control verification
- Power domain control testing
- Wake event detection
- Interrupt generation testing

Features:
- APB register access
- PM Timer configuration and monitoring
- Power state transitions
- GPE event injection
- Button press simulation
- Interrupt verification
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
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.amba_random_configs import APB_MASTER_RANDOMIZER_CONFIGS


class PMACPIRegisterMap:
    """PM_ACPI Register address definitions."""

    # ACPI Control and Status (0x00-0x0F)
    ACPI_CONTROL = 0x000        # 0x000: ACPI global control
    ACPI_STATUS = 0x004         # 0x004: ACPI status flags (W1C)
    ACPI_INT_ENABLE = 0x008     # 0x008: Interrupt enables
    ACPI_INT_STATUS = 0x00C     # 0x00C: Interrupt status (W1C)

    # PM1 Registers (0x10-0x1F)
    PM1_CONTROL = 0x010         # 0x010: PM1 control (sleep type, etc)
    PM1_STATUS = 0x014          # 0x014: PM1 status (W1C)
    PM1_ENABLE = 0x018          # 0x018: PM1 enables

    # PM Timer (0x20-0x2F)
    PM_TIMER_VALUE = 0x020      # 0x020: PM Timer current value (RO)
    PM_TIMER_CONFIG = 0x024     # 0x024: PM Timer configuration

    # GPE Registers (0x30-0x3F)
    GPE0_STATUS_LO = 0x030      # 0x030: GPE0 status low 16 bits (W1C)
    GPE0_STATUS_HI = 0x034      # 0x034: GPE0 status high 16 bits (W1C)
    GPE0_ENABLE_LO = 0x038      # 0x038: GPE0 enable low 16 bits
    GPE0_ENABLE_HI = 0x03C      # 0x03C: GPE0 enable high 16 bits

    # Clock and Power Control (0x50-0x5F)
    CLOCK_GATE_CTRL = 0x050     # 0x050: Clock gate control
    CLOCK_GATE_STATUS = 0x054   # 0x054: Clock gate status (RO)
    POWER_DOMAIN_CTRL = 0x058   # 0x058: Power domain control
    POWER_DOMAIN_STATUS = 0x05C # 0x05C: Power domain status (RO)

    # Wake and Reset (0x60-0x6F)
    WAKE_STATUS = 0x060         # 0x060: Wake status (W1C)
    WAKE_ENABLE = 0x064         # 0x064: Wake enables
    RESET_CTRL = 0x068          # 0x068: Reset control
    RESET_STATUS = 0x06C        # 0x06C: Reset status (RO)
    BUTTON_TIMING = 0x070       # 0x070: Button debounce and long-press
    PM_TIMER_VALUE_HI = 0x074   # 0x074: PM Timer high word (shadow, RO)
    PM_TIMER_MATCH = 0x078      # 0x078: PM Timer comparator
    PWR_SEQ_CONFIG = 0x07C      # 0x07C: Power sequencer configuration
    PWR_SEQ_STATUS = 0x080      # 0x080: Power sequencer status (RO)
    GPE0_TRIGGER_LO = 0x084     # 0x084: GPE0 edge/level per source [15:0]
    GPE0_TRIGGER_HI = 0x088     # 0x088: GPE0 edge/level per source [31:16]
    GPE0_WAKE_EN_LO = 0x08C     # 0x08C: GPE0 wake arming [15:0]
    GPE0_WAKE_EN_HI = 0x090     # 0x090: GPE0 wake arming [31:16]
    GPE1_STATUS_LO = 0x094      # 0x094: GPE1 status [15:0] (W1C)
    GPE1_STATUS_HI = 0x098      # 0x098: GPE1 status [31:16] (W1C)
    GPE1_ENABLE_LO = 0x09C      # 0x09C: GPE1 enable [15:0]
    GPE1_ENABLE_HI = 0x0A0      # 0x0A0: GPE1 enable [31:16]
    GPE1_TRIGGER_LO = 0x0A4     # 0x0A4: GPE1 edge/level per source [15:0]
    GPE1_TRIGGER_HI = 0x0A8     # 0x0A8: GPE1 edge/level per source [31:16]
    GPE1_WAKE_EN_LO = 0x0AC     # 0x0AC: GPE1 wake arming [15:0]
    GPE1_WAKE_EN_HI = 0x0B0     # 0x0B0: GPE1 wake arming [31:16]

    # ACPI_CONTROL bit definitions
    #
    # GH#54: bits below were audited against peakrdl/pm_acpi_regs.rdl's actual
    # field ranges after gh54 sleep-entry tests (test_gh54_pwrbtn_wake_latches_in_s0
    # / test_gh54_level_wake_guard) polled current_state via APB and never saw
    # anything but 0, even though a whitebox read of pm_acpi_core.current_pwr_state
    # proved the FSM really was in S3 and staying there. Root cause: this class
    # had current_state at [7:6] and low_power_req/soft_reset at [3]/[4], but the
    # RDL places them at current_state[5:4], low_power_req[6:6], soft_reset[7:7]
    # (bit 3 is an unnamed gap between gpe_enable[2:2] and current_state[5:4]).
    # Every pre-existing test only ever checked current_state at reset (=0,
    # indistinguishable under either mask) and never exercised low_power_req/
    # soft_reset's real bit position, so the wrong mask was never caught.
    CONTROL_ACPI_ENABLE = (1 << 0)
    CONTROL_PM_TIMER_ENABLE = (1 << 1)
    CONTROL_GPE_ENABLE = (1 << 2)
    # Bit 3 is an unnamed reserved gap (no RDL field covers it).
    # Bits 5:4 = current_state (read-only)
    CONTROL_CURRENT_STATE_MASK = 0x30
    CONTROL_CURRENT_STATE_SHIFT = 4
    CONTROL_LOW_POWER_REQ = (1 << 6)
    CONTROL_SOFT_RESET = (1 << 7)
    CONTROL_GPE_SPLIT_ENABLE = (1 << 8)

    # ACPI_STATUS bit definitions (W1C)
    STATUS_PME = (1 << 0)
    STATUS_WAKE = (1 << 1)
    STATUS_TIMER_OVERFLOW = (1 << 2)
    STATUS_STATE_TRANSITION = (1 << 3)
    STATUS_TIMER_MATCH = (1 << 4)

    # ACPI_INT_ENABLE bit definitions
    INT_ENABLE_PME = (1 << 0)
    INT_ENABLE_WAKE = (1 << 1)
    INT_ENABLE_TIMER_OVF = (1 << 2)
    INT_ENABLE_STATE_TRANS = (1 << 3)
    INT_ENABLE_PM1 = (1 << 4)
    INT_ENABLE_GPE = (1 << 5)
    INT_ENABLE_TIMER_MATCH = (1 << 6)

    # ACPI_INT_STATUS bit definitions (W1C)
    INT_STATUS_PME = (1 << 0)
    INT_STATUS_WAKE = (1 << 1)
    INT_STATUS_TIMER_OVF = (1 << 2)
    INT_STATUS_STATE_TRANS = (1 << 3)
    INT_STATUS_PM1 = (1 << 4)
    INT_STATUS_GPE = (1 << 5)
    INT_STATUS_TIMER_MATCH = (1 << 6)

    # PM1_CONTROL bit definitions
    PM1_SLEEP_TYPE_MASK = 0x7
    PM1_SLEEP_TYPE_SHIFT = 0
    PM1_SLEEP_ENABLE = (1 << 3)
    PM1_PWRBTN_OVR = (1 << 4)
    PM1_SLPBTN_OVR = (1 << 5)

    # PM1_STATUS bit definitions (W1C)
    PM1_STATUS_TMR = (1 << 0)
    PM1_STATUS_PWRBTN = (1 << 1)
    PM1_STATUS_SLPBTN = (1 << 2)
    PM1_STATUS_RTC = (1 << 3)
    PM1_STATUS_WAK = (1 << 4)

    # PM1_ENABLE bit definitions
    PM1_ENABLE_TMR = (1 << 0)
    PM1_ENABLE_PWRBTN = (1 << 1)
    PM1_ENABLE_SLPBTN = (1 << 2)
    PM1_ENABLE_RTC = (1 << 3)

    # PM_TIMER_CONFIG bit definitions
    PM_TIMER_DIV_MASK = 0xFFFF
    PM_TIMER_PRESCALE_SHIFT = 16      # [19:16] pre-divide by 2**this
    PM_TIMER_PRESCALE_MASK = 0xF
    PM_TIMER_64BIT = (1 << 20)        # overflow from bit 63, not bit 31

    # PWR_SEQ_CONFIG bit definitions
    SEQ_ENABLE = (1 << 0)
    SEQ_ACK_ENABLE = (1 << 1)
    SEQ_DELAY_SHIFT = 16

    # PWR_SEQ_STATUS bit definitions (RO)
    SEQ_STATUS_BUSY = (1 << 0)
    SEQ_STATUS_INDEX_SHIFT = 4
    SEQ_STATUS_INDEX_MASK = 0x7
    SEQ_STATUS_DIR = (1 << 8)

    # WAKE_STATUS bit definitions (W1C)
    WAKE_STATUS_GPE = (1 << 0)
    WAKE_STATUS_PWRBTN = (1 << 1)
    WAKE_STATUS_RTC = (1 << 2)
    WAKE_STATUS_EXT = (1 << 3)

    # WAKE_ENABLE bit definitions
    WAKE_ENABLE_GPE = (1 << 0)
    WAKE_ENABLE_PWRBTN = (1 << 1)
    WAKE_ENABLE_RTC = (1 << 2)
    WAKE_ENABLE_EXT = (1 << 3)

    # RESET_CTRL bit definitions
    RESET_CTRL_SYS = (1 << 0)
    RESET_CTRL_PERIPH = (1 << 1)

    # RESET_STATUS bit definitions (RO)
    RESET_STATUS_POR = (1 << 0)
    RESET_STATUS_WDT = (1 << 1)
    RESET_STATUS_SW = (1 << 2)
    RESET_STATUS_EXT = (1 << 3)

    # Power State definitions
    POWER_STATE_S0 = 0  # Working
    POWER_STATE_S1 = 1  # Sleep
    POWER_STATE_S3 = 3  # Deep sleep/Suspend


class PMACPITB(TBBase):
    """
    PM_ACPI Testbench class.

    Provides comprehensive testing infrastructure for the APB PM_ACPI module.
    """

    def __init__(self, dut, **kwargs):
        """
        Initialize PM_ACPI testbench.

        Args:
            dut: DUT (Device Under Test) handle
            **kwargs: Additional arguments for TBBase
        """
        super().__init__(dut)

        self.dut = dut
        self.pclk = dut.pclk
        self.presetn = dut.presetn

        # Components will be initialized in setup_clocks_and_reset
        self.apb4_master = None

        # Test tracking
        self.interrupt_events = []
        self.power_state_changes = []
        self.gpe_events = []

        # CDC_ENABLE mirror of the RTL parameter, plumbed by the runner via
        # TEST_CDC_ENABLE (same pattern as pit_8254_tb.py/gpio_tb.py). Needed
        # so GH#54 whitebox tests can sample/poke pm_acpi_core internals on
        # the clock the core actually runs on (pm_clk when CDC_ENABLE=1, pclk
        # when 0 - see apb4_pm_acpi.sv's `CDC_ENABLE[0] ? pm_clk : pclk`).
        self.cdc_enable = bool(int(os.environ.get('TEST_CDC_ENABLE', '0')))
        self.core_clk = None  # set in setup_clocks_and_reset

    async def setup_clocks_and_reset(self):
        """Complete initialization - clocks and reset (MANDATORY METHOD).

        Clock periods are read from TEST_APB_CLOCK_PERIOD / TEST_PM_CLOCK_PERIOD
        (plumbed by the test runner), same pattern as pit_8254_tb.py. GH#54:
        the runner drives pm_clk at a non-unity, non-integer ratio to pclk
        (10ns:7ns) whenever CDC_ENABLE=1, so a CDC configuration actually
        crosses a real clock-domain boundary instead of running edge-identical
        clocks. When CDC_ENABLE=0 the RTL ties both internal instances to
        pclk, so pm_clk is started at the same period as pclk to match (it
        exists as a port either way, just unused internally).
        """
        apb_clock_period_ns = int(os.environ.get('TEST_APB_CLOCK_PERIOD', '10'))
        pm_clock_period_ns = int(os.environ.get('TEST_PM_CLOCK_PERIOD', str(apb_clock_period_ns)))

        # Start APB clock (100 MHz = 10ns period by default)
        await self.start_clock('pclk', freq=apb_clock_period_ns, units='ns')

        # Start PM clock (same period as APB unless the runner requests a CDC ratio)
        await self.start_clock('pm_clk', freq=pm_clock_period_ns, units='ns')

        # Initialize external inputs to inactive state
        self.dut.gpe_events.value = 0
        self.dut.gpe1_events.value = 0
        self.dut.power_button_n.value = 1  # Active low, so 1 = not pressed
        self.dut.sleep_button_n.value = 1  # Active low, so 1 = not pressed
        self.dut.rtc_alarm.value = 0
        self.dut.ext_wake_n.value = 1      # Active low, so 1 = no wake
        self.dut.wdt_reset_n.value = 1     # Active low, so 1 = no watchdog reset
        self.dut.ext_reset_n.value = 1     # Active low, so 1 = no external reset
        # Every rail reports itself present. The sequencer only consults these
        # when PWR_SEQ_CONFIG.seq_ack_enable is set, and a test that wants to
        # model a slow or dead rail drives them itself.
        self.dut.power_domain_ack.value = 0xFF

        # Perform reset sequence
        await self.assert_reset()
        await self.wait_clocks('pclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('pclk', 5)

        # Core clock: the clock pm_acpi_core/pm_acpi_config_regs actually run
        # on (apb4_pm_acpi.sv CDC_ENABLE[0] ? pm_clk : pclk). Whitebox
        # sampling/poking of core internals must use this edge.
        self.core_clk = self.dut.pm_clk if self.cdc_enable else self.dut.pclk

    async def setup_components(self):
        """Initialize APB components (call after setup_clocks_and_reset)."""
        self.log.info("Setting up PM_ACPI testbench components")

        try:
            # Create APB Master - SAME AS PIT/HPET/RTC
            self.apb4_master = APBMaster(
                entity=self.dut,
                title='PM_ACPI APB Master',
                prefix='s_apb_',  # Consistent s_apb_* naming
                clock=self.dut.pclk,
                bus_width=32,
                addr_width=12,
                randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
                log=self.log
            )

            # Properly initialize the APB master
            await self.apb4_master.reset_bus()
            self.log.info(f"APB Master created and initialized: {type(self.apb4_master)}")

        except Exception as e:
            self.log.error(f"Failed to create APB Master: {e}")
            raise

        self.log.info("PM_ACPI testbench components setup complete")

    async def assert_reset(self):
        """Assert reset (MANDATORY METHOD)."""
        self.presetn.value = 0           # Active-low APB reset
        self.dut.pm_resetn.value = 0     # Active-low PM reset

    async def deassert_reset(self):
        """Deassert reset (MANDATORY METHOD)."""
        self.presetn.value = 1           # Release active-low APB reset
        self.dut.pm_resetn.value = 1     # Release active-low PM reset

    # ========================================================================
    # Register Access Methods
    # ========================================================================

    async def write_register(self, addr: int, data: int) -> APBPacket:
        """Write to PM_ACPI register using correct APB master API.

        GH#54: the returned packet's ``.pslverr`` (and equivalently
        ``.fields['pslverr']``) carries the APB slave error response sampled
        by the framework APB master BFM (APBMaster._finish_xmit) once the
        transaction completes - same pattern as pic_8259_tb.py/pit_tb.py's
        write_register().
        """
        try:
            # Create APB packet
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

            if not hasattr(self.apb4_master, 'transmit_coroutine'):
                self.apb4_master.transmit_coroutine = None

            await self.apb4_master.send(write_packet)

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

            # Expose the completed transaction's PSLVERR response. write_packet
            # is the exact object queued into APBMaster.send() above, and
            # APBMaster._finish_xmit already wrote fields['pslverr'] from
            # s_apb_PSLVERR before the PSEL&&PENABLE&&PREADY handshake waited
            # for above completed, so it is settled by this point.
            write_packet.pslverr = write_packet.fields.get('pslverr', 0)
            return write_packet

        except Exception as e:
            self.log.error(f"Write register failed: {e}")
            raise

    async def read_register(self, addr: int) -> Tuple[APBPacket, int]:
        """Read from PM_ACPI register using correct APB master API."""
        try:
            # Create APB packet
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

            if not hasattr(self.apb4_master, 'transmit_coroutine'):
                self.apb4_master.transmit_coroutine = None

            await self.apb4_master.send(read_packet)

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

            # Expose the completed transaction's PSLVERR response (see
            # write_register for the same-timing rationale).
            read_packet.pslverr = read_packet.fields.get('pslverr', 0)
            return read_packet, read_data

        except Exception as e:
            self.log.error(f"Read register failed: {e}")
            raise

    # ========================================================================
    # PM_ACPI Configuration Helpers
    # ========================================================================

    async def enable_acpi(self, enable: bool = True, pm_timer: bool = True, gpe: bool = True):
        """
        Enable/disable ACPI and its subsystems.

        Args:
            enable: Enable ACPI globally
            pm_timer: Enable PM timer
            gpe: Enable GPE processing
        """
        control = 0
        if enable:
            control |= PMACPIRegisterMap.CONTROL_ACPI_ENABLE
        if pm_timer:
            control |= PMACPIRegisterMap.CONTROL_PM_TIMER_ENABLE
        if gpe:
            control |= PMACPIRegisterMap.CONTROL_GPE_ENABLE
        await self.write_register(PMACPIRegisterMap.ACPI_CONTROL, control)

    async def configure_pm_timer(self, divider: int = 1):
        """
        Configure PM Timer divider.

        Args:
            divider: Clock divider value (0-65535)
        """
        await self.write_register(PMACPIRegisterMap.PM_TIMER_CONFIG,
                                  divider & PMACPIRegisterMap.PM_TIMER_DIV_MASK)

    async def read_pm_timer(self) -> int:
        """
        Read current PM Timer value.

        Returns:
            32-bit timer value
        """
        _, value = await self.read_register(PMACPIRegisterMap.PM_TIMER_VALUE)
        return value

    async def get_current_power_state(self) -> int:
        """
        Read current power state.

        Returns:
            Power state (0=S0, 1=S1, 3=S3)
        """
        _, control = await self.read_register(PMACPIRegisterMap.ACPI_CONTROL)
        state = (control & PMACPIRegisterMap.CONTROL_CURRENT_STATE_MASK) >> \
                PMACPIRegisterMap.CONTROL_CURRENT_STATE_SHIFT
        return state

    async def request_sleep(self, sleep_type: int = 1):
        """
        Request entry to sleep state.

        Args:
            sleep_type: Target sleep state (0=S0, 1=S1, 3=S3)
        """
        control = (sleep_type & PMACPIRegisterMap.PM1_SLEEP_TYPE_MASK) | \
                  PMACPIRegisterMap.PM1_SLEEP_ENABLE
        await self.write_register(PMACPIRegisterMap.PM1_CONTROL, control)

    async def configure_gpe_enables(self, enables: int):
        """
        Configure GPE enables (32-bit mask).

        Args:
            enables: 32-bit GPE enable mask
        """
        await self.write_register(PMACPIRegisterMap.GPE0_ENABLE_LO, enables & 0xFFFF)
        await self.write_register(PMACPIRegisterMap.GPE0_ENABLE_HI, (enables >> 16) & 0xFFFF)

    async def read_gpe_status(self) -> int:
        """
        Read GPE status (32-bit).

        Returns:
            32-bit GPE status
        """
        _, lo = await self.read_register(PMACPIRegisterMap.GPE0_STATUS_LO)
        _, hi = await self.read_register(PMACPIRegisterMap.GPE0_STATUS_HI)
        return (hi << 16) | lo

    async def clear_gpe_status(self, mask: int):
        """
        Clear GPE status bits (W1C).

        Args:
            mask: Bits to clear
        """
        await self.write_register(PMACPIRegisterMap.GPE0_STATUS_LO, mask & 0xFFFF)
        await self.write_register(PMACPIRegisterMap.GPE0_STATUS_HI, (mask >> 16) & 0xFFFF)

    async def configure_wake_enables(self, gpe: bool = False, pwrbtn: bool = False,
                                      rtc: bool = False, ext: bool = False):
        """
        Configure wake source enables.

        Args:
            gpe: Enable GPE wake
            pwrbtn: Enable power button wake
            rtc: Enable RTC alarm wake
            ext: Enable external wake
        """
        enables = 0
        if gpe:
            enables |= PMACPIRegisterMap.WAKE_ENABLE_GPE
        if pwrbtn:
            enables |= PMACPIRegisterMap.WAKE_ENABLE_PWRBTN
        if rtc:
            enables |= PMACPIRegisterMap.WAKE_ENABLE_RTC
        if ext:
            enables |= PMACPIRegisterMap.WAKE_ENABLE_EXT
        await self.write_register(PMACPIRegisterMap.WAKE_ENABLE, enables)

    async def configure_clock_gates(self, mask: int):
        """
        Configure clock gate control.

        Args:
            mask: 32-bit clock gate enable mask
        """
        await self.write_register(PMACPIRegisterMap.CLOCK_GATE_CTRL, mask)

    async def read_clock_gate_status(self) -> int:
        """
        Read clock gate status.

        Returns:
            32-bit clock gate status
        """
        _, status = await self.read_register(PMACPIRegisterMap.CLOCK_GATE_STATUS)
        return status

    async def configure_power_domains(self, mask: int):
        """
        Configure power domain control.

        Args:
            mask: 8-bit power domain enable mask
        """
        await self.write_register(PMACPIRegisterMap.POWER_DOMAIN_CTRL, mask & 0xFF)

    async def read_power_domain_status(self) -> int:
        """
        Read power domain status.

        Returns:
            8-bit power domain status
        """
        _, status = await self.read_register(PMACPIRegisterMap.POWER_DOMAIN_STATUS)
        return status & 0xFF

    async def enable_interrupts(self, pme: bool = False, wake: bool = False,
                                 timer_ovf: bool = False, state_trans: bool = False,
                                 pm1: bool = False, gpe: bool = False):
        """
        Configure interrupt enables.

        Args:
            pme: Enable PME interrupt
            wake: Enable wake interrupt
            timer_ovf: Enable timer overflow interrupt
            state_trans: Enable state transition interrupt
            pm1: Enable PM1 interrupt
            gpe: Enable GPE interrupt
        """
        enables = 0
        if pme:
            enables |= PMACPIRegisterMap.INT_ENABLE_PME
        if wake:
            enables |= PMACPIRegisterMap.INT_ENABLE_WAKE
        if timer_ovf:
            enables |= PMACPIRegisterMap.INT_ENABLE_TIMER_OVF
        if state_trans:
            enables |= PMACPIRegisterMap.INT_ENABLE_STATE_TRANS
        if pm1:
            enables |= PMACPIRegisterMap.INT_ENABLE_PM1
        if gpe:
            enables |= PMACPIRegisterMap.INT_ENABLE_GPE
        await self.write_register(PMACPIRegisterMap.ACPI_INT_ENABLE, enables)

    async def read_interrupt_status(self) -> int:
        """
        Read interrupt status.

        Returns:
            Interrupt status bits
        """
        _, status = await self.read_register(PMACPIRegisterMap.ACPI_INT_STATUS)
        return status

    async def clear_interrupt_status(self, mask: int):
        """
        Clear interrupt status bits (W1C).

        Args:
            mask: Bits to clear
        """
        await self.write_register(PMACPIRegisterMap.ACPI_INT_STATUS, mask)

    async def read_acpi_status(self) -> Dict[str, bool]:
        """
        Read ACPI status register.

        Returns:
            Dictionary with status flags
        """
        _, status = await self.read_register(PMACPIRegisterMap.ACPI_STATUS)

        return {
            'pme': bool(status & PMACPIRegisterMap.STATUS_PME),
            'wake': bool(status & PMACPIRegisterMap.STATUS_WAKE),
            'timer_overflow': bool(status & PMACPIRegisterMap.STATUS_TIMER_OVERFLOW),
            'state_transition': bool(status & PMACPIRegisterMap.STATUS_STATE_TRANSITION)
        }

    async def read_pm1_status(self) -> Dict[str, bool]:
        """
        Read PM1 status register.

        Returns:
            Dictionary with PM1 status flags
        """
        _, status = await self.read_register(PMACPIRegisterMap.PM1_STATUS)

        return {
            'timer': bool(status & PMACPIRegisterMap.PM1_STATUS_TMR),
            'power_button': bool(status & PMACPIRegisterMap.PM1_STATUS_PWRBTN),
            'sleep_button': bool(status & PMACPIRegisterMap.PM1_STATUS_SLPBTN),
            'rtc': bool(status & PMACPIRegisterMap.PM1_STATUS_RTC),
            'wake': bool(status & PMACPIRegisterMap.PM1_STATUS_WAK)
        }

    async def read_wake_status(self) -> Dict[str, bool]:
        """
        Read wake status register.

        Returns:
            Dictionary with wake status flags
        """
        _, status = await self.read_register(PMACPIRegisterMap.WAKE_STATUS)

        return {
            'gpe': bool(status & PMACPIRegisterMap.WAKE_STATUS_GPE),
            'power_button': bool(status & PMACPIRegisterMap.WAKE_STATUS_PWRBTN),
            'rtc': bool(status & PMACPIRegisterMap.WAKE_STATUS_RTC),
            'external': bool(status & PMACPIRegisterMap.WAKE_STATUS_EXT)
        }

    async def read_reset_status(self) -> Dict[str, bool]:
        """
        Read reset status register.

        Returns:
            Dictionary with reset status flags
        """
        _, status = await self.read_register(PMACPIRegisterMap.RESET_STATUS)

        return {
            'por': bool(status & PMACPIRegisterMap.RESET_STATUS_POR),
            'watchdog': bool(status & PMACPIRegisterMap.RESET_STATUS_WDT),
            'software': bool(status & PMACPIRegisterMap.RESET_STATUS_SW),
            'external': bool(status & PMACPIRegisterMap.RESET_STATUS_EXT)
        }

    # ========================================================================
    # External Signal Helpers
    # ========================================================================

    async def inject_gpe_event(self, bit: int):
        """
        Inject a GPE event by pulsing a bit high then low.

        The GPE signal needs to be held long enough for the edge detection
        logic in pm_acpi_core to sample it. The pipeline includes:
        1. gpe_events_prev sampling in pm_acpi_core (1 cycle)
        2. Edge detection and gpe_status_reg update in pm_acpi_core (1 cycle)
        3. r_gpe_status_prev sampling in pm_acpi_config_regs (1 cycle)
        4. Edge detection w_gpe_status_edge in pm_acpi_config_regs (combinational)
        5. hwset/next propagation to PeakRDL register (1 cycle)

        Total: ~5 cycles minimum for the edge to propagate through.

        After the edge is captured, we clear the input so subsequent W1C
        operations can properly clear the status bits without re-triggering.

        Args:
            bit: GPE bit number (0-31)
        """
        current = int(self.dut.gpe_events.value)
        # Ensure the bit is low first for proper edge detection in pm_acpi_core
        self.dut.gpe_events.value = current & ~(1 << bit)
        await ClockCycles(self.pclk, 10)  # Let gpe_events_prev sample 0

        # Set the bit high for edge detection - this will:
        # 1. Create edge in pm_acpi_core (gpe_status_reg becomes sticky)
        # 2. status_gpe_status goes high
        # 3. pm_acpi_config_regs detects edge on status_gpe_status
        self.dut.gpe_events.value = current | (1 << bit)
        await ClockCycles(self.pclk, 20)  # Hold for full pipeline propagation

        # Clear the input signal - the pm_acpi_core gpe_status_reg is still sticky
        # but we need the input low so it doesn't keep re-triggering
        self.dut.gpe_events.value = current & ~(1 << bit)
        await ClockCycles(self.pclk, 10)  # Wait for any transients to settle

    async def press_power_button(self, cycles: int = 5):
        """
        Simulate power button press.

        Args:
            cycles: Number of clock cycles to hold button
        """
        self.dut.power_button_n.value = 0  # Press (active low)
        await ClockCycles(self.pclk, cycles)
        self.dut.power_button_n.value = 1  # Release
        await ClockCycles(self.pclk, 2)

    async def press_sleep_button(self, cycles: int = 5):
        """
        Simulate sleep button press.

        Args:
            cycles: Number of clock cycles to hold button
        """
        self.dut.sleep_button_n.value = 0  # Press (active low)
        await ClockCycles(self.pclk, cycles)
        self.dut.sleep_button_n.value = 1  # Release
        await ClockCycles(self.pclk, 2)

    async def trigger_rtc_alarm(self, cycles: int = 5):
        """
        Simulate RTC alarm assertion.

        Args:
            cycles: Number of clock cycles to hold alarm
        """
        self.dut.rtc_alarm.value = 1
        await ClockCycles(self.pclk, cycles)
        self.dut.rtc_alarm.value = 0
        await ClockCycles(self.pclk, 2)

    async def trigger_external_wake(self, cycles: int = 5):
        """
        Simulate external wake assertion.

        Args:
            cycles: Number of clock cycles to hold wake
        """
        self.dut.ext_wake_n.value = 0  # Assert (active low)
        await ClockCycles(self.pclk, cycles)
        self.dut.ext_wake_n.value = 1  # Deassert
        await ClockCycles(self.pclk, 2)

    def get_pm_interrupt(self) -> bool:
        """
        Get current PM interrupt state.

        Returns:
            True if interrupt is asserted
        """
        return bool(self.dut.pm_interrupt.value)

    def get_clock_gate_outputs(self) -> int:
        """
        Get current clock gate enable outputs.

        Returns:
            32-bit clock gate enable mask
        """
        return int(self.dut.clock_gate_en.value)

    def get_power_domain_outputs(self) -> int:
        """
        Get current power domain enable outputs.

        Returns:
            8-bit power domain enable mask
        """
        return int(self.dut.power_domain_en.value)

    # ========================================================================
    # GH#54 Helpers (whitebox stimulus + interrupt-pin sampling)
    # ========================================================================

    async def force_pm_timer_near_overflow(self, remaining_ticks: int = 2):
        """
        Whitebox-poke pm_acpi_core.r_pm_timer_count close to 2**32-1.

        There is no software path to force a PM Timer overflow quickly:
        PM_TIMER_VALUE is read-only (sw=r) and the counter is a genuine
        32-bit free-runner, so waiting for a natural overflow would take
        billions of sim cycles. This directly drives the internal counter
        register (a stimulus injection, not a hand-rolled protocol driver)
        so cfg_pm_timer_div=0 ticks it over within `remaining_ticks` core
        clock edges.

        Caller is responsible for enabling ACPI + PM timer (divider=0)
        first so cfg_acpi_enable && cfg_pm_timer_enable is true and the
        forced value is not immediately overwritten.

        History: the flop was pm_timer_count until the 2026-09-09 prefix-rule
        pass (issue #54 review F7) renamed it r_pm_timer_count; this reference
        follows the RTL name.
        """
        target = (2 ** 32) - remaining_ticks
        self.dut.u_pm_acpi_core.r_pm_timer_count.value = target
        self.log.info(f"  [whitebox] forced r_pm_timer_count -> 0x{target:08X}")

    def force_pm_timer_count(self, value: int):
        """
        Whitebox-poke the full 64-bit pm_acpi_core.r_pm_timer_count.

        The counter is a genuine free-runner with no software write path, so
        the only way to exercise a carry out of bit 31 inside a simulation is
        to start just below it. Same stimulus-injection argument as
        force_pm_timer_near_overflow(), which this generalises: the caller
        must already have ACPI and the PM timer enabled with a divider of 0,
        or the forced value simply sits there.
        """
        self.dut.u_pm_acpi_core.r_pm_timer_count.value = value & ((1 << 64) - 1)
        self.log.info(f"  [whitebox] forced r_pm_timer_count -> 0x{value:016X}")

    async def sample_signal_over(self, signal, cycles: int, clock=None) -> List[bool]:
        """
        Sample an arbitrary 1-bit signal once per clock edge for `cycles`
        edges, returning the list of sampled values (oldest first).

        Args:
            signal: a cocotb signal handle (e.g. self.dut.pm_interrupt)
            cycles: number of clock edges to sample
            clock: clock handle to sample on (defaults to self.pclk)
        """
        clk = clock if clock is not None else self.pclk
        samples = []
        for _ in range(cycles):
            await RisingEdge(clk)
            samples.append(bool(signal.value))
        return samples

    async def sample_pm_interrupt_over(self, cycles: int, clock=None) -> List[bool]:
        """Sample the pm_interrupt output pin - see sample_signal_over()."""
        return await self.sample_signal_over(self.dut.pm_interrupt, cycles, clock)

    async def force_power_state_s0(self):
        """
        GH#54 test cleanup: unconditionally return the FSM to PWR_S0_WORKING
        regardless of any wake/sleep bug under test. pm_acpi_core's next-state
        logic forces next_pwr_state = PWR_S0_WORKING whenever cfg_acpi_enable
        is low, independent of sleep_type/any_wake_event, so this is a clean
        way to leave the DUT in a known state between GH#54 test methods
        without depending on the very wake logic some of those tests exercise.
        """
        await self.write_register(PMACPIRegisterMap.PM1_CONTROL, 0)
        await self.write_register(PMACPIRegisterMap.ACPI_CONTROL, 0)  # acpi_enable=0
        await ClockCycles(self.pclk, 10)
        await self.write_register(PMACPIRegisterMap.ACPI_CONTROL, 0)  # stay disabled
        await ClockCycles(self.pclk, 5)
