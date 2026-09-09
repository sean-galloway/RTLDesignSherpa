# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PMACPIGH54Tests
# Purpose: PM_ACPI GitHub #54 defect-encoding test suite
#
# Documentation: projects/components/retro_legacy_blocks/docs/pm_acpi_mas/
# Subsystem: retro_legacy_blocks/pm_acpi
#
# Created: 2026-09-09

"""
PM_ACPI GitHub #54 Defect-Encoding Test Suite

This suite encodes the ACPI-style PM block contract the RDL/MAS describe,
as pass/fail assertions. Each item states the CONTRACT this suite enforces
in the present tense; the History line names the original finding for
context. Where the corresponding RTL fix has not landed yet, the test is
expected RED against current RTL - that is the point of the suite, not a
bug in it.

  1. All 19 one-bit W1C status fields in ACPI_STATUS, ACPI_INT_STATUS,
     PM1_STATUS and WAKE_STATUS are sticky: a hwset holds the bit until
     software W1Cs it, independent of anything else happening on the
     register in between.
     History: C2 / round_2 item 2 - `hwif_in.*.next` was undriven, so the
     bit reloaded to 0 (self-cleared) one clock after every hwset.
  2. GPE0_STATUS_LO/HI are per-bit sticky: an edge on GPE input k sets
     ONLY bit k and holds it; two edges on k and j hold exactly {k, j}.
     History: round_2 item 1 - hwset set ALL 16 bits in the register for
     one cycle (PeakRDL hwset semantics ignore `next`), then the next
     cycle reloaded the one-cycle edge-detect pulse, so software could
     never see which source fired.
  3. Once an enabled GPE fires and software W1Cs its status bit,
     `pm_interrupt` deasserts (GH54-3a) and a subsequent sleep request is
     honoured - the FSM actually leaves S0 (GH54-3b).
     History: H2 / round_2 item 5 / round_3 item 1 - pm_acpi_core's
     `gpe_status_reg` was set-only with no clear path from the software
     W1C, so `gpe_int` (and therefore `pm_interrupt`) latched forever, and
     `any_wake_event` (when gpe_wake_en=1) stayed permanently asserted,
     which blocked PWR_TRANSITION from ever resolving to S1/S3.
  4. PM1_ENABLE's per-source enables gate their sources: with
     PM1_ENABLE.<src>_en=0 an event sets the PM1_STATUS bit but does NOT
     raise `pm_interrupt`; with <src>_en=1 it does. Level PM1 sources
     (rtc_alarm) are edge-latched into their status bit like GPE, not
     re-armed every cycle the level is held (GH54-1, see item 11 below).
     History: H3 - cfg_pm1_tmr_en/pwrbtn_en/slpbtn_en/rtc_en were routed
     all the way to pm_acpi_core's port list and never used; `pm1_int` was
     gated only by the global `cfg_pm1_enable`.
  5. A pulsed wake source (power button) wakes the device from S1/S3 to
     S0 and it STAYS there. Level wake sources (rtc_alarm, ext_wake_n,
     the sticky GPE wake) already do this correctly (GH54-5b is a
     regression guard for that, not a defect test).
     History: H5 - `power_button_press` is a one-cycle pulse;
     PWR_TRANSITION re-sampled the still-programmed sleep_type after the
     pulse was gone and re-entered sleep.
  6. `pm_interrupt` for non-GPE sources is level: it stays asserted while
     the corresponding status is set and deasserts only when cleared, not
     a one-cycle pulse off the raw hardware event.
     History: round_3 item 3 - timer overflow, state_transition_done and
     button presses drove `pm_interrupt` as one-cycle combinational
     pulses - the opposite failure mode from the GPE term, which never
     deasserted at all.
  7. Only the 21 mapped registers are software-visible in the 4KB APB
     window; everything else (including the 7-bit alias at 0x080, which
     hits ACPI_CONTROL) is dropped - write ignored, read 0 - with PSLVERR.
     History: round_2 item 4 - `pm_acpi_config_regs` connected
     `regblk_addr[8:0]` (9 bits) to `pm_acpi_regs`'s 7-bit `s_cpuif_addr`
     port, so only PADDR[6:0] was ever decoded, and `cpuif_wr_err`/
     `readback_err` were tied off so PSLVERR never fired at all.
  8. rtc_alarm/ext_wake_n/gpe_events_in reach the core correctly from the
     pclk-domain testbench (functional-only guard - cocotb cannot exercise
     metastability, so this does not prove synchronizer safety).
     History: round_2 item 6 / round_3 item 2 - these three inputs have no
     synchronizer at all (button inputs get a 3-flop sync); a real gap
     under CDC_ENABLE=1 that this guard cannot close.
  9. Toggling a GPE input while GPE/ACPI is disabled, then enabling with
     the input left steady, must NOT manufacture a spurious status bit.
     History: round_3 item 4 - `gpe_events_prev` only updated while
     `cfg_acpi_enable && cfg_gpe_enable`, so it froze at its pre-disable
     value and produced a false edge on re-enable.
  10. RESET_STATUS.por_reset reads 1 after reset and stays sticky;
      RESET_STATUS.sw_reset reads 1 after ACPI_CONTROL.soft_reset, and
      soft_reset itself clears every sticky status register, GPE0_STATUS
      and the wake latch (the power state returns to S0 and stays),
      self-clears, and leaves configuration registers intact.
      wdt_reset/ext_reset stay 0 - the module has no watchdog or external-
      reset input pins at all, so this is a documented "always 0" contract
      rather than a defect being chased.
      History: por_reset was `first_cycle`, a single-cycle pulse the very
      first clock after reset that normal APB latency always missed;
      ACPI_CONTROL.soft_reset was entirely unconnected to the core (H6),
      so it did nothing but auto-clear its own field.

Every test method here follows the same {try/assert/return True} ...
{except AssertionError: log + return False} pattern as
pit_tests_medium.py's GH#52 address-decode test, and is registered at the
medium/full test levels (run_all_gh54_tests() is invoked from
test_apb4_pm_acpi.py's `func` and `full` branches, never `gate`).

State hygiene (temporary, pending the item-3 RTL fix): until
pm_acpi_core's `gpe_status_reg` gets a clear path, any GPE bit ever
injected in this suite is stuck set at the core level for the rest of the
simulation. Every test method that is not specifically about GPE
explicitly zeroes GPE0_ENABLE_LO/HI (and ACPI_INT_ENABLE.gpe_int_enable)
so that permanent core-level pollution cannot leak into gpe_int /
pm_interrupt for later tests, and the GPE-interrupt-latch tests (which
exploit that stuck state on purpose) run near the end. `_clean_slate()`
itself is a plain per-test reset-to-known-config helper and stays
regardless of when item 3 lands; only the GPE-specific ordering/masking
around it is expected to become removable once gpe_status_reg is
clearable.
"""

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge

from projects.components.retro_legacy_blocks.dv.tbclasses.pm_acpi.pm_acpi_tb import (
    PMACPITB, PMACPIRegisterMap
)
from projects.components.retro_legacy_blocks.dv.tbclasses.pm_acpi.pm_acpi_tests_basic import (
    PMACPIBasicTests
)


# Generous settle window: real APB read/write round trips (and, under
# CDC_ENABLE=1, the async cmd/rsp FIFO crossing) already take many pclk
# cycles, but sticky-status self-clear (defect 1) happens within ~2-3 core
# clocks of the hwset pulse. This constant is deliberately far larger than
# either so every assertion below is robust to both CDC ratios (10ns:7ns).
SETTLE_CYCLES = 40


class PMACPIGH54Tests:
    """GitHub #54 defect-encoding test methods for PM_ACPI."""

    def __init__(self, tb: PMACPITB):
        self.tb = tb
        self.log = tb.log

    async def run_all_gh54_tests(self) -> bool:
        """Run all GH#54 tests. Registered at medium/full - never gate."""
        self.log.info("=" * 80)
        self.log.info("Starting PM_ACPI GH#54 Defect-Encoding Tests")
        self.log.info("=" * 80)

        test_methods = [
            ('GH54 ACPI_STATUS sticky', self.test_gh54_acpi_status_sticky),
            ('GH54 ACPI_INT_STATUS sticky', self.test_gh54_acpi_int_status_sticky),
            ('GH54 PM1_STATUS sticky', self.test_gh54_pm1_status_sticky),
            ('GH54 WAKE_STATUS sticky', self.test_gh54_wake_status_sticky),
            ('GH54 status cross-field independence', self.test_gh54_status_cross_field_independence),
            ('GH54 level sources are edge-latched (PM1 rtc)', self.test_gh54_level_sources_are_edge_latched),
            ('GH54 level sources are edge-latched (WAKE ext)', self.test_gh54_wake_level_source_is_edge_latched),
            ('GH54 GPE0_STATUS per-bit sticky', self.test_gh54_gpe_status_per_bit_sticky),
            ('GH54 GPE0_STATUS two bits exact', self.test_gh54_gpe_status_two_bits_exact),
            ('GH54 PM1_ENABLE gates interrupt', self.test_gh54_pm1_enable_gates_interrupt),
            ('GH54 pm_interrupt level not pulse', self.test_gh54_pm_interrupt_level_not_pulse),
            ('GH54 address alias dropped + PSLVERR', self.test_gh54_address_alias_dropped_with_pslverr),
            ('GH54 CDC async input guard', self.test_gh54_cdc_async_input_guard),
            ('GH54 gpe_events_prev no freeze', self.test_gh54_gpe_prev_no_freeze_spurious_edge),
            ('GH54 pwrbtn wake latches in S0', self.test_gh54_pwrbtn_wake_latches_in_s0),
            ('GH54 level wake guard', self.test_gh54_level_wake_guard),
            ('GH54 GPE interrupt deasserts after W1C', self.test_gh54_gpe_interrupt_deasserts_after_w1c),
            ('GH54 GPE sleep unblocked after W1C', self.test_gh54_gpe_sleep_unblocked_after_w1c),
            ('GH54 reset requests are one cycle', self.test_gh54_reset_requests_are_one_cycle),
            ('GH54 basic: RESET_CTRL request pulses', self.test_gh54_reset_control_basic_check),
            ('GH54 RESET_STATUS / soft_reset', self.test_gh54_reset_status_and_soft_reset),
        ]

        results = []
        for test_name, test_method in test_methods:
            self.log.info(f"\n{'=' * 60}")
            self.log.info(f"Running: {test_name}")
            self.log.info(f"{'=' * 60}")
            try:
                result = await test_method()
                results.append((test_name, result))
            except Exception as e:
                self.log.error(f"{test_name} raised exception: {e}")
                results.append((test_name, False))

        # Always leave the DUT in a clean, ACPI-disabled S0 state regardless
        # of what the sleep/wake tests above did to the FSM.
        await self.tb.force_power_state_s0()

        self.log.info("\n" + "=" * 80)
        self.log.info("GH#54 TEST SUMMARY")
        self.log.info("=" * 80)
        passed_count = sum(1 for _, result in results if result)
        total_count = len(results)
        for test_name, result in results:
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name:45s} {status}")
        self.log.info(f"\nGH#54 Tests: {passed_count}/{total_count} passed")

        return all(result for _, result in results)

    # ------------------------------------------------------------------
    # Shared setup helpers
    # ------------------------------------------------------------------

    async def _clean_slate(self, gpe: bool = False):
        """Explicitly zero every enable register this suite touches, so no
        test depends on state left behind by a previous one (see module
        docstring re: gpe_status_reg permanent pollution)."""
        await self.tb.write_register(PMACPIRegisterMap.ACPI_INT_ENABLE, 0)
        await self.tb.write_register(PMACPIRegisterMap.PM1_ENABLE, 0)
        await self.tb.write_register(PMACPIRegisterMap.WAKE_ENABLE, 0)
        if not gpe:
            await self.tb.write_register(PMACPIRegisterMap.GPE0_ENABLE_LO, 0)
            await self.tb.write_register(PMACPIRegisterMap.GPE0_ENABLE_HI, 0)
        # Best-effort W1C of every status register (harmless even though
        # defect 1 means most bits are already self-cleared by the time we
        # get here).
        await self.tb.write_register(PMACPIRegisterMap.ACPI_STATUS, 0xF)
        await self.tb.write_register(PMACPIRegisterMap.ACPI_INT_STATUS, 0x3F)
        await self.tb.write_register(PMACPIRegisterMap.PM1_STATUS, 0x1F)
        await self.tb.write_register(PMACPIRegisterMap.WAKE_STATUS, 0xF)
        await ClockCycles(self.tb.pclk, 5)

    # ------------------------------------------------------------------
    # 1. C2 / round_2 item 2 - W1C status sticky (one field per register)
    # ------------------------------------------------------------------

    async def test_gh54_acpi_status_sticky(self) -> bool:
        """ACPI_STATUS.pme_status must stay set until software W1Cs it."""
        self.log.info("Test: GH54-1a ACPI_STATUS W1C sticky (pme_status)")
        try:
            await self._clean_slate()
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            await self.tb.press_power_button()  # status_pme edge -> hwset
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            status = await self.tb.read_acpi_status()
            assert status['pme'], (
                "ACPI_STATUS.pme_status read 0 after settling - the W1C "
                "status field self-cleared instead of staying sticky "
                "(GH#54 C2: hwif_in.ACPI_STATUS.pme_status.next is "
                "undriven and reloaded every non-hwset cycle)"
            )

            # Now W1C it and confirm it actually clears (the write path
            # itself is not part of C2 - only the un-written persistence is).
            await self.tb.write_register(PMACPIRegisterMap.ACPI_STATUS,
                                          PMACPIRegisterMap.STATUS_PME)
            await ClockCycles(self.tb.pclk, 5)
            status = await self.tb.read_acpi_status()
            assert not status['pme'], "ACPI_STATUS.pme_status did not clear on W1C"

            self.log.info("PASS: ACPI_STATUS.pme_status sticky")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-1a FAILED: {e}")
            return False

    async def test_gh54_acpi_int_status_sticky(self) -> bool:
        """ACPI_INT_STATUS.pme_int must stay set until software W1Cs it."""
        self.log.info("Test: GH54-1b ACPI_INT_STATUS W1C sticky (pme_int)")
        try:
            await self._clean_slate()
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            await self.tb.press_power_button()  # status_pme edge -> pme_int hwset too
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            int_status = await self.tb.read_interrupt_status()
            assert int_status & PMACPIRegisterMap.INT_STATUS_PME, (
                f"ACPI_INT_STATUS.pme_int read 0x{int_status:02X} (bit0 clear) "
                f"after settling - self-cleared instead of staying sticky (GH#54 C2)"
            )

            self.log.info("PASS: ACPI_INT_STATUS.pme_int sticky")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-1b FAILED: {e}")
            return False

    async def test_gh54_pm1_status_sticky(self) -> bool:
        """PM1_STATUS.tmr_sts must stay set until software W1Cs it."""
        self.log.info("Test: GH54-1c PM1_STATUS W1C sticky (tmr_sts)")
        try:
            await self._clean_slate()
            await self.tb.configure_pm_timer(divider=0)
            await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            await RisingEdge(self.tb.core_clk)
            await self.tb.force_pm_timer_near_overflow(remaining_ticks=2)
            await ClockCycles(self.tb.core_clk, 5)
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            pm1 = await self.tb.read_pm1_status()
            assert pm1['timer'], (
                "PM1_STATUS.tmr_sts read 0 after settling - self-cleared "
                "instead of staying sticky (GH#54 C2)"
            )

            self.log.info("PASS: PM1_STATUS.tmr_sts sticky")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-1c FAILED: {e}")
            return False

    async def test_gh54_wake_status_sticky(self) -> bool:
        """WAKE_STATUS.pwrbtn_wake must stay set until software W1Cs it."""
        self.log.info("Test: GH54-1d WAKE_STATUS W1C sticky (pwrbtn_wake)")
        try:
            await self._clean_slate()
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await self.tb.configure_wake_enables(pwrbtn=True)
            await ClockCycles(self.tb.pclk, 5)

            await self.tb.press_power_button()  # pwrbtn_wake_event edge -> hwset
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            wake = await self.tb.read_wake_status()
            assert wake['power_button'], (
                "WAKE_STATUS.pwrbtn_wake read 0 after settling - self-cleared "
                "instead of staying sticky (GH#54 C2)"
            )

            self.log.info("PASS: WAKE_STATUS.pwrbtn_wake sticky")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-1d FAILED: {e}")
            return False

    async def test_gh54_status_cross_field_independence(self) -> bool:
        """Set A (timer_overflow) and B (pme) in ACPI_STATUS, W1C only B,
        confirm A survives. Dominated by the same undriven-.next root cause
        as the four sticky tests above (A self-clears on its own regardless
        of the W1C-B write), but it is still the correct-behaviour contract
        the review round_2 item 2 asked for."""
        self.log.info("Test: GH54-1e ACPI_STATUS cross-field independence")
        try:
            await self._clean_slate()
            await self.tb.configure_pm_timer(divider=0)
            await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            # A: force a timer overflow edge (sets ACPI_STATUS.timer_overflow)
            await RisingEdge(self.tb.core_clk)
            await self.tb.force_pm_timer_near_overflow(remaining_ticks=2)
            await ClockCycles(self.tb.core_clk, 5)

            # B: press power button (sets ACPI_STATUS.pme_status)
            await self.tb.press_power_button()
            await ClockCycles(self.tb.pclk, 10)

            # W1C only B (pme)
            await self.tb.write_register(PMACPIRegisterMap.ACPI_STATUS,
                                          PMACPIRegisterMap.STATUS_PME)
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            status = await self.tb.read_acpi_status()
            assert status['timer_overflow'], (
                "ACPI_STATUS.timer_overflow (field A) did not survive a W1C "
                "of a different field (pme_status, field B) - it read 0, "
                "i.e. it is not sticky (GH#54 C2)"
            )
            assert not status['pme'], "ACPI_STATUS.pme_status (field B) did not clear on its own W1C"

            self.log.info("PASS: ACPI_STATUS cross-field independence")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-1e FAILED: {e}")
            return False

    async def test_gh54_level_sources_are_edge_latched(self) -> bool:
        """Level sources (rtc_alarm, ext_wake_n) latch their status bit on
        the synchronized rising EDGE, like GPE - not re-set every cycle the
        level is held. Contract: HOLD the level, confirm the bit sets (and,
        for the PM1 rtc source with pm1_enable on, pm_interrupt asserts);
        W1C the bit WHILE the level is still held; the bit must clear and
        STAY cleared (and pm_interrupt must drop) even though the physical
        pin has not changed, because there is no new edge.

        RED today for two independent reasons that will resolve together
        with the pending RTL follow-up: item 1's sticky-field fix (this
        suite's item 1) is what lets the bit set at all, and pm1_int/
        WAKE_STATUS becoming driven by the latched status bit (rather than
        the raw pin) rather than a level term is what lets clearing the bit
        actually drop pm_interrupt while the pin is still asserted."""
        self.log.info("Test: GH54-11a Level sources are edge-latched (PM1 rtc)")
        try:
            await self._clean_slate()
            await self.tb.write_register(PMACPIRegisterMap.ACPI_INT_ENABLE,
                                          PMACPIRegisterMap.INT_ENABLE_PM1)
            await self.tb.write_register(PMACPIRegisterMap.PM1_ENABLE,
                                          PMACPIRegisterMap.PM1_ENABLE_RTC)
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            self.tb.dut.rtc_alarm.value = 1  # HOLD - do not release
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            pm1 = await self.tb.read_pm1_status()
            assert pm1['rtc'], "PM1_STATUS.rtc_sts did not set with rtc_alarm held high"
            assert self.tb.get_pm_interrupt(), (
                "pm_interrupt did not assert with rtc_alarm held high and pm1_enable/rtc_en set"
            )

            # W1C while the level is STILL held.
            await self.tb.write_register(PMACPIRegisterMap.PM1_STATUS,
                                          PMACPIRegisterMap.PM1_STATUS_RTC)
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            pm1 = await self.tb.read_pm1_status()
            assert not pm1['rtc'], (
                "PM1_STATUS.rtc_sts re-set itself after W1C while rtc_alarm was still "
                "held high - the level is re-arming the bit every cycle instead of only "
                "on the synchronized rising edge (GH#54 follow-up item 1)"
            )
            assert not self.tb.get_pm_interrupt(), (
                "pm_interrupt is still asserted after PM1_STATUS.rtc_sts was W1C'd, even "
                "though rtc_alarm is still held high - pm1_int must be driven by the "
                "latched status bit, not the raw level pin (GH#54 follow-up item 1)"
            )

            self.tb.dut.rtc_alarm.value = 0
            await ClockCycles(self.tb.pclk, 5)

            self.log.info("PASS: PM1_STATUS.rtc_sts edge-latched")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-11a FAILED: {e}")
            return False
        finally:
            self.tb.dut.rtc_alarm.value = 0

    async def test_gh54_wake_level_source_is_edge_latched(self) -> bool:
        """WAKE_STATUS.ext_wake must be edge-latched like the PM1 rtc case
        above: hold ext_wake_n low, confirm the bit sets, W1C it while
        still held, confirm it clears and STAYS cleared. WAKE_STATUS does
        not feed pm_interrupt in this architecture, so only the bit is
        checked here (see test_gh54_level_sources_are_edge_latched for the
        pm_interrupt-coupled PM1 case)."""
        self.log.info("Test: GH54-11b Level sources are edge-latched (WAKE ext)")
        try:
            await self._clean_slate()
            await self.tb.write_register(PMACPIRegisterMap.WAKE_ENABLE,
                                          PMACPIRegisterMap.WAKE_ENABLE_EXT)
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            self.tb.dut.ext_wake_n.value = 0  # HOLD asserted (active low) - do not release
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            wake = await self.tb.read_wake_status()
            assert wake['external'], "WAKE_STATUS.ext_wake did not set with ext_wake_n held low"

            await self.tb.write_register(PMACPIRegisterMap.WAKE_STATUS,
                                          PMACPIRegisterMap.WAKE_STATUS_EXT)
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            wake = await self.tb.read_wake_status()
            assert not wake['external'], (
                "WAKE_STATUS.ext_wake re-set itself after W1C while ext_wake_n was still "
                "held low - the level is re-arming the bit every cycle instead of only on "
                "the synchronized falling edge (GH#54 follow-up item 1)"
            )

            self.tb.dut.ext_wake_n.value = 1
            await ClockCycles(self.tb.pclk, 5)

            self.log.info("PASS: WAKE_STATUS.ext_wake edge-latched")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-11b FAILED: {e}")
            return False
        finally:
            self.tb.dut.ext_wake_n.value = 1
            await self.tb.write_register(PMACPIRegisterMap.WAKE_ENABLE, 0)

    # ------------------------------------------------------------------
    # 2. round_2 item 1 - GPE0_STATUS per-bit sticky
    # ------------------------------------------------------------------

    async def test_gh54_gpe_status_per_bit_sticky(self) -> bool:
        """A GPE edge on input k must set ONLY bit k, and it must hold."""
        self.log.info("Test: GH54-2a GPE0_STATUS per-bit sticky (single bit)")
        try:
            await self._clean_slate(gpe=True)
            bit = 5
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=True)
            await self.tb.configure_gpe_enables(1 << bit)
            await ClockCycles(self.tb.pclk, 10)

            await self.tb.inject_gpe_event(bit)
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            status = await self.tb.read_gpe_status()
            assert status == (1 << bit), (
                f"GPE0_STATUS after a single edge on bit {bit} read "
                f"0x{status:08X}, expected exactly 0x{1 << bit:08X} - "
                f"hwset sets ALL 16 bits in the register for one cycle "
                f"then self-clears (GH#54 round_2 item 1)"
            )

            # Clean up: W1C the bit so later tests start from a clear register.
            await self.tb.clear_gpe_status(1 << bit)
            self.log.info("PASS: GPE0_STATUS per-bit sticky (single bit)")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-2a FAILED: {e}")
            return False

    async def test_gh54_gpe_status_two_bits_exact(self) -> bool:
        """Two edges on k (lo half) and j (hi half) must set exactly {k, j}."""
        self.log.info("Test: GH54-2b GPE0_STATUS two bits exact")
        try:
            await self._clean_slate(gpe=True)
            bit_k, bit_j = 3, 20
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=True)
            await self.tb.configure_gpe_enables((1 << bit_k) | (1 << bit_j))
            await ClockCycles(self.tb.pclk, 10)

            await self.tb.inject_gpe_event(bit_k)
            await self.tb.inject_gpe_event(bit_j)
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            status = await self.tb.read_gpe_status()
            expected = (1 << bit_k) | (1 << bit_j)
            assert status == expected, (
                f"GPE0_STATUS after edges on bits {bit_k} and {bit_j} read "
                f"0x{status:08X}, expected exactly 0x{expected:08X} "
                f"(GH#54 round_2 item 1 - status is not per-bit sticky)"
            )

            await self.tb.clear_gpe_status(expected)
            self.log.info("PASS: GPE0_STATUS two bits exact")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-2b FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # 4. H3 - PM1_ENABLE per-source gating of pm_interrupt
    # ------------------------------------------------------------------

    async def test_gh54_pm1_enable_gates_interrupt(self) -> bool:
        """With PM1_ENABLE.<src>_en=0, a <src> event must NOT raise
        pm_interrupt; with <src>_en=1 it must. Looped over all four PM1
        sources rather than four near-duplicate test methods."""
        self.log.info("Test: GH54-4 PM1_ENABLE per-source interrupt gating")
        try:
            sources = [
                ('tmr', PMACPIRegisterMap.PM1_ENABLE_TMR, self._trigger_pm1_tmr),
                ('pwrbtn', PMACPIRegisterMap.PM1_ENABLE_PWRBTN, self.tb.press_power_button),
                ('slpbtn', PMACPIRegisterMap.PM1_ENABLE_SLPBTN, self.tb.press_sleep_button),
                ('rtc', PMACPIRegisterMap.PM1_ENABLE_RTC, self.tb.trigger_rtc_alarm),
            ]

            for name, enable_bit, trigger in sources:
                await self._clean_slate()
                # Isolate pm1_int: only ACPI_INT_ENABLE.pm1_enable set.
                await self.tb.write_register(PMACPIRegisterMap.ACPI_INT_ENABLE,
                                              PMACPIRegisterMap.INT_ENABLE_PM1)
                await self.tb.configure_pm_timer(divider=0)
                await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=False)
                await ClockCycles(self.tb.pclk, 5)

                # --- per-source enable OFF: event must NOT raise pm_interrupt ---
                await self.tb.write_register(PMACPIRegisterMap.PM1_ENABLE, 0)
                await ClockCycles(self.tb.pclk, 5)
                seen_high = await self._trigger_and_sample(trigger)
                assert not seen_high, (
                    f"pm_interrupt asserted for PM1 source '{name}' with "
                    f"PM1_ENABLE.{name}_en=0 - per-source enable does not "
                    f"gate the interrupt (GH#54 H3: cfg_pm1_{name}_en is "
                    f"routed to pm_acpi_core and never used)"
                )

                # Drain PM1_STATUS between phases (GH#54 follow-up F3): without
                # this, the ON-phase assertion below could be satisfied by a
                # leftover assertion carried over from the OFF-phase trigger
                # rather than by a fresh event under the enable=1 config,
                # which would make the ON check pass for the wrong reason.
                await self.tb.write_register(PMACPIRegisterMap.PM1_STATUS, 0x1F)
                await ClockCycles(self.tb.pclk, SETTLE_CYCLES)
                assert not self.tb.get_pm_interrupt(), (
                    f"pm_interrupt is still asserted for PM1 source '{name}' after "
                    f"draining PM1_STATUS between the enable=0 and enable=1 phases - "
                    f"the enable=1 check below would be satisfied by this leftover "
                    f"assertion instead of a fresh event"
                )

                # --- per-source enable ON: event must raise pm_interrupt ---
                await self.tb.write_register(PMACPIRegisterMap.PM1_ENABLE, enable_bit)
                await ClockCycles(self.tb.pclk, 5)
                seen_high = await self._trigger_and_sample(trigger)
                assert seen_high, (
                    f"pm_interrupt never asserted for PM1 source '{name}' "
                    f"even with PM1_ENABLE.{name}_en=1"
                )
                self.log.info(f"  PM1 source '{name}': gating verified")

            self.log.info("PASS: PM1_ENABLE per-source interrupt gating")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-4 FAILED: {e}")
            return False

    async def _trigger_pm1_tmr(self):
        """Force a PM timer overflow (whitebox - see module docstring)."""
        await RisingEdge(self.tb.core_clk)
        await self.tb.force_pm_timer_near_overflow(remaining_ticks=2)
        await ClockCycles(self.tb.core_clk, 3)

    async def _trigger_and_sample(self, trigger_coro, cycles: int = 40) -> bool:
        """Sample pm_interrupt for `cycles` pclk edges CONCURRENTLY with
        firing `trigger_coro()`, returning True if it was ever seen
        asserted.

        Earlier version awaited trigger_coro() to completion FIRST and only
        started sampling afterward - since pwrbtn/slpbtn/rtc/tmr triggers
        assert-then-release their stimulus internally (e.g.
        press_power_button holds for ~5 cycles then releases), the
        resulting pm1_int pulse (itself only ~1 cycle wide, since it is
        driven straight off the raw hardware event with none of the
        source's sticky-status defect (C2) in the way) had already come and
        gone by the time sampling began, making the "OFF" gating check
        pass for the wrong reason (it never observed a pulse either way)
        and the "ON" check fail with a misleading "never asserted" message
        even when the interrupt genuinely fired. Concurrent sampling
        (cocotb.start_soon) covers the whole trigger duration."""
        sample_task = cocotb.start_soon(self.tb.sample_pm_interrupt_over(cycles))
        await trigger_coro()
        samples = await sample_task
        return any(samples)

    # ------------------------------------------------------------------
    # 6. round_3 item 3 - pm_interrupt level, not pulse, for non-GPE terms
    # ------------------------------------------------------------------

    async def test_gh54_pm_interrupt_level_not_pulse(self) -> bool:
        """pm_interrupt must stay asserted while an enabled status bit is
        set, not pulse for one cycle off the raw hardware event."""
        self.log.info("Test: GH54-6 pm_interrupt level (timer overflow)")
        try:
            await self._clean_slate()
            await self.tb.write_register(PMACPIRegisterMap.ACPI_INT_ENABLE,
                                          PMACPIRegisterMap.INT_ENABLE_TIMER_OVF)
            await self.tb.configure_pm_timer(divider=0)
            await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            await RisingEdge(self.tb.core_clk)
            await self.tb.force_pm_timer_near_overflow(remaining_ticks=2)
            await ClockCycles(self.tb.core_clk, 3)  # let the overflow pulse land

            samples = await self.tb.sample_pm_interrupt_over(20, clock=self.tb.core_clk)
            high_count = sum(1 for s in samples if s)
            assert high_count >= 15, (
                f"pm_interrupt was asserted for only {high_count}/20 core-clock "
                f"cycles after an enabled timer-overflow event (with the status "
                f"bit not yet W1C'd) - expected it to stay asserted (level), "
                f"not pulse for ~1 cycle (GH#54 round_3 item 3: timer_ovf_int "
                f"is `status_timer_overflow && cfg_timer_ovf_enable`, and "
                f"status_timer_overflow is the raw one-cycle pm_timer_overflow "
                f"pulse, not a latched status bit). Samples: {samples}"
            )

            self.log.info(f"PASS: pm_interrupt level for {high_count}/20 cycles")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-6 FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # 7. round_2 item 4 - address decode aliasing / PSLVERR
    # ------------------------------------------------------------------

    async def test_gh54_address_alias_dropped_with_pslverr(self) -> bool:
        """Only the 21 mapped registers are software-visible. Every other
        address in the 4KB window - including the 7-bit alias at 0x080
        (which today hits ACPI_CONTROL) - must be dropped (write ignored,
        read 0) with PSLVERR, the same policy already used by
        ioapic/pic_8259/pit_8254."""
        self.log.info("Test: GH54-7 address decode aliasing / PSLVERR")
        try:
            await self._clean_slate()

            # Put a known, distinctive, nonzero value in ACPI_CONTROL so a
            # read-through-the-alias would return something recognizable,
            # and so a write-through-the-alias would visibly corrupt it.
            await self.tb.write_register(PMACPIRegisterMap.ACPI_CONTROL,
                                          PMACPIRegisterMap.CONTROL_ACPI_ENABLE)
            await ClockCycles(self.tb.pclk, 5)

            # Read the alias: 0x080 & 0x7F == 0x000 == ACPI_CONTROL.
            read_pkt, data = await self.tb.read_register(0x080)
            assert getattr(read_pkt, 'pslverr', 0) == 1, (
                "read from unmapped alias 0x080 (aliases ACPI_CONTROL via the "
                "7-bit PADDR[6:0] decode) did not raise PSLVERR (GH#54 round_2 "
                "item 4: cpuif_rd_err/readback_err is tied to 0 in the "
                "generated regblock)"
            )
            assert data == 0, (
                f"read from unmapped alias 0x080 returned 0x{data:08x} "
                f"(ACPI_CONTROL's live value), expected 0 (dropped, not "
                f"aliased through to ACPI_CONTROL)"
            )

            # Write the alias with a value that would clear acpi_enable if
            # it lands on the real ACPI_CONTROL - must NOT actually happen.
            write_pkt = await self.tb.write_register(0x080, 0x00000000)
            assert getattr(write_pkt, 'pslverr', 0) == 1, (
                "write to unmapped alias 0x080 did not raise PSLVERR"
            )
            await ClockCycles(self.tb.pclk, 5)
            _, control = await self.tb.read_register(PMACPIRegisterMap.ACPI_CONTROL)
            assert control & PMACPIRegisterMap.CONTROL_ACPI_ENABLE, (
                "write to unmapped alias 0x080 silently corrupted "
                "ACPI_CONTROL.acpi_enable - the address-decode aliasing bug "
                "let an out-of-map write reach a real register (GH#54 "
                "round_2 item 4)"
            )

            self.log.info("PASS: address alias 0x080 dropped with PSLVERR")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-7 FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # 8. round_2 item 6 / round_3 item 2 - CDC synchronizer functional guard
    # ------------------------------------------------------------------

    async def test_gh54_cdc_async_input_guard(self) -> bool:
        """Contract: a value driven on rtc_alarm from the pclk-domain
        testbench reaches the pm_clk-domain core and is correctly observed
        as a pm_interrupt pulse. This is a functional-only guard - cocotb
        cannot exercise metastability, so passing here does NOT prove
        rtc_alarm/ext_wake_n/gpe_events_in are metastability-safe under
        CDC_ENABLE=1, only that they are functionally wired through.
        Expected to PASS today (and after any future synchronizer add,
        which would only change latency, not functional correctness).
        History: round_2 item 6 / round_3 item 2 - none of these three
        inputs have a synchronizer at all (button inputs get a 3-flop
        sync); this guard exists to catch a future change accidentally
        breaking the functional path while that real silicon-level gap
        remains open."""
        self.log.info("Test: GH54-8 CDC async input functional guard")
        try:
            await self._clean_slate()
            await self.tb.write_register(PMACPIRegisterMap.ACPI_INT_ENABLE,
                                          PMACPIRegisterMap.INT_ENABLE_PM1)
            await self.tb.write_register(PMACPIRegisterMap.PM1_ENABLE,
                                          PMACPIRegisterMap.PM1_ENABLE_RTC)
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            # rtc_alarm: driven synchronously to pclk edges by trigger_rtc_alarm().
            seen_high = await self._trigger_and_sample(self.tb.trigger_rtc_alarm)
            assert seen_high, (
                "rtc_alarm asserted from the pclk-domain testbench never "
                "produced a pm_interrupt pulse - the signal did not reach "
                "the pm_clk-domain core"
            )

            self.log.info("PASS: rtc_alarm reaches the core without a synchronizer (functional-only)")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-8 FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # 9. round_3 item 4 - gpe_events_prev freeze while disabled
    # ------------------------------------------------------------------

    async def test_gh54_gpe_prev_no_freeze_spurious_edge(self) -> bool:
        """A GPE input toggled while GPE/ACPI is disabled, then left steady
        across a later enable, must NOT manufacture a spurious status bit."""
        self.log.info("Test: GH54-9 gpe_events_prev no freeze -> no spurious edge")
        try:
            await self._clean_slate(gpe=True)
            bit = 9

            # Start disabled, GPE input low.
            await self.tb.write_register(PMACPIRegisterMap.ACPI_CONTROL, 0)
            self.tb.dut.gpe_events.value = 0
            await ClockCycles(self.tb.pclk, 10)

            # While STILL disabled, raise the GPE input and hold it steady
            # (no edge visible to anything downstream of the disabled block).
            current = int(self.tb.dut.gpe_events.value)
            self.tb.dut.gpe_events.value = current | (1 << bit)
            await ClockCycles(self.tb.pclk, 20)

            # Now enable ACPI+GPE with the input already steady-high -
            # gpe_events_prev should already reflect the current input
            # (no real edge occurs at enable time).
            await self.tb.configure_gpe_enables(1 << bit)
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=True)
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            status = await self.tb.read_gpe_status()
            assert status == 0, (
                f"GPE0_STATUS read 0x{status:08X} after enabling GPE with "
                f"input bit {bit} already steady-high (no real edge) - "
                f"expected 0. gpe_events_prev froze at its pre-disable value "
                f"while cfg_gpe_enable was low, so re-enabling manufactured "
                f"a spurious edge on bit {bit} (GH#54 round_3 item 4)"
            )

            # Drop the input back low for hygiene before the next test.
            self.tb.dut.gpe_events.value = 0
            await ClockCycles(self.tb.pclk, 5)

            self.log.info("PASS: no spurious edge on re-enable")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-9 FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # 5. H5 - wake latch from S1/S3 by a pulsed source
    # ------------------------------------------------------------------

    async def test_gh54_pwrbtn_wake_latches_in_s0(self) -> bool:
        """Waking from S3 via a pulsed power-button press must land in S0
        and STAY there - not bounce back into S3 once the pulse is gone."""
        self.log.info("Test: GH54-5a power-button wake latches in S0")
        try:
            await self._clean_slate()
            await self.tb.write_register(PMACPIRegisterMap.WAKE_ENABLE,
                                          PMACPIRegisterMap.WAKE_ENABLE_PWRBTN)
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            await self.tb.request_sleep(sleep_type=3)  # -> S3
            state = await self._poll_power_state(PMACPIRegisterMap.POWER_STATE_S3)
            assert state == PMACPIRegisterMap.POWER_STATE_S3, (
                f"device did not reach S3 before the wake attempt (state={state})"
            )

            await self.tb.press_power_button()  # one-cycle wake pulse

            # Give the FSM plenty of time to settle, then confirm it is in
            # S0 and STAYS there (poll twice, spaced apart).
            await ClockCycles(self.tb.pclk, 30)
            state1 = await self.tb.get_current_power_state()
            await ClockCycles(self.tb.pclk, 20)
            state2 = await self.tb.get_current_power_state()

            assert state1 == PMACPIRegisterMap.POWER_STATE_S0, (
                f"power-button wake from S3 did not reach S0 (state=0x{state1:X} "
                f"after 30 cycles) - GH#54 H5: power_button_press is a "
                f"one-cycle pulse; PWR_TRANSITION re-samples the still-"
                f"programmed sleep_type after the pulse is gone and re-enters "
                f"sleep"
            )
            assert state2 == PMACPIRegisterMap.POWER_STATE_S0, (
                f"device woke to S0 but then bounced back to state=0x{state2:X} "
                f"(GH#54 H5: the wake is not latched, so the FSM re-enters "
                f"sleep once the one-cycle wake pulse is gone)"
            )

            self.log.info("PASS: power-button wake latched in S0")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-5a FAILED: {e}")
            return False
        finally:
            await self.tb.force_power_state_s0()

    async def test_gh54_level_wake_guard(self) -> bool:
        """Guard: a LEVEL wake source (ext_wake_n held low) already wakes
        S3 -> S0 correctly and stays there - only the pulsed power-button
        path is broken (GH#54 H5). Expected to PASS today; kept as a
        regression sentinel so a future fix cannot silently break the
        already-working level-wake path. Also serves as the round_2 item 6
        / round_3 item 2 CDC guard for ext_wake_n specifically."""
        self.log.info("Test: GH54-5b level wake (ext_wake_n) guard")
        try:
            await self._clean_slate()
            await self.tb.write_register(PMACPIRegisterMap.WAKE_ENABLE,
                                          PMACPIRegisterMap.WAKE_ENABLE_EXT)
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            await self.tb.request_sleep(sleep_type=3)  # -> S3
            state = await self._poll_power_state(PMACPIRegisterMap.POWER_STATE_S3)
            assert state == PMACPIRegisterMap.POWER_STATE_S3, (
                f"device did not reach S3 before the wake attempt (state={state})"
            )

            self.tb.dut.ext_wake_n.value = 0  # assert level wake
            await ClockCycles(self.tb.pclk, 30)
            state1 = await self.tb.get_current_power_state()
            self.tb.dut.ext_wake_n.value = 1
            await ClockCycles(self.tb.pclk, 20)
            state2 = await self.tb.get_current_power_state()

            assert state1 == PMACPIRegisterMap.POWER_STATE_S0, (
                f"level ext_wake_n did not wake S3 -> S0 (state=0x{state1:X})"
            )
            assert state2 == PMACPIRegisterMap.POWER_STATE_S0, (
                f"device drifted away from S0 after a level wake (state=0x{state2:X})"
            )

            self.log.info("PASS: level wake (ext_wake_n) guard")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-5b FAILED: {e}")
            return False
        finally:
            await self.tb.force_power_state_s0()

    async def _poll_power_state(self, expected: int, timeout_reads: int = 20) -> int:
        """Poll get_current_power_state() until it matches `expected` or
        `timeout_reads` reads elapse; returns the last-read state."""
        state = await self.tb.get_current_power_state()
        reads = 0
        while state != expected and reads < timeout_reads:
            await ClockCycles(self.tb.pclk, 5)
            state = await self.tb.get_current_power_state()
            reads += 1
        return state

    # ------------------------------------------------------------------
    # 3. H2 / round_3 item 1 - GPE interrupt deassert + sleep unblock
    # ------------------------------------------------------------------

    async def test_gh54_gpe_interrupt_deasserts_after_w1c(self) -> bool:
        """Contract: after an enabled GPE fires and software W1Cs its
        status bit, pm_interrupt DEASSERTS (no other sources enabled).

        History: H2 - pm_acpi_core's gpe_status_reg was set-only, with no
        clear path from the software W1C, so pm_interrupt latched forever.
        That gap is still open today, which is why this test intentionally,
        permanently sets gpe_status_reg bit `GH54_GPE_BIT` for the rest of
        the simulation as an unavoidable side effect - it must run after
        every other GPE test, and leaves GPE0_ENABLE at 0 on exit so the
        stuck core bit cannot reach gpe_int for anything that runs later."""
        self.log.info("Test: GH54-3a GPE interrupt deasserts after W1C")
        try:
            await self._clean_slate(gpe=True)
            bit = self.GH54_GPE_BIT
            await self.tb.write_register(PMACPIRegisterMap.ACPI_INT_ENABLE,
                                          PMACPIRegisterMap.INT_ENABLE_GPE)
            await self.tb.configure_gpe_enables(1 << bit)
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=True)
            await ClockCycles(self.tb.pclk, 10)

            await self.tb.inject_gpe_event(bit)
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            assert self.tb.get_pm_interrupt(), (
                f"pm_interrupt did not assert after an enabled GPE (bit {bit}) fired"
            )

            await self.tb.clear_gpe_status(1 << bit)
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            assert not self.tb.get_pm_interrupt(), (
                "pm_interrupt is still asserted after software W1C'd the GPE "
                "status bit that caused it - GH#54 H2: pm_acpi_core's "
                "gpe_status_reg is set-only (`gpe_status_reg <= gpe_status_reg "
                "| gpe_events_edge`), with no clear path from the software "
                "W1C on GPE0_STATUS_LO/HI, so gpe_int (and therefore "
                "pm_interrupt) latches until reset"
            )

            self.log.info("PASS: pm_interrupt deasserted after GPE W1C")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-3a FAILED: {e}")
            return False
        finally:
            # Neutralize the (permanently, core-level) stuck GPE bit so it
            # cannot reach gpe_int/pm_interrupt for anything running later.
            await self.tb.write_register(PMACPIRegisterMap.GPE0_ENABLE_LO, 0)
            await self.tb.write_register(PMACPIRegisterMap.GPE0_ENABLE_HI, 0)
            await self.tb.write_register(PMACPIRegisterMap.ACPI_INT_ENABLE, 0)

    async def test_gh54_gpe_sleep_unblocked_after_w1c(self) -> bool:
        """Contract: after an enabled GPE fires (as a wake source) and
        software W1Cs its status bit, a subsequent sleep request is
        honoured - the FSM actually leaves S0.

        History: round_3 item 1 - gpe_status_reg feeding any_wake_event
        whenever gpe_wake_en=1, with no clear path (H2), meant
        PWR_TRANSITION always resolved back to S0: sleep entry was blocked
        forever, not just the interrupt line. Uses a fresh GPE bit so it is
        independent of whatever test_gh54_gpe_interrupt_deasserts_after_w1c
        left stuck at the core level."""
        self.log.info("Test: GH54-3b GPE sleep unblocked after W1C")
        try:
            await self._clean_slate(gpe=True)
            bit = self.GH54_GPE_BIT_2
            await self.tb.write_register(PMACPIRegisterMap.WAKE_ENABLE,
                                          PMACPIRegisterMap.WAKE_ENABLE_GPE)
            await self.tb.configure_gpe_enables(1 << bit)
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=True)
            await ClockCycles(self.tb.pclk, 10)

            await self.tb.inject_gpe_event(bit)
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            await self.tb.clear_gpe_status(1 << bit)
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            await self.tb.request_sleep(sleep_type=3)  # attempt -> S3
            state = await self._poll_power_state(PMACPIRegisterMap.POWER_STATE_S3, timeout_reads=15)

            assert state == PMACPIRegisterMap.POWER_STATE_S3, (
                f"sleep request never resolved to S3 (last-read state=0x{state:X}) "
                f"after the triggering GPE (bit {bit}) was W1C'd - GH#54 round_3 "
                f"item 1: gpe_status_reg feeds any_wake_event whenever "
                f"gpe_wake_en=1 and is never actually cleared at the core "
                f"level (H2), so PWR_TRANSITION always resolves back to S0 "
                f"and sleep entry is permanently blocked, not just the "
                f"interrupt line"
            )

            self.log.info("PASS: sleep unblocked after GPE W1C")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-3b FAILED: {e}")
            return False
        finally:
            await self.tb.force_power_state_s0()
            await self.tb.write_register(PMACPIRegisterMap.GPE0_ENABLE_LO, 0)
            await self.tb.write_register(PMACPIRegisterMap.GPE0_ENABLE_HI, 0)
            await self.tb.write_register(PMACPIRegisterMap.WAKE_ENABLE, 0)

    GH54_GPE_BIT = 17
    GH54_GPE_BIT_2 = 25

    # ------------------------------------------------------------------
    # 10a. Follow-up item 2 - RESET_CTRL request pulses
    # ------------------------------------------------------------------

    async def test_gh54_reset_requests_are_one_cycle(self) -> bool:
        """Contract: writing RESET_CTRL.sys_reset (or .periph_reset)
        produces exactly one core-clock cycle of sys_reset_req (or
        periph_reset_req).

        History: H6 - sys_reset_req/periph_reset_req were hardwired to
        1'b0, so a RESET_CTRL write had zero effect outside the field's
        own auto-clear. The pending RTL follow-up wires these through the
        RESET_CTRL field storage (already auto-cleared to 0 the cycle
        after a write by pm_acpi_config_regs); this test additionally
        guards against the APB bridge presenting the write strobe for two
        cycles instead of one, which would hold the request high for two
        cycles instead of one."""
        self.log.info("Test: GH54-12 RESET_CTRL requests are exactly one cycle")
        try:
            await self._clean_slate()
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            for name, bit, signal in [
                ('sys', PMACPIRegisterMap.RESET_CTRL_SYS, self.tb.dut.sys_reset_req),
                ('periph', PMACPIRegisterMap.RESET_CTRL_PERIPH, self.tb.dut.periph_reset_req),
            ]:
                sample_task = cocotb.start_soon(
                    self.tb.sample_signal_over(signal, 40, clock=self.tb.core_clk))
                await self.tb.write_register(PMACPIRegisterMap.RESET_CTRL, bit)
                samples = await sample_task
                high_count = sum(1 for s in samples if s)

                assert high_count == 1, (
                    f"{name}_reset_req was high for {high_count} core-clock cycles "
                    f"after the RESET_CTRL.{name}_reset write (expected exactly 1) "
                    f"(GH#54 follow-up item 2). samples={samples}"
                )

            self.log.info("PASS: RESET_CTRL requests are one cycle each")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-12 FAILED: {e}")
            return False

    async def test_gh54_reset_control_basic_check(self) -> bool:
        """Runs PMACPIBasicTests.test_reset_control() (GH#54 follow-up F4)
        from inside the GH#54 suite.

        test_reset_control (renamed from test_external_wake, which
        previously wrote RESET_CTRL and returned True with no assertion at
        all) is intentionally NOT wired into run_basic_tests()'s shared
        basic_test_methods list: that list gates whether medium/full/GH#54
        run at all (pm_acpi_test() skips everything past basic on any
        basic failure), and this method is expected RED until GH#54 item 2
        lands - wiring it into the gate-level list would take the entire
        suite down with it. Running it here keeps its assertions actually
        exercised without that blast radius."""
        return await PMACPIBasicTests(self.tb).test_reset_control()

    # ------------------------------------------------------------------
    # 10b. Follow-up F4/F5 - RESET_STATUS sticky POR / soft_reset
    # ------------------------------------------------------------------

    async def test_gh54_reset_status_and_soft_reset(self) -> bool:
        """Contract:
        - RESET_STATUS.por_reset reads 1 after reset and STAYS 1 (a sticky
          level, not a single pulse).
        - Writing ACPI_CONTROL.soft_reset=1 makes RESET_STATUS.sw_reset
          read 1, clears every sticky status register (ACPI_STATUS,
          ACPI_INT_STATUS, PM1_STATUS, WAKE_STATUS) and GPE0_STATUS,
          clears the wake latch (a sleeping device returns to S0 and stays
          there), self-clears (ACPI_CONTROL.soft_reset reads back 0), and
          leaves configuration registers (PM1_ENABLE, GPE0_ENABLE_LO/HI,
          ...) intact.
        - RESET_STATUS.wdt_reset/ext_reset always read 0 - the module has
          no watchdog or external-reset input pins at all, so this is a
          documented "always 0" contract, not a defect under test.

        History: por_reset was `first_cycle`, a single-cycle pulse the
        very first clock after reset that normal APB latency always
        missed; ACPI_CONTROL.soft_reset was entirely unconnected to the
        core (H6), so writing it did nothing but auto-clear its own
        field."""
        self.log.info("Test: GH54-13 RESET_STATUS / soft_reset")
        try:
            # --- POR sticky: pulse a real local reset, then read RESET_STATUS ---
            await self.tb.assert_reset()
            await ClockCycles(self.tb.pclk, 10)
            await self.tb.deassert_reset()
            await ClockCycles(self.tb.pclk, 2)

            reset_status = await self.tb.read_reset_status()
            assert reset_status['por'], (
                f"RESET_STATUS.por_reset read 0 after a reset pulse (expected 1, "
                f"sticky) - full readback: {reset_status}"
            )
            assert not reset_status['watchdog'], (
                "RESET_STATUS.wdt_reset was not 0 (no watchdog input pin exists)")
            assert not reset_status['external'], (
                "RESET_STATUS.ext_reset was not 0 (no external-reset input pin exists)")

            # --- Configure known state with something for soft_reset to clear ---
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=True)
            await self.tb.write_register(PMACPIRegisterMap.PM1_ENABLE,
                                          PMACPIRegisterMap.PM1_ENABLE_TMR)
            await self.tb.configure_gpe_enables(1 << 4)
            await ClockCycles(self.tb.pclk, 5)

            await self.tb.press_power_button()
            await self.tb.inject_gpe_event(4)
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            # Put the device into S3 so soft_reset's wake-latch clear is meaningful.
            await self.tb.request_sleep(sleep_type=3)
            await self._poll_power_state(PMACPIRegisterMap.POWER_STATE_S3)

            # --- Trigger soft_reset ---
            await self.tb.write_register(
                PMACPIRegisterMap.ACPI_CONTROL,
                PMACPIRegisterMap.CONTROL_ACPI_ENABLE | PMACPIRegisterMap.CONTROL_GPE_ENABLE |
                PMACPIRegisterMap.CONTROL_SOFT_RESET)
            await ClockCycles(self.tb.pclk, SETTLE_CYCLES)

            reset_status = await self.tb.read_reset_status()
            assert reset_status['software'], (
                f"RESET_STATUS.sw_reset read 0 after ACPI_CONTROL.soft_reset was "
                f"written (expected 1) - full readback: {reset_status}"
            )

            acpi_status = await self.tb.read_acpi_status()
            assert not any(acpi_status.values()), (
                f"ACPI_STATUS was not cleared by soft_reset: {acpi_status}")
            pm1_status = await self.tb.read_pm1_status()
            assert not any(pm1_status.values()), (
                f"PM1_STATUS was not cleared by soft_reset: {pm1_status}")
            wake_status = await self.tb.read_wake_status()
            assert not any(wake_status.values()), (
                f"WAKE_STATUS was not cleared by soft_reset: {wake_status}")
            gpe_status = await self.tb.read_gpe_status()
            assert gpe_status == 0, (
                f"GPE0_STATUS was not cleared by soft_reset: 0x{gpe_status:08X}")

            state = await self.tb.get_current_power_state()
            assert state == PMACPIRegisterMap.POWER_STATE_S0, (
                f"power state did not return to S0 after soft_reset (state=0x{state:X})")
            await ClockCycles(self.tb.pclk, 20)
            state2 = await self.tb.get_current_power_state()
            assert state2 == PMACPIRegisterMap.POWER_STATE_S0, (
                f"power state drifted away from S0 after soft_reset (state=0x{state2:X})")

            _, control = await self.tb.read_register(PMACPIRegisterMap.ACPI_CONTROL)
            assert not (control & PMACPIRegisterMap.CONTROL_SOFT_RESET), (
                f"ACPI_CONTROL.soft_reset did not self-clear: 0x{control:02X}")

            # Configuration must survive a soft_reset.
            _, pm1_enable = await self.tb.read_register(PMACPIRegisterMap.PM1_ENABLE)
            assert pm1_enable == PMACPIRegisterMap.PM1_ENABLE_TMR, (
                f"PM1_ENABLE was disturbed by soft_reset (expected it to survive "
                f"as configuration, not status): 0x{pm1_enable:02X}"
            )
            _, gpe_enable_lo = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_LO)
            assert gpe_enable_lo == (1 << 4), (
                f"GPE0_ENABLE_LO was disturbed by soft_reset (expected it to "
                f"survive as configuration, not status): 0x{gpe_enable_lo:04X}"
            )

            self.log.info("PASS: RESET_STATUS / soft_reset")
            return True
        except AssertionError as e:
            self.log.error(f"GH54-13 FAILED: {e}")
            return False
        finally:
            await self.tb.force_power_state_s0()
            await self.tb.write_register(PMACPIRegisterMap.GPE0_ENABLE_LO, 0)
            await self.tb.write_register(PMACPIRegisterMap.GPE0_ENABLE_HI, 0)
            await self.tb.write_register(PMACPIRegisterMap.WAKE_ENABLE, 0)
            await self.tb.write_register(PMACPIRegisterMap.PM1_ENABLE, 0)
