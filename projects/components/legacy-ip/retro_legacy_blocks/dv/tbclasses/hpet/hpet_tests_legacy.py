# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: HPETLegacyTests
# Purpose: HPET LegacyReplacement Route tests (RLB/hpet TASK-003)
#
# Documentation: projects/components/retro_legacy_blocks/rtl/hpet/README.md
# Subsystem: hpet
#
# Author: sean galloway
# Created: 2026-09-28

"""
HPET LegacyReplacement Route Tests (RLB/hpet TASK-003)

The spec's LegacyReplacement Route REPLACES the delivery of timers 0 and 1
rather than adding to it: while HPET_CONFIG.legacy_replacement is set, timer 0
leaves on legacy_irq0 (IRQ0, standing in for 8254 PIT channel 0), timer 1 on
legacy_irq8 (IRQ8, standing in for the RTC periodic interrupt), and BOTH are
suppressed on timer_irq. Timers 2 and above are untouched.

Every scenario here is run TWICE, once with legacy mode OFF and once ON, and
asserts both directions: the legacy output must stay low when the mode is off,
and timer_irq must stay low when it is on. A test that only checked the ON case
would pass against RTL that ignored the mode bit entirely and simply asserted
both outputs, which is the most likely way to get this wrong.
"""

from typing import Tuple
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import Timer

from .hpet_tb import HPETTB, HPETRegisterMap


class HPETLegacyTests:
    """HPET legacy replacement routing test suite."""

    # HPET_CONFIG bit values, spelled out so the intent is readable at the
    # call site rather than being two magic bits.
    CFG_ENABLE = 1 << 0
    CFG_LEGACY = 1 << HPETRegisterMap.CONFIG_LEGACY_REPLACEMENT

    # SIM-TIME BUDGET, not an arbitrary number. This suite fires a one-shot
    # five times (timer 0 off/on, timer 1 off/on, status), and the FULL level
    # runs it on top of the medium and full suites in one cocotb test with a
    # single timeout. At 1000 ticks and the non-CDC 20 ns period that is ~20 us
    # per fire, ~100 us for the suite, which pushed the 2-timer FULL cell past
    # its 400 us timeout. Nothing here needs a long count-up -- the checks are
    # "which output carried the fire", not timing accuracy -- so keep this
    # small. test_apb4_hpet.py's header records the same budget hazard.
    COMPARE_TICKS = 200

    def __init__(self, tb: HPETTB):
        self.tb = tb
        self.log = tb.log

    async def _quiesce(self):
        """Halt the counter, disarm every timer, clear status AND legacy mode.

        Leaving legacy_replacement set would suppress timers 0 and 1 on
        timer_irq for every test that runs afterwards, so clearing it is not
        tidiness -- it is what keeps this suite from corrupting the next one.
        """
        await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)
        for t in range(self.tb.NUM_TIMERS):
            await self.tb.write_register(
                HPETRegisterMap.get_timer_config_addr(t), 0x00000000)
        await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 0xFFFFFFFF)
        await self.tb.wait_apb_idle()

    async def _fire_one_shot(self, timer_id: int, legacy: bool,
                             compare: int = None) -> Tuple[bool, bool, bool]:
        """Arm timer_id as a one-shot and wait for it to fire.

        Returns (timer_irq_seen, legacy_irq0_seen, legacy_irq8_seen) -- sampled
        as a LATCHED "did this ever assert", not an instantaneous read, because
        one-shot deliveries are cleared by the status write and a single poll can
        land either side of the pulse.
        """
        if compare is None:
            compare = self.COMPARE_TICKS
        await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)
        await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
        await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)
        await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 0xFFFFFFFF)

        cfg = (1 << HPETRegisterMap.TIMER_INT_ENABLE)      # one-shot: TYPE = 0
        await self.tb.write_register(
            HPETRegisterMap.get_timer_comp_lo_addr(timer_id), compare)
        await self.tb.write_register(
            HPETRegisterMap.get_timer_comp_hi_addr(timer_id), 0x00000000)
        await self.tb.write_register(
            HPETRegisterMap.get_timer_config_addr(timer_id), cfg)

        run = self.CFG_ENABLE | (self.CFG_LEGACY if legacy else 0)
        await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, run)

        seen_timer = False
        seen_l0 = False
        seen_l8 = False
        start = get_sim_time('ns')
        while (get_sim_time('ns') - start) < self.tb.INTERRUPT_TIMEOUT:
            if self.tb.timer_interrupt_state[timer_id]:
                seen_timer = True
            if self.tb.legacy_irq_state[0]:
                seen_l0 = True
            if self.tb.legacy_irq_state[1]:
                seen_l8 = True
            if seen_timer or seen_l0 or seen_l8:
                break
            await Timer(10, units="ns")

        # Give the delivery a few more samples so a route that asserts a cycle
        # later than the one we noticed is still observed, then stop the block.
        for _ in range(10):
            if self.tb.timer_interrupt_state[timer_id]:
                seen_timer = True
            if self.tb.legacy_irq_state[0]:
                seen_l0 = True
            if self.tb.legacy_irq_state[1]:
                seen_l8 = True
            await Timer(10, units="ns")

        await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)
        await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 0xFFFFFFFF)
        await self.tb.wait_apb_idle()
        return seen_timer, seen_l0, seen_l8

    async def test_legacy_route_timer0(self) -> bool:
        """Timer 0: normal delivery with legacy off, legacy_irq0 with it on."""
        self.log.info("=== RLB/hpet TASK-003: timer 0 legacy route (IRQ0) ===")
        self.tb.test_phase = "LEGACY_ROUTE_T0"
        passed = True
        try:
            await self._quiesce()

            # OFF: the parameter's off-state needs its own assertion, or RTL
            # that ignores the mode bit passes the on-case unnoticed.
            t_irq, l0, l8 = await self._fire_one_shot(0, legacy=False)
            self.log.info(f"legacy OFF: timer_irq[0]={t_irq} legacy_irq0={l0} "
                          f"legacy_irq8={l8}")
            if not t_irq:
                self.log.error("legacy OFF: timer 0 did not deliver on timer_irq[0]")
                passed = False
            if l0 or l8:
                self.log.error("legacy OFF: a legacy route asserted with "
                               "legacy_replacement clear")
                passed = False

            # ON: delivery MOVES to legacy_irq0 and timer_irq[0] stays quiet.
            t_irq, l0, l8 = await self._fire_one_shot(0, legacy=True)
            self.log.info(f"legacy ON : timer_irq[0]={t_irq} legacy_irq0={l0} "
                          f"legacy_irq8={l8}")
            if not l0:
                self.log.error("legacy ON: timer 0 did not deliver on legacy_irq0")
                passed = False
            if t_irq:
                self.log.error("legacy ON: timer_irq[0] still asserted -- the "
                               "spec REPLACES timer 0's delivery, it does not "
                               "duplicate it")
                passed = False
            if l8:
                self.log.error("legacy ON: legacy_irq8 asserted for a timer 0 fire")
                passed = False

            await self._quiesce()
            return passed
        except Exception as e:
            self.log.error(f"timer 0 legacy route test failed: {e}")
            await self._quiesce()
            return False

    async def test_legacy_route_timer1(self) -> bool:
        """Timer 1: legacy_irq8 (the RTC replacement) with legacy mode on."""
        if self.tb.NUM_TIMERS < 2:
            self.log.warning("NUM_TIMERS < 2: no timer 1 to replace the RTC with")
            return True
        self.log.info("=== RLB/hpet TASK-003: timer 1 legacy route (IRQ8) ===")
        self.tb.test_phase = "LEGACY_ROUTE_T1"
        passed = True
        try:
            await self._quiesce()

            t_irq, l0, l8 = await self._fire_one_shot(1, legacy=False)
            self.log.info(f"legacy OFF: timer_irq[1]={t_irq} legacy_irq0={l0} "
                          f"legacy_irq8={l8}")
            if not t_irq:
                self.log.error("legacy OFF: timer 1 did not deliver on timer_irq[1]")
                passed = False
            if l0 or l8:
                self.log.error("legacy OFF: a legacy route asserted with "
                               "legacy_replacement clear")
                passed = False

            t_irq, l0, l8 = await self._fire_one_shot(1, legacy=True)
            self.log.info(f"legacy ON : timer_irq[1]={t_irq} legacy_irq0={l0} "
                          f"legacy_irq8={l8}")
            if not l8:
                self.log.error("legacy ON: timer 1 did not deliver on legacy_irq8")
                passed = False
            if t_irq:
                self.log.error("legacy ON: timer_irq[1] still asserted -- timer 1's "
                               "delivery must MOVE to legacy_irq8")
                passed = False
            if l0:
                self.log.error("legacy ON: legacy_irq0 asserted for a timer 1 fire")
                passed = False

            await self._quiesce()
            return passed
        except Exception as e:
            self.log.error(f"timer 1 legacy route test failed: {e}")
            await self._quiesce()
            return False

    async def test_legacy_leaves_other_timers_alone(self) -> bool:
        """Timers 2+ keep delivering on timer_irq even in legacy mode."""
        if self.tb.NUM_TIMERS < 3:
            self.log.warning("NUM_TIMERS < 3: no timer above the legacy pair")
            return True
        self.log.info("=== RLB/hpet TASK-003: timer 2 unaffected by legacy mode ===")
        self.tb.test_phase = "LEGACY_OTHER_TIMERS"
        passed = True
        try:
            await self._quiesce()
            t_irq, l0, l8 = await self._fire_one_shot(2, legacy=True)
            self.log.info(f"legacy ON, timer 2: timer_irq[2]={t_irq} "
                          f"legacy_irq0={l0} legacy_irq8={l8}")
            if not t_irq:
                self.log.error("legacy ON: timer 2 stopped delivering on "
                               "timer_irq[2] -- only timers 0 and 1 are replaced")
                passed = False
            if l0 or l8:
                self.log.error("legacy ON: timer 2 leaked onto a legacy route")
                passed = False
            await self._quiesce()
            return passed
        except Exception as e:
            self.log.error(f"other-timer legacy test failed: {e}")
            await self._quiesce()
            return False

    async def test_legacy_status_is_not_masked(self) -> bool:
        """GINTR_STA still reports timer 0 while it is delivered as IRQ0.

        The status bit is deliberately NOT masked by legacy mode: only the
        DELIVERY path moves, so software polling status sees the same thing
        either way. A driver that polls instead of taking the interrupt must
        keep working.
        """
        self.log.info("=== RLB/hpet TASK-003: status unmasked in legacy mode ===")
        self.tb.test_phase = "LEGACY_STATUS"
        try:
            await self._quiesce()

            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0)
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 0xFFFFFFFF)
            await self.tb.write_register(
                HPETRegisterMap.get_timer_comp_lo_addr(0), self.COMPARE_TICKS)
            await self.tb.write_register(
                HPETRegisterMap.get_timer_comp_hi_addr(0), 0)
            await self.tb.write_register(
                HPETRegisterMap.get_timer_config_addr(0),
                1 << HPETRegisterMap.TIMER_INT_ENABLE)
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG,
                                         self.CFG_ENABLE | self.CFG_LEGACY)

            status = 0
            start = get_sim_time('ns')
            while (get_sim_time('ns') - start) < self.tb.INTERRUPT_TIMEOUT:
                _, status = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
                if status & 0x1:
                    break
                await Timer(20, units="ns")

            self.log.info(f"HPET_STATUS in legacy mode = 0x{status:08X}")
            passed = True
            if not (status & 0x1):
                self.log.error("legacy ON: HPET_STATUS[0] never set -- the sticky "
                               "status must behave identically in both modes; only "
                               "the delivery path moves")
                passed = False

            await self._quiesce()
            return passed
        except Exception as e:
            self.log.error(f"legacy status test failed: {e}")
            await self._quiesce()
            return False

    async def run_all_legacy_tests(self) -> bool:
        """Run the LegacyReplacement Route suite (RLB/hpet TASK-003)."""
        self.log.info(f"=== Running All HPET Legacy Tests "
                      f"({self.tb.NUM_TIMERS} timers) ===")

        tests = [
            ("Legacy route timer 0 -> IRQ0", self.test_legacy_route_timer0()),
            ("Legacy route timer 1 -> IRQ8", self.test_legacy_route_timer1()),
            ("Legacy leaves timers 2+ alone",
             self.test_legacy_leaves_other_timers_alone()),
            ("Legacy status unmasked", self.test_legacy_status_is_not_masked()),
        ]

        results = []
        for test_name, test_coro in tests:
            self.log.info(f"Running {test_name}...")
            try:
                result = await test_coro
                results.append(result)
                self.tb.scoreboard.record_test(test_name, result)
                status = "PASS" if result else "FAIL"
                self.log.info(f"{test_name}: {status}")
            except Exception as e:
                self.log.error(f"{test_name} failed with exception: {e}")
                results.append(False)
                self.tb.scoreboard.record_test(test_name, False)

        all_passed = all(results)
        self.log.info(f"=== Legacy tests: {sum(results)}/{len(results)} passed ===")
        return all_passed
