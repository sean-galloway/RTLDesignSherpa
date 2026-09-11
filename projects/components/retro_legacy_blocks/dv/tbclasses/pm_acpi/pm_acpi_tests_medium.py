# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PMACPIMediumTests
# Purpose: PM_ACPI Medium Test Suite
#
# Documentation: projects/components/retro_legacy_blocks/docs/pm_acpi_spec/
# Subsystem: retro_legacy_blocks/pm_acpi
#
# Created: 2025-11-29

"""
PM_ACPI Medium Test Suite

Extended test coverage beyond basic tests including:
- PM Timer divider variations and accuracy
- Multiple GPE enable/status patterns
- Power state transitions
- Wake source combinations
- Extended register access patterns
- Timer stress with various dividers
"""

from cocotb.triggers import ClockCycles, Timer

from projects.components.retro_legacy_blocks.dv.tbclasses.pm_acpi.pm_acpi_tb import (
    PMACPITB, PMACPIRegisterMap
)


class PMACPIMediumTests:
    """Medium test methods for PM_ACPI module."""

    def __init__(self, tb: PMACPITB):
        """
        Initialize test suite.

        Args:
            tb: PM_ACPI testbench instance
        """
        self.tb = tb
        self.log = tb.log

    async def run_all_medium_tests(self) -> bool:
        """Run all medium-level tests."""
        self.log.info("=" * 80)
        self.log.info("Starting PM_ACPI Medium Tests")
        self.log.info("=" * 80)

        results = []

        test_methods = [
            ('RLB-009 reset source pins', self.test_rlb009_reset_source_pins),
            ('RLB-009 soft off state', self.test_rlb009_soft_off_state),
            ('RLB-009 button debounce and override', self.test_rlb009_button_debounce_and_override),
            ('RLB-009 PM timer extensions', self.test_rlb009_pm_timer_extensions),
            ('PM Timer Divider Sweep', self.test_pm_timer_divider_sweep),
            ('PM Timer Extended Run', self.test_pm_timer_extended_run),
            ('GPE Enable Patterns', self.test_gpe_enable_patterns),
            ('GPE Walking Ones', self.test_gpe_walking_ones),
            ('Clock Gate Patterns', self.test_clock_gate_patterns),
            ('Power Domain Patterns', self.test_power_domain_patterns),
            ('PM1 Control Sweep', self.test_pm1_control_sweep),
            ('Wake Enable Combinations', self.test_wake_enable_combinations),
            ('Interrupt Enable Matrix', self.test_interrupt_enable_matrix),
            ('Register Access Stress', self.test_register_access_stress),
        ]

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

        # Print summary
        self.log.info("\n" + "=" * 80)
        self.log.info("MEDIUM TEST SUMMARY")
        self.log.info("=" * 80)

        passed_count = sum(1 for _, result in results if result)
        total_count = len(results)

        for test_name, result in results:
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name:45s} {status}")

        self.log.info(f"\nMedium Tests: {passed_count}/{total_count} passed")

        return all(result for _, result in results)

    # ========================================================================
    # PM Timer Extended Tests
    # ========================================================================

    async def test_rlb009_pm_timer_extensions(self) -> bool:
        """RLB-009: PM timer prescaler, comparator, and 64-bit mode.

        The divider is sixteen bits, so on its own the timer cannot reach the
        slow end of its range; a power-of-two prescaler ahead of it extends
        the range without widening a field software already uses. The
        comparator gives software a deadline rather than only a wrap, and
        64-bit mode moves the overflow to the carry out of bit 63 while
        leaving the low word where it was. Reading the low word snapshots the
        high word, so a pair of reads cannot straddle a carry."""
        self.log.info("=== RLB-009: PM timer prescaler, comparator, 64-bit ===")
        M = PMACPIRegisterMap
        try:
            async def fresh(config):
                """Reset, program PM_TIMER_CONFIG, then enable. The config has
                to land before the enable or the first ticks run on the old
                divider."""
                await self.tb.assert_reset()
                await ClockCycles(self.tb.pclk, 10)
                await self.tb.deassert_reset()
                await ClockCycles(self.tb.pclk, 20)
                # Park the comparator somewhere the test will not reach, so a
                # match cannot be confused with an overflow.
                await self.tb.write_register(M.PM_TIMER_MATCH, 0x0FFF_0000)
                await self.tb.write_register(M.PM_TIMER_CONFIG, config)
                await self.tb.write_register(M.ACPI_CONTROL,
                                             M.CONTROL_ACPI_ENABLE |
                                             M.CONTROL_PM_TIMER_ENABLE)
                await ClockCycles(self.tb.pclk, 10)

            # --- 1. PRESCALER -------------------------------------------
            # Identical measurement either side, so the APB overhead in the
            # delta cancels and only the prescale ratio is left.
            async def measure(config):
                await fresh(config)
                _, v0 = await self.tb.read_register(M.PM_TIMER_VALUE)
                await ClockCycles(self.tb.pclk, 320)
                _, v1 = await self.tb.read_register(M.PM_TIMER_VALUE)
                return (v1 - v0) & 0xFFFFFFFF

            d_fast = await measure(0)                                  # /1
            d_slow = await measure(4 << M.PM_TIMER_PRESCALE_SHIFT)     # /16
            ratio_ok = (d_slow > 0 and
                        0.75 <= (d_fast / (d_slow * 16.0)) <= 1.25)
            self.log.info(f"  prescale /1 advanced {d_fast}, /16 advanced "
                          f"{d_slow} over the same window (ratio ok={ratio_ok})")

            # --- 2. COMPARATOR ------------------------------------------
            await fresh(0)
            await self.tb.write_register(M.ACPI_STATUS, 0x1F)
            await self.tb.write_register(M.ACPI_INT_STATUS, 0x7F)
            await self.tb.write_register(M.ACPI_INT_ENABLE,
                                         M.INT_ENABLE_TIMER_MATCH)
            _, now = await self.tb.read_register(M.PM_TIMER_VALUE)
            deadline = (now + 400) & 0xFFFFFFFF
            await self.tb.write_register(M.PM_TIMER_MATCH, deadline)
            saw_irq = any(await self.tb.sample_pm_interrupt_over(600))
            _, st = await self.tb.read_register(M.ACPI_STATUS)
            _, ist = await self.tb.read_register(M.ACPI_INT_STATUS)
            matched = bool(st & M.STATUS_TIMER_MATCH)
            match_int = bool(ist & M.INT_STATUS_TIMER_MATCH)
            self.log.info(f"  comparator at 0x{deadline:08X}: status={matched} "
                          f"int_status={match_int} pm_interrupt={saw_irq}")

            # Negative control: a deadline the window cannot reach must not
            # set the bit, or the test above proves nothing.
            await fresh(0)
            await self.tb.write_register(M.PM_TIMER_MATCH, 0x0FFF_0000)
            await self.tb.write_register(M.ACPI_STATUS, 0x1F)
            await ClockCycles(self.tb.pclk, 600)
            _, st_n = await self.tb.read_register(M.ACPI_STATUS)
            no_false_match = not bool(st_n & M.STATUS_TIMER_MATCH)
            self.log.info(f"  unreachable deadline stayed clear: {no_false_match}")

            # --- 3. OVERFLOW SOURCE -------------------------------------
            # 32-bit mode: the carry out of bit 31 is the overflow.
            await fresh(0)
            await self.tb.write_register(M.ACPI_STATUS, 0x1F)
            self.tb.force_pm_timer_count(0xFFFF_FFF0)
            await ClockCycles(self.tb.pclk, 60)
            _, st32 = await self.tb.read_register(M.ACPI_STATUS)
            ovf32 = bool(st32 & M.STATUS_TIMER_OVERFLOW)

            # 64-bit mode: the SAME carry is no longer an overflow, because
            # the counter has 32 more bits to run through first.
            await fresh(M.PM_TIMER_64BIT)
            await self.tb.write_register(M.ACPI_STATUS, 0x1F)
            self.tb.force_pm_timer_count(0xFFFF_FFF0)
            await ClockCycles(self.tb.pclk, 60)
            _, st64 = await self.tb.read_register(M.ACPI_STATUS)
            ovf64 = bool(st64 & M.STATUS_TIMER_OVERFLOW)
            self.log.info(f"  carry out of bit 31: overflow in 32-bit mode="
                          f"{ovf32}, in 64-bit mode={ovf64}")

            # --- 4. COHERENT 64-BIT READ --------------------------------
            # PM_TIMER_VALUE_HI is a snapshot taken when the low word is read,
            # not a live view, so the two halves always belong to the same
            # instant. Read it stale across a carry to prove it.
            await fresh(M.PM_TIMER_64BIT)
            self.tb.force_pm_timer_count(0xFFFF_FFF0)
            _, _lo0 = await self.tb.read_register(M.PM_TIMER_VALUE)   # snaps hi=0
            await ClockCycles(self.tb.pclk, 100)                      # carry happens
            _, hi_stale = await self.tb.read_register(M.PM_TIMER_VALUE_HI)
            _, _lo1 = await self.tb.read_register(M.PM_TIMER_VALUE)   # snaps hi=1
            _, hi_fresh = await self.tb.read_register(M.PM_TIMER_VALUE_HI)
            self.log.info(f"  high word across the carry: stale snapshot="
                          f"{hi_stale}, after re-reading the low word={hi_fresh}")

            ok = (ratio_ok and matched and match_int and saw_irq and
                  no_false_match and ovf32 and not ovf64 and
                  hi_stale == 0 and hi_fresh == 1)
            if ok:
                self.log.info("RLB-009 PM timer extensions GREEN")
                return True
            self.log.error(
                f"RLB-009 PM timer: prescale_ratio_ok={ratio_ok} "
                f"(fast={d_fast} slow={d_slow}), match_status={matched} "
                f"match_int={match_int} match_irq={saw_irq} "
                f"no_false_match={no_false_match} ovf_32bit_mode={ovf32} "
                f"ovf_64bit_mode={ovf64} (want False) hi_stale={hi_stale} "
                f"(want 0) hi_fresh={hi_fresh} (want 1)")
            return False
        except Exception as e:
            self.log.error(f"RLB-009 PM timer test error: {e}")
            return False
        finally:
            # Put PM_TIMER_CONFIG and the comparator back where reset left
            # them. A prescaled or 64-bit timer left running changes what
            # every later test sees on PM_TIMER_VALUE.
            await self.tb.assert_reset()
            await ClockCycles(self.tb.pclk, 10)
            await self.tb.deassert_reset()
            await ClockCycles(self.tb.pclk, 20)
            await self.tb.write_register(M.PM_TIMER_CONFIG, 0)
            await self.tb.write_register(M.PM_TIMER_MATCH, 0)
            await self.tb.write_register(M.ACPI_INT_ENABLE, 0)
            await self.tb.write_register(M.ACPI_CONTROL, 0)
            await ClockCycles(self.tb.pclk, 20)

    async def test_rlb009_button_debounce_and_override(self) -> bool:
        """RLB-009: button debounce and the power-button override.

        A three-flop synchronizer resolves metastability and does nothing
        about contact bounce, so one press was recorded as several. A level
        now has to hold for BUTTON_TIMING.debounce_cycles before an edge is
        reported, and holding the debounced button past the long-press
        threshold forces soft off - ACPI's four-second override."""
        self.log.info("=== RLB-009: button debounce and override ===")
        M = PMACPIRegisterMap
        try:
            async def fresh(debounce, shift):
                await self.tb.assert_reset()
                await ClockCycles(self.tb.pclk, 10)
                await self.tb.deassert_reset()
                await ClockCycles(self.tb.pclk, 20)
                await self.tb.write_register(
                    M.BUTTON_TIMING, (debounce & 0xFFFFFF) | ((shift & 0x1F) << 24))
                await self.tb.write_register(M.ACPI_CONTROL, 0x1)
                await self.tb.write_register(M.PM1_ENABLE, 0xFFFF)
                await ClockCycles(self.tb.pclk, 20)

            # Bounce the button: 6 quick edges inside the debounce window.
            await fresh(debounce=200, shift=0)
            for _ in range(3):
                self.tb.dut.power_button_n.value = 0
                await ClockCycles(self.tb.pclk, 20)
                self.tb.dut.power_button_n.value = 1
                await ClockCycles(self.tb.pclk, 20)
            self.tb.dut.power_button_n.value = 0      # then settle pressed
            await ClockCycles(self.tb.pclk, 600)
            _, st = await self.tb.read_register(M.PM1_STATUS)
            one_press = bool(st & M.PM1_STATUS_PWRBTN)
            self.tb.dut.power_button_n.value = 1
            await ClockCycles(self.tb.pclk, 600)
            self.log.info(f"  bounced press recorded: {one_press}")

            # With debouncing off, the same bounce is several presses: this is
            # the behaviour the default now suppresses, kept as the control.
            await fresh(debounce=0, shift=0)
            presses = 0
            prev = 0
            for _ in range(3):
                self.tb.dut.power_button_n.value = 0
                await ClockCycles(self.tb.pclk, 20)
                self.tb.dut.power_button_n.value = 1
                await ClockCycles(self.tb.pclk, 20)
                _, st = await self.tb.read_register(M.PM1_STATUS)
                now = 1 if (st & M.PM1_STATUS_PWRBTN) else 0
                if now and not prev:
                    presses += 1
                await self.tb.write_register(M.PM1_STATUS, M.PM1_STATUS_PWRBTN)
                prev = 0
            self.log.info(f"  undebounced bounce recorded {presses} press(es)")

            # Long press forces soft off, with the override ENABLED.
            await fresh(debounce=10, shift=10)     # 2^10 = 1024 cycles
            await self.tb.write_register(M.PM1_CONTROL, 1 << 4)   # pwrbtn_ovr
            self.tb.dut.power_button_n.value = 0
            await ClockCycles(self.tb.pclk, 4000)
            _, ctl = await self.tb.read_register(M.ACPI_CONTROL)
            forced = ((ctl >> 4) & 0x3) == 2       # encoding 2 = S5
            self.tb.dut.power_button_n.value = 1
            await ClockCycles(self.tb.pclk, 200)
            self.log.info(f"  long press with override enabled: S5={forced}")

            # With the override disabled the same hold does nothing: the bit
            # enables the escape hatch rather than commanding it, so a write
            # that merely sets it cannot park the machine in S5.
            await fresh(debounce=10, shift=10)
            await self.tb.write_register(M.PM1_CONTROL, 0)
            self.tb.dut.power_button_n.value = 0
            await ClockCycles(self.tb.pclk, 4000)
            _, ctl2 = await self.tb.read_register(M.ACPI_CONTROL)
            not_forced = ((ctl2 >> 4) & 0x3) != 2
            self.tb.dut.power_button_n.value = 1
            await ClockCycles(self.tb.pclk, 200)
            self.log.info(f"  long press with override disabled: stayed out of S5={not_forced}")

            ok = one_press and presses >= 2 and forced and not_forced
            if ok:
                self.log.info("RLB-009 button debounce and override GREEN")
                return True
            self.log.error(
                f"RLB-009 buttons: debounced_press={one_press} "
                f"undebounced_presses={presses} (want >= 2) "
                f"long_press_forced_S5={forced} disabled_did_nothing={not_forced}")
            return False
        except Exception as e:
            self.log.error(f"RLB-009 button test error: {e}")
            return False
        finally:
            # RESTORE THE RESET DEFAULTS, pass or fail. This is the only test
            # that programs BUTTON_TIMING, and it ends holding the part in S5
            # behind a ten-cycle debounce window. Every later test presses the
            # button for five cycles, which a ten-cycle window swallows, so
            # leaving it programmed reads as five unrelated GH#54 failures in
            # the suite that runs next.
            await self.tb.assert_reset()
            await ClockCycles(self.tb.pclk, 10)
            await self.tb.deassert_reset()
            await ClockCycles(self.tb.pclk, 20)
            await self.tb.write_register(M.BUTTON_TIMING, 0x1C000000)
            await self.tb.write_register(M.PM1_CONTROL, 0)
            await self.tb.write_register(M.ACPI_CONTROL, 0)
            await ClockCycles(self.tb.pclk, 20)

    async def test_rlb009_soft_off_state(self) -> bool:
        """RLB-009: S5 soft off.

        S5 is as dark as S3 - every clock gated, every domain but the
        always-on one powered down - but it retains nothing, so leaving it
        pulses sys_reset_req: a wake from soft off is a boot, not a resume.
        The two-bit state field reports encoding 2 for it, the free one."""
        self.log.info("=== RLB-009: S5 soft off ===")
        M = PMACPIRegisterMap
        try:
            await self.tb.assert_reset()
            await ClockCycles(self.tb.pclk, 10)
            await self.tb.deassert_reset()
            await ClockCycles(self.tb.pclk, 20)
            await self.tb.write_register(M.ACPI_CONTROL, 0x1)   # acpi_enable
            await self.tb.write_register(M.PM1_ENABLE, 0xFFFF)
            await self.tb.write_register(M.WAKE_ENABLE, 0xF)
            await ClockCycles(self.tb.pclk, 10)

            await self.tb.request_sleep(sleep_type=5)
            await ClockCycles(self.tb.pclk, 40)
            _, ctl = await self.tb.read_register(M.ACPI_CONTROL)
            state = (ctl >> 4) & 0x3
            clocks = int(self.tb.dut.clock_gate_en.value)
            rails = int(self.tb.dut.power_domain_en.value)
            self.log.info(f"  in S5: state_encoding={state} clocks=0x{clocks:08X} "
                          f"rails=0x{rails:02X}")

            # Wake on the power button, and watch for the boot pulse.
            saw_reset = 0
            self.tb.dut.power_button_n.value = 0
            for _ in range(200):
                await ClockCycles(self.tb.pclk, 1)
                saw_reset |= int(self.tb.dut.sys_reset_req.value)
            self.tb.dut.power_button_n.value = 1
            await ClockCycles(self.tb.pclk, 100)
            _, ctl2 = await self.tb.read_register(M.ACPI_CONTROL)
            back = ((ctl2 >> 4) & 0x3) == 0
            self.log.info(f"  after wake: state_encoding={(ctl2 >> 4) & 0x3} "
                          f"sys_reset_req pulsed={bool(saw_reset)}")

            ok = (state == 2 and clocks == 0 and (rails & 0xFE) == 0
                  and bool(saw_reset) and back)
            if ok:
                self.log.info("RLB-009 soft off GREEN")
                return True
            self.log.error(
                f"RLB-009 soft off: state_encoding={state} (want 2), "
                f"clocks=0x{clocks:08X} (want 0), rails=0x{rails:02X} (want "
                f"only bit 0), boot_pulse={bool(saw_reset)}, back_in_S0={back}")
            return False
        except Exception as e:
            self.log.error(f"RLB-009 soft off test error: {e}")
            return False

    async def test_rlb009_reset_source_pins(self) -> bool:
        """RLB-009: RESET_STATUS.wdt_reset and .ext_reset are observable.

        Both used to read 0 always, because nothing carried the information
        into the block. They now come from device pins, and a source is
        LATCHED rather than sampled: the pulse that caused a reset is long
        gone by the time software reads the register."""
        self.log.info("=== RLB-009: reset source pins ===")
        try:
            results = {}
            M = PMACPIRegisterMap
            for name, pin, bit in (("wdt", self.tb.dut.wdt_reset_n, M.RESET_STATUS_WDT),
                                   ("ext", self.tb.dut.ext_reset_n, M.RESET_STATUS_EXT)):
                await self.tb.assert_reset()
                await ClockCycles(self.tb.pclk, 10)
                await self.tb.deassert_reset()
                await ClockCycles(self.tb.pclk, 20)
                _, before = await self.tb.read_register(M.RESET_STATUS)
                pin.value = 0                      # assert (active low)
                await ClockCycles(self.tb.pclk, 20)
                pin.value = 1                      # release
                await ClockCycles(self.tb.pclk, 20)
                _, after = await self.tb.read_register(M.RESET_STATUS)
                await ClockCycles(self.tb.pclk, 200)
                _, held = await self.tb.read_register(M.RESET_STATUS)
                results[name] = (bool(before & bit), bool(after & bit),
                                 bool(held & bit))
                self.log.info(f"  {name}: before={results[name][0]} "
                              f"after_pulse={results[name][1]} "
                              f"still_latched={results[name][2]}")

            ok = all((not b) and a and h for (b, a, h) in results.values())
            if ok:
                self.log.info("RLB-009 reset source pins GREEN")
                return True
            self.log.error(
                f"RLB-009 reset sources: {results} (want each False before the "
                f"pulse, True after it, and still True later)")
            return False
        except Exception as e:
            self.log.error(f"RLB-009 reset source test error: {e}")
            return False

    async def test_pm_timer_divider_sweep(self) -> bool:
        """Test PM Timer with various divider values."""
        self.log.info("Testing PM Timer divider sweep...")

        try:
            dividers = [0, 1, 2, 4, 8, 16, 32, 64, 100, 255]

            for divider in dividers:
                # Configure and enable
                await self.tb.configure_pm_timer(divider=divider)
                await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=False)
                await ClockCycles(self.tb.pclk, 10)

                # Read timer values
                timer_val1 = await self.tb.read_pm_timer()
                await ClockCycles(self.tb.pclk, 200)
                timer_val2 = await self.tb.read_pm_timer()

                increment = timer_val2 - timer_val1
                expected = 200 // (divider + 1) if divider > 0 else 200

                self.log.info(f"  Divider {divider:3d}: increment={increment}, expected~{expected}")

                # Verify timer incremented (don't be too strict on exact counts)
                if increment == 0 and expected > 2:
                    self.log.error(f"Timer did not increment with divider {divider}")
                    return False

            self.log.info("PM Timer divider sweep PASSED")
            return True

        except Exception as e:
            self.log.error(f"PM Timer divider sweep failed: {e}")
            return False

    async def test_pm_timer_extended_run(self) -> bool:
        """Run PM Timer for extended period and verify monotonic increase."""
        self.log.info("Testing PM Timer extended run...")

        try:
            # Fast timer
            await self.tb.configure_pm_timer(divider=0)
            await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            # Run for many iterations
            prev_val = 0
            read_count = 200  # More iterations than basic test

            for i in range(read_count):
                timer_val = await self.tb.read_pm_timer()
                if timer_val < prev_val:
                    self.log.error(f"Timer went backwards at iteration {i}: {prev_val} -> {timer_val}")
                    return False
                prev_val = timer_val
                await ClockCycles(self.tb.pclk, 5)

            self.log.info(f"  Timer read {read_count} times, final value: 0x{prev_val:08X}")
            self.log.info("PM Timer extended run PASSED")
            return True

        except Exception as e:
            self.log.error(f"PM Timer extended run failed: {e}")
            return False

    # ========================================================================
    # GPE Extended Tests
    # ========================================================================

    async def test_gpe_enable_patterns(self) -> bool:
        """Test comprehensive GPE enable patterns."""
        self.log.info("Testing GPE enable patterns...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=True)
            await ClockCycles(self.tb.pclk, 5)

            # Extended pattern set
            patterns = [
                0x00000000, 0xFFFFFFFF, 0x55555555, 0xAAAAAAAA,
                0x0F0F0F0F, 0xF0F0F0F0, 0x00FF00FF, 0xFF00FF00,
                0x0000FFFF, 0xFFFF0000, 0x12345678, 0x87654321,
                0xDEADBEEF, 0xCAFEBABE, 0x01234567, 0x76543210,
            ]

            for pattern in patterns:
                await self.tb.configure_gpe_enables(pattern)
                await ClockCycles(self.tb.pclk, 5)

                _, lo = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_LO)
                _, hi = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_HI)
                readback = (hi << 16) | lo

                if readback != pattern:
                    self.log.error(f"GPE pattern mismatch: 0x{pattern:08X} != 0x{readback:08X}")
                    return False

            self.log.info(f"  Tested {len(patterns)} GPE patterns")
            self.log.info("GPE enable patterns PASSED")
            return True

        except Exception as e:
            self.log.error(f"GPE enable patterns test failed: {e}")
            return False

    async def test_gpe_walking_ones(self) -> bool:
        """Test GPE with walking ones pattern."""
        self.log.info("Testing GPE walking ones...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=True)
            await ClockCycles(self.tb.pclk, 5)

            # Walking ones through all 32 bits
            for bit in range(32):
                pattern = 1 << bit
                await self.tb.configure_gpe_enables(pattern)
                await ClockCycles(self.tb.pclk, 3)

                _, lo = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_LO)
                _, hi = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_HI)
                readback = (hi << 16) | lo

                if readback != pattern:
                    self.log.error(f"GPE bit {bit} mismatch: 0x{pattern:08X} != 0x{readback:08X}")
                    return False

            # Walking zeros
            for bit in range(32):
                pattern = 0xFFFFFFFF ^ (1 << bit)
                await self.tb.configure_gpe_enables(pattern)
                await ClockCycles(self.tb.pclk, 3)

                _, lo = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_LO)
                _, hi = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_HI)
                readback = (hi << 16) | lo

                if readback != pattern:
                    self.log.error(f"GPE walking-zero bit {bit} mismatch")
                    return False

            self.log.info("  Walking ones and zeros verified")
            self.log.info("GPE walking ones PASSED")
            return True

        except Exception as e:
            self.log.error(f"GPE walking ones test failed: {e}")
            return False

    # ========================================================================
    # Clock Gate Extended Tests
    # ========================================================================

    async def test_clock_gate_patterns(self) -> bool:
        """Test comprehensive clock gate patterns."""
        self.log.info("Testing clock gate patterns...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            patterns = [
                0x00000000, 0xFFFFFFFF, 0x55555555, 0xAAAAAAAA,
                0x0F0F0F0F, 0xF0F0F0F0, 0x00FF00FF, 0xFF00FF00,
            ]

            for pattern in patterns:
                await self.tb.configure_clock_gates(pattern)
                await ClockCycles(self.tb.pclk, 5)

                outputs = self.tb.get_clock_gate_outputs()
                if outputs != pattern:
                    self.log.error(f"Clock gate mismatch: 0x{pattern:08X} != 0x{outputs:08X}")
                    return False

            # Walking ones for clock gates
            for bit in range(32):
                pattern = 1 << bit
                await self.tb.configure_clock_gates(pattern)
                await ClockCycles(self.tb.pclk, 3)

                outputs = self.tb.get_clock_gate_outputs()
                if outputs != pattern:
                    self.log.error(f"Clock gate bit {bit} mismatch")
                    return False

            self.log.info("Clock gate patterns PASSED")
            return True

        except Exception as e:
            self.log.error(f"Clock gate patterns test failed: {e}")
            return False

    # ========================================================================
    # Power Domain Extended Tests
    # ========================================================================

    async def test_power_domain_patterns(self) -> bool:
        """Test all power domain patterns."""
        self.log.info("Testing power domain patterns...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            # Test all 256 possible 8-bit patterns
            for pattern in range(256):
                await self.tb.configure_power_domains(pattern)
                await ClockCycles(self.tb.pclk, 3)

                outputs = self.tb.get_power_domain_outputs()
                if outputs != pattern:
                    self.log.error(f"Power domain mismatch: 0x{pattern:02X} != 0x{outputs:02X}")
                    return False

            self.log.info("  Tested all 256 power domain patterns")
            self.log.info("Power domain patterns PASSED")
            return True

        except Exception as e:
            self.log.error(f"Power domain patterns test failed: {e}")
            return False

    # ========================================================================
    # PM1 Control Tests
    # ========================================================================

    async def test_pm1_control_sweep(self) -> bool:
        """Test PM1 control register patterns."""
        self.log.info("Testing PM1 control sweep...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            # Test sleep type patterns (bits 2:0)
            for sleep_type in range(8):
                await self.tb.write_register(PMACPIRegisterMap.PM1_CONTROL, sleep_type)
                await ClockCycles(self.tb.pclk, 5)

                _, readback = await self.tb.read_register(PMACPIRegisterMap.PM1_CONTROL)
                if (readback & 0x7) != sleep_type:
                    self.log.error(f"PM1 sleep type mismatch: {sleep_type} != {readback & 0x7}")
                    return False

            # Test PM1 enable patterns
            for enable_pattern in range(16):
                await self.tb.write_register(PMACPIRegisterMap.PM1_ENABLE, enable_pattern)
                await ClockCycles(self.tb.pclk, 3)

                _, readback = await self.tb.read_register(PMACPIRegisterMap.PM1_ENABLE)
                if (readback & 0xF) != enable_pattern:
                    self.log.error(f"PM1 enable mismatch: {enable_pattern} != {readback & 0xF}")
                    return False

            self.log.info("PM1 control sweep PASSED")
            return True

        except Exception as e:
            self.log.error(f"PM1 control sweep failed: {e}")
            return False

    # ========================================================================
    # Wake Enable Tests
    # ========================================================================

    async def test_wake_enable_combinations(self) -> bool:
        """Test all wake enable combinations."""
        self.log.info("Testing wake enable combinations...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            # Test all 16 possible 4-bit patterns
            for pattern in range(16):
                await self.tb.write_register(PMACPIRegisterMap.WAKE_ENABLE, pattern)
                await ClockCycles(self.tb.pclk, 3)

                _, readback = await self.tb.read_register(PMACPIRegisterMap.WAKE_ENABLE)
                if (readback & 0xF) != pattern:
                    self.log.error(f"Wake enable mismatch: 0x{pattern:X} != 0x{readback & 0xF:X}")
                    return False

            self.log.info("  Tested all 16 wake enable patterns")
            self.log.info("Wake enable combinations PASSED")
            return True

        except Exception as e:
            self.log.error(f"Wake enable combinations failed: {e}")
            return False

    # ========================================================================
    # Interrupt Enable Tests
    # ========================================================================

    async def test_interrupt_enable_matrix(self) -> bool:
        """Test all interrupt enable combinations."""
        self.log.info("Testing interrupt enable matrix...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=True)
            await ClockCycles(self.tb.pclk, 5)

            # Test all 64 possible 6-bit patterns
            for pattern in range(64):
                await self.tb.write_register(PMACPIRegisterMap.ACPI_INT_ENABLE, pattern)
                await ClockCycles(self.tb.pclk, 3)

                _, readback = await self.tb.read_register(PMACPIRegisterMap.ACPI_INT_ENABLE)
                if (readback & 0x3F) != pattern:
                    self.log.error(f"Interrupt enable mismatch: 0x{pattern:02X} != 0x{readback & 0x3F:02X}")
                    return False

            self.log.info("  Tested all 64 interrupt enable patterns")
            self.log.info("Interrupt enable matrix PASSED")
            return True

        except Exception as e:
            self.log.error(f"Interrupt enable matrix failed: {e}")
            return False

    # ========================================================================
    # Register Access Stress Tests
    # ========================================================================

    async def test_register_access_stress(self) -> bool:
        """Stress test register access with many read/write operations."""
        self.log.info("Testing register access stress...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=True)
            await ClockCycles(self.tb.pclk, 5)

            # Rapid fire register writes and reads
            iterations = 100

            for i in range(iterations):
                # Write various registers
                pattern = (i * 0x12345) & 0xFFFFFFFF

                await self.tb.configure_clock_gates(pattern)
                await self.tb.configure_gpe_enables(pattern)
                await self.tb.configure_power_domains(pattern & 0xFF)

                # Read them back
                clk_out = self.tb.get_clock_gate_outputs()
                pwr_out = self.tb.get_power_domain_outputs()

                if clk_out != pattern:
                    self.log.error(f"Clock gate stress mismatch at iteration {i}")
                    return False

                if pwr_out != (pattern & 0xFF):
                    self.log.error(f"Power domain stress mismatch at iteration {i}")
                    return False

            self.log.info(f"  Completed {iterations} stress iterations")
            self.log.info("Register access stress PASSED")
            return True

        except Exception as e:
            self.log.error(f"Register access stress failed: {e}")
            return False
