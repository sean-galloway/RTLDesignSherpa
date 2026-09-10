# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: RTCMediumTests
# Purpose: GitHub #56 defect-regression suite for RTC
#
# Created: 2026-09-09

"""
RTC GitHub #56 Defect-Regression Test Suite

These tests encode CORRECT RTC behaviour against GitHub issue #56 (body
H4-H7 + qc round_2 (7 items) + qc round_3 (3 items)), checked against
`rtl/rtc/` (apb4_rtc.sv, rtc_config_regs.sv, rtc_core.sv) as ground truth.
Every test in this file is authored RED against the current (unfixed) RTL -
an RTL fix has NOT landed yet, so a FAIL here is the expected, correct
outcome and is the finding this suite exists to route to rds-rtl-design.

CLOCKING: unlike rtc_tests_basic.py (which always runs cfg_clock_select=1,
i.e. selected_clk=pclk, and is therefore indifferent to rtc_clk's actual
period), every test below exercises cfg_clock_select=0 - the RTC's actual
production configuration - with rtc_clk run at a real, non-unity 10:1 ratio
to pclk (TEST_RTC_CLOCK_PERIOD=100ns vs TEST_APB_CLOCK_PERIOD=10ns, wired by
the test runner; see rtc_tb.py's setup_clocks_and_reset() docstring). Nearly
every defect below is invisible at 1:1 - that IS the finding: the existing
suite only ever exercises the test-mode (clock_select=1) escape hatch, and
GH#56 round_3 item 1 says exactly this ("...which is why DV never saw it").

WHITEBOX FORCING: the real production divider is a 32768-tick divide
(one second = 32768 rtc_clk edges = ~3.3ms of sim time at this ratio, ~330k
pclk cycles). Waiting for a NATURAL tick in every scenario would make this
suite impractically slow, so every test that needs a tick uses
tb.force_divider_near_target() to whitebox-poke rtc_core.r_clk_div_counter
close to its rollover target - the same pattern hpet/pm_acpi use
(pm_acpi_tb.force_pm_timer_near_overflow). Tests that need a specific
calendar/hour STATE (not the time-SET mechanism itself) also whitebox-load
rtc_core's r_seconds..r_year directly via tb.force_time_registers(),
bypassing the separately-broken (contract A/B) APB time-set path entirely -
this deliberately isolates the counting/comparison-logic contracts (C/D/E/G)
from the time-set contracts (A/B) so one defect's test result does not
depend on a second, unrelated defect.

Defect index (GitHub #56):
  A. round_3 item 1 (the suite's worst defect) - time-set is DEAD in the
     production configuration. r_time_regs_wr (rtc_config_regs.sv ~157-168)
     is a single-pclk-wide strobe consumed by rtc_core's counting always_ff
     on `posedge selected_clk` (rtc_core.sv:223-242); with cfg_clock_select=0,
     selected_clk=rtc_clk, and a ~10ns pulse is essentially never seen by a
     domain running 10x (32768x on real silicon) slower - no synchronizer,
     no handshake, no level-hold. A single time-set attempt lands only by
     accident; repeating it does not converge to "eventually correct".
  B. round_2 item 6 - time-set is not atomic across the six fields.
     rtc_config_regs.sv's r_time_regs_wr strobes on ANY write ack in
     [0x00C, 0x020] (~163-166), and rtc_core.sv:234-242 reloads ALL SIX
     counting registers from the six hwif_out mirrors on every strobe, not
     just a designated "commit" register - so a captured strobe from an
     early field's write mixes that field's new value with whatever the
     other five mirrors held at that instant (defaults / a previous
     set_time(), not the values from the CURRENT batch, unless every earlier
     write's own mirror already settled by the time of the capture).
  C. round_2 item 4 / round_3 item 2 (H4) - multi-register reads can tear.
     rtc_core's r_seconds..r_year are re-evaluated as a group on
     `posedge selected_clk`, but the six-register APB read burst runs at
     pclk speed with no coherence mechanism (no shadow-latch-on-first-read,
     no atomic snapshot) - a real tick landing mid-burst is visible as a
     torn read (this is the exact "Stress test 15: seconds mismatch 0 vs 59"
     signature already filed on the issue as regression evidence).
  D. H5 - BCD calendar: `days_in_month()`'s BCD conversion
     (rtc_core.sv:212-214) is `{4'd0, days/8'd10, days%8'd10}`, a 20-bit
     concatenation truncated on assignment to an 8-bit `days` - only the
     low 8 bits (dominated by `days%10`) survive, so month lengths become
     0x01/0x00/0x08/0x09 instead of 0x31/0x30/0x28/0x29. `bcd_increment()`'s
     own `max_val` parameter is dead code (never referenced in the function
     body) so the corrupted `days_in_month()` return only reaches the
     carry-comparison a few lines later (rtc_core.sv:319,
     `bcd_compare_ge(next_day, max_days + 8'h01)`), which is where the wrong
     threshold actually bites.
  E. H6 - 12-hour mode sequencing is wrong in both paths
     (rtc_core.sv:278-296). BCD: the AM/PM toggle and day-carry condition
     tests `r_hours[6:0]==7'h12` (fires on the 12->1 transition) instead of
     an 11->12 transition, so AM/PM inverts for one hour in twelve and the
     day carries at noon instead of midnight. Binary: `carry_day =
     (r_hours == 8'd11)` fires on EVERY 11->12 wrap (there is no AM/PM state
     to distinguish the AM instance from the PM one - the comment even
     concedes "simplified here"), so the date advances twice per day.
  F. round_3 item 2 - a W1C can be undone by the wide tick pulse. The
     status-flag set sources (r_second_tick, r_alarm_match) are registered
     on selected_clk and, in production mode, stay asserted for a full
     rtc_clk period (~10 pclk cycles at this test's ratio, ~655360 pclk
     cycles / ~30.5us on real silicon) - crossed RAW into the pclk domain
     with no edge detection (rtc_core.sv:401-420). A W1C write that lands
     anywhere inside that window clears the regblock's W1C field for one
     cycle, but the very next cycle the (still-high) source re-arms it via
     the field's HW-write path (rtc_regs.sv ~518-527) - an ISR that clears
     promptly after the tick gets re-interrupted.
  G. round_3 item 3 - the alarm comparator is not gated by cfg_time_set_mode.
     rtc_core.sv:378-392's `always_ff` checks only `cfg_alarm_enable &&
     r_second_tick` - and r_second_tick keeps pulsing even while
     cfg_time_set_mode stops the counting update (the divider logic at
     rtc_core.sv:96-109 only checks `rst || !cfg_rtc_enable`) - so a
     counter frozen mid-programming that happens to sit on the alarm value
     sets the alarm flag before the operator has finished setting the time.
  H. round_2 item 1 (address decode) - rtc_config_regs.sv passes only
     `regblk_addr[5:0]` into the PeakRDL regblock's `s_cpuif_addr`
     (rtc_regs.sv:10,227 of the wrapper), and the generated regblock's
     `cpuif_wr_err`/`readback_err` are hardwired `'0` (rtc_regs.sv ~862,916)
     - so (1) every address in the 4KB APB window aliases into the 6-bit
     [0x000,0x030] register space instead of the unmapped remainder being
     dropped with PSLVERR, and (2) even the genuinely-reserved slots inside
     that 6-bit space (0x034-0x3F) silently ack with no error. Concretely,
     writing 0x84C (0x84C & 0x3F == 0x0C) corrupts the live RTC_SECONDS
     shadow register through an address no register map documents.
  I. round_2 item 5 - rtc_resetn dangles. apb4_rtc.sv declares the port but
     never references it again anywhere in the module body - it is not
     wired to rtc_core, not to rtc_config_regs, not to anything. Per the
     task brief this is a real (not log-only) assertion since the TB CAN
     drive the pin; the RTL guarantees driving it low has zero effect.

Which existing tests mask each defect (all of rtc_tests_basic.py runs
cfg_clock_select=1 via enable_rtc(use_sys_clock=True) EXCLUSIVELY - not one
existing test ever sets cfg_clock_select=0):
  - A/B: test_time_setting()/test_rtc_stress() etc. call set_time() at 1:1
    clocks, where selected_clk=pclk=the SAME domain r_time_regs_wr is
    generated in - the strobe is captured on effectively every attempt, so
    the CDC failure mode (A) and the mid-batch reload race (B) never fire.
  - C: never exercised - no existing test forces a tick to land mid-burst;
    test_rtc_stress()'s "Stress test 15: seconds mismatch 0 vs 59" (filed as
    regression evidence on the issue) is this SAME defect class showing up
    by accident under a particular SEED, not a directed reproduction.
  - D: test_bcd_mode() only checks that the upper BCD nibble is <=5 right
    after a set_time() and logs (does not assert on) the post-rollover
    value; test_date_rollover()/test_leap_year_feb29() wait then just log
    whatever day/month came out - masks D entirely.
  - E: test_12_hour_mode() sets an AM and a PM time and only logs the
    readback, no assertion on hours/PM/day at all - masks E entirely.
  - F: no existing test issues a W1C promptly after observing a tick in
    production mode (1:1 clocks make the set pulse a single pclk cycle
    wide, so even a same-cycle clear cannot race it) - masks F entirely.
  - G: no existing test enables the alarm while cfg_time_set_mode is
    asserted - masks G entirely.
  - H: test_register_access() only touches RTC_CONFIG; no existing test
    reads/writes an out-of-map or aliased address, and PSLVERR is never
    read back by the TB at all before this suite added it - masks H
    entirely.
  - I: no existing test ever drives dut.rtc_resetn independently of
    presetn - masks I entirely.
"""

import os

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb.utils import get_sim_time

from .rtc_tb import RTCRegisterMap


# ============================================================================
# Reference model helpers (plain Python, used only to compute EXPECTED
# values for assertions - never touches the DUT)
# ============================================================================

def _bcd_to_int(b: int) -> int:
    return (b >> 4) * 10 + (b & 0xF)


def _int_to_bcd(v: int) -> int:
    return ((v // 10) << 4) | (v % 10)


def _is_leap(year_2digit: int) -> bool:
    # Matches rtc_core.sv's OWN is_leap_year() rule exactly (year_bin[1:0]
    # == 0) - not the real Gregorian century rule, and not something GH#56
    # flags as a defect, so the reference model intentionally mirrors it
    # rather than the "more correct" astronomical rule.
    return (year_2digit % 4) == 0


def _days_in_month_correct(month: int, year_2digit: int) -> int:
    if month in (1, 3, 5, 7, 8, 10, 12):
        return 31
    if month in (4, 6, 9, 11):
        return 30
    if month == 2:
        return 29 if _is_leap(year_2digit) else 28
    return 31


def _next_day_bcd(day_bcd: int, month_bcd: int, year_bcd: int):
    """One-day advance of a BCD (day, month, year) tuple using the CORRECT
    (not GH#56-H5-broken) days-in-month rule. Returns (day, month, year), all
    BCD-encoded bytes."""
    day = _bcd_to_int(day_bcd)
    month = _bcd_to_int(month_bcd)
    year = _bcd_to_int(year_bcd)

    max_days = _days_in_month_correct(month, year)
    day += 1
    if day > max_days:
        day = 1
        month += 1
        if month > 12:
            month = 1
            year = (year + 1) % 100

    return _int_to_bcd(day), _int_to_bcd(month), _int_to_bcd(year)


class RTCMediumTests:
    """GitHub #56 defect-regression suite for RTC (medium/full levels)."""

    def __init__(self, tb):
        """
        Args:
            tb: RTCTB testbench instance
        """
        self.tb = tb
        self.log = tb.log

    async def _enable_production_mode(self, bcd: bool = False, hour_12: bool = False):
        """CONFIG.rtc_enable=1, clock_select=0 (production/rtc_clk), plus the
        requested BCD/12h mode bits. time_set_mode left clear."""
        config = RTCRegisterMap.CONFIG_RTC_ENABLE
        if bcd:
            config |= RTCRegisterMap.CONFIG_BCD_MODE
        if hour_12:
            config |= RTCRegisterMap.CONFIG_HOUR_MODE_12
        await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
        await ClockCycles(self.tb.pclk, 5)

    async def _wait_mode_applied(self, bcd: bool, hour_12: bool,
                                  timeout_counter_clocks: int = 20):
        """
        Poll dut.u_rtc_core's held configuration (r_cfg_hold bits 2/1:
        bcd_mode/hour_mode_12) until the counter domain has actually
        applied the requested mode bits, with a bounded timeout.

        Coordinator direction 2026-09-09 (round-6 RTL follow-up): the
        config crossing now takes SYNC_STAGES=3 counter clocks PLUS a
        one-sample two-identical-samples filter, i.e. 4 counter clocks
        total from the RTC_CONFIG write - one more than
        _enable_production_mode()'s flat 5-pclk (0.5 counter-clock at the
        10:1 ratio) wait accounts for. Rather than hardcode a new fixed
        wait (which would just be the next stale-margin bug waiting to
        happen the next time the crossing's internal latency changes),
        this polls the actual white-box evidence that the mode bits have
        landed, so the test states what it depends on instead of guessing.
        """
        core = self.tb.dut.u_rtc_core
        expected_bcd = 1 if bcd else 0
        expected_hour12 = 1 if hour_12 else 0
        got_bcd = None
        got_hour12 = None
        consecutive_matches = 0
        for _ in range(timeout_counter_clocks):
            held = int(core.r_cfg_hold.value)
            got_bcd = (held >> 2) & 1
            got_hour12 = (held >> 1) & 1
            if got_bcd == expected_bcd and got_hour12 == expected_hour12:
                consecutive_matches += 1
                # Require the match twice in a row, one counter clock
                # apart, mirroring the RTL's own two-identical-samples
                # filter - a single matching sample can be a transient on
                # the crossing's settling edge, not the steady-state value.
                if consecutive_matches >= 2:
                    return
            else:
                consecutive_matches = 0
            await ClockCycles(self.tb.dut.rtc_clk, 1)
        raise AssertionError(
            f"mode bits did not cross to the counter domain (and hold stable for 2 "
            f"consecutive counter clocks) within {timeout_counter_clocks} counter "
            f"clocks of the RTC_CONFIG write: expected bcd={expected_bcd} "
            f"hour12={expected_hour12}, r_cfg_hold last read bcd={got_bcd} "
            f"hour12={got_hour12}"
        )

    # ------------------------------------------------------------------
    # A. Time-set is dead in the production configuration (round_3 item 1)
    # ------------------------------------------------------------------

    async def test_gh56_time_set_production_mode(self) -> bool:
        """
        Setting the time via the documented APB protocol (time_set_mode +
        the six writes) must work in the RTC's actual production
        configuration (cfg_clock_select=0), not just the clock_select=1
        test-mode escape hatch. Repeats the write/read-back N times with a
        DIFFERENT, easily-distinguishable time each attempt and requires
        ALL of them to land - "eventually correct" is not the contract.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-A Time-set in production mode (repeated)")
        self.log.info("=" * 80)

        try:
            await self._enable_production_mode(bcd=False, hour_12=False)

            attempts = 12
            failures = []
            for i in range(attempts):
                secs = (7 + i * 3) % 60
                mins = (11 + i * 5) % 60
                hrs = (1 + i * 2) % 24
                day = 1 + (i % 27)
                month = 1 + (i % 12)
                year = (i * 4) % 100

                await self.tb.set_time(secs, mins, hrs, day, month, year)
                # A couple of rtc_clk periods of settle time - long enough
                # for a captured (or missed) strobe to show up, short enough
                # that the free-running production divider (target=32767)
                # has no realistic chance of an incidental natural tick.
                await ClockCycles(self.tb.pclk, 30)

                readback = await self.tb.read_time()
                expected = {'seconds': secs, 'minutes': mins, 'hours': hrs,
                            'day': day, 'month': month, 'year': year}

                if readback != expected:
                    failures.append((i, expected, readback))
                    self.log.error(f"  attempt {i}: expected {expected}, got {readback}")
                else:
                    self.log.info(f"  attempt {i}: OK {readback}")

            assert not failures, (
                f"{len(failures)}/{attempts} production-mode time-set attempts did not "
                f"land (r_time_regs_wr's single-pclk strobe was not captured by the "
                f"rtc_clk domain) - first failure: attempt {failures[0][0]}, expected "
                f"{failures[0][1]}, got {failures[0][2]}"
            )

            self.log.info("GH#56-A Time-set in production mode test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-A Time-set in production mode test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # B. Time-set is not atomic across the six fields (round_2 item 6)
    # ------------------------------------------------------------------

    async def test_gh56_time_set_atomicity(self) -> bool:
        """
        The six time-register writes issued by a single set_time() call
        must all land together - no captured intermediate reload may mix a
        just-written field with stale values from a PREVIOUS batch. Seeds a
        recognizably-different "previous" time first, then repeats a fresh
        batch several times, requiring every readback to exactly equal the
        NEW batch (never a seconds/minutes/... mix between old and new).
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-B Time-set atomicity (six fields, back-to-back)")
        self.log.info("=" * 80)

        try:
            await self._enable_production_mode(bcd=False, hour_12=False)

            # Seed a "previous" batch so any mixed reload is visible as a
            # foreign value rather than accidentally matching (0 vs 0 etc.).
            await self.tb.set_time(seconds=1, minutes=2, hours=3, day=4, month=5, year=6)
            await ClockCycles(self.tb.pclk, 30)

            attempts = 10
            failures = []
            for i in range(attempts):
                new = {'seconds': 40 + (i % 19), 'minutes': 33 + (i % 20),
                       'hours': 5 + (i % 18), 'day': 9 + (i % 15),
                       'month': 1 + ((i + 6) % 12), 'year': 50 + i}

                await self.tb.set_time(**new)
                await ClockCycles(self.tb.pclk, 30)

                readback = await self.tb.read_time()
                if readback != new:
                    mixed = {k: v for k, v in readback.items() if v != new[k]}
                    failures.append((i, new, readback, mixed))
                    self.log.error(
                        f"  attempt {i}: expected {new}, got {readback} (mismatched fields: {mixed})"
                    )
                else:
                    self.log.info(f"  attempt {i}: OK {readback}")

            assert not failures, (
                f"{len(failures)}/{attempts} back-to-back six-field time-set batches did "
                f"not land atomically - first failure: attempt {failures[0][0]}, wrote "
                f"{failures[0][1]}, read back {failures[0][2]} (mismatched fields: "
                f"{failures[0][3]}) - a captured reload mid-batch mixed fields from an "
                f"earlier/previous write with the current batch"
            )

            self.log.info("GH#56-B Time-set atomicity test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-B Time-set atomicity test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # C. Coherent multi-register reads across a rollover (H4 / round_2-4)
    # ------------------------------------------------------------------

    async def test_gh56_coherent_reads_across_rollover(self) -> bool:
        """
        A six-register read burst (seconds/minutes/hours/day/month/year)
        must never return a torn mix of the pre- and post-rollover time -
        every burst must equal EXACTLY the pre-tick snapshot or EXACTLY the
        post-tick snapshot. Whitebox-loads 23:59:59 Dec 31 directly (see
        module docstring - this isolates the read-coherence contract from
        the separately-broken time-SET contracts A/B) and whitebox-forces
        the divider to land the real tick at a series of different offsets
        from the start of the read burst, sweeping across the burst's
        width so at least one alignment lands the tick between two of the
        six reads - the same sweep-for-alignment pattern PIT's GH#52-I test
        uses for an unknown internal latency.

        This directly reproduces the "Stress test 15: seconds mismatch 0
        vs 59" signature already filed on the issue as regression evidence
        (SEED=87792, test_rtc_stress) - but by construction rather than by
        accident.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-C Coherent reads across rollover")
        self.log.info("=" * 80)

        pre = {'seconds': 59, 'minutes': 59, 'hours': 23, 'day': 31, 'month': 12, 'year': 25}
        post = {'seconds': 0, 'minutes': 0, 'hours': 0, 'day': 1, 'month': 1, 'year': 26}

        try:
            await self._enable_production_mode(bcd=False, hour_12=False)

            torn = []
            for k in range(1, 16):
                await self.tb.force_time_registers(**pre)
                await self.tb.force_divider_near_target(clock_select=0, remaining_cycles=k)
                await ClockCycles(self.tb.pclk, 2)

                burst = {}
                for name, addr in (('seconds', RTCRegisterMap.RTC_SECONDS),
                                    ('minutes', RTCRegisterMap.RTC_MINUTES),
                                    ('hours', RTCRegisterMap.RTC_HOURS),
                                    ('day', RTCRegisterMap.RTC_DAY),
                                    ('month', RTCRegisterMap.RTC_MONTH),
                                    ('year', RTCRegisterMap.RTC_YEAR)):
                    _, val = await self.tb.read_register(addr)
                    burst[name] = val & 0xFF

                coherent = (burst == pre) or (burst == post)
                self.log.info(f"  k={k:2d} burst={burst} coherent={coherent}")
                if not coherent:
                    torn.append((k, dict(burst)))

            assert not torn, (
                f"{len(torn)}/15 read bursts were torn (matched neither the pre-tick "
                f"snapshot {pre} nor the post-tick snapshot {post}): "
                f"{torn[:3]}{'...' if len(torn) > 3 else ''}"
            )

            self.log.info("GH#56-C Coherent reads across rollover test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-C Coherent reads across rollover test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # D. BCD calendar (H5)
    # ------------------------------------------------------------------

    async def test_gh56_bcd_calendar_rollover(self) -> bool:
        """
        BCD-mode day/month/year rollover must follow the real (BCD-correct)
        days-in-month table. Whitebox-loads each scenario's pre-tick time
        directly (see module docstring), forces a tick, and compares the
        readback against a plain-Python reference model
        (_next_day_bcd/_days_in_month_correct above) rather than
        hand-computed literals.

        Scenarios are exactly the ones named in the GH#56 defect brief.
        Historical note (this suite, first run): a few of these land on the
        CORRECT answer even against the current buggy days_in_month() by
        coincidence - see the docstring on days_in_month() (GH#56-D defect
        index entry) - the corrupted month-length threshold is nearly
        always much SMALLER than the real one, so by the time day reaches
        the REAL end of a long/medium month the (already-satisfied-much-
        earlier) wrong threshold has been true for many days and the two
        algorithms agree at that specific instant. The Feb-29-in-a-leap-
        year scenario is the one guaranteed to diverge (day 28 must NOT
        roll yet), so it anchors this test; the "must not roll early"
        scenario is added as a second, independently-reliable check.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-D BCD calendar rollover")
        self.log.info("=" * 80)

        scenarios = [
            ("Jan 31 -> Feb 1", 0x59, 0x59, 0x23, 0x31, 0x01, 0x25),
            ("Feb 28 -> Mar 1 (non-leap, 2025)", 0x59, 0x59, 0x23, 0x28, 0x02, 0x25),
            ("Feb 28 -> Feb 29 (leap, 2024)", 0x59, 0x59, 0x23, 0x28, 0x02, 0x24),
            ("Feb 29 -> Mar 1 (leap, 2024)", 0x59, 0x59, 0x23, 0x29, 0x02, 0x24),
            ("Apr 30 -> May 1", 0x59, 0x59, 0x23, 0x30, 0x04, 0x25),
            ("Dec 31 -> Jan 1 (year rollover)", 0x59, 0x59, 0x23, 0x31, 0x12, 0x25),
            # Supplementary: a 31-day month must NOT roll the month at day 2
            # (the corrupted max_days=0x01+1 threshold is satisfied by
            # essentially any day count, including the very first
            # increment) - the most direct reproduction of H5's "rolls
            # after day 2" framing.
            ("Jan 2 -> Jan 3 (must NOT roll month)", 0x59, 0x59, 0x23, 0x02, 0x01, 0x25),
        ]

        try:
            await self._enable_production_mode(bcd=True, hour_12=False)

            failures = []
            for name, sec, mn, hr, day, month, year in scenarios:
                exp_day, exp_month, exp_year = _next_day_bcd(day, month, year)

                await self.tb.force_time_registers(sec, mn, hr, day, month, year)
                await self.tb.force_divider_near_target(clock_select=0, remaining_cycles=2)
                await ClockCycles(self.tb.pclk, 30)  # several rtc_clk periods past the tick

                time = await self.tb.read_time()
                got = (time['day'], time['month'], time['year'])
                exp = (exp_day, exp_month, exp_year)

                ok = got == exp
                self.log.info(
                    f"  {name}: pre=({day:02x},{month:02x},{year:02x}) "
                    f"expected=({exp_day:02x},{exp_month:02x},{exp_year:02x}) "
                    f"got=({got[0]:02x},{got[1]:02x},{got[2]:02x}) {'OK' if ok else 'MISMATCH'}"
                )
                if not ok:
                    failures.append((name, exp, got))

            assert not failures, (
                f"{len(failures)}/{len(scenarios)} BCD calendar rollover scenarios "
                f"mismatched the reference model: " +
                "; ".join(f"{n}: expected {e}, got {g}" for n, e, g in failures)
            )

            self.log.info("GH#56-D BCD calendar rollover test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-D BCD calendar rollover test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # E. 12-hour mode sequencing (H6)
    # ------------------------------------------------------------------

    async def test_gh56_12_hour_mode_transitions(self) -> bool:
        """
        BCD 12-hour: the AM/PM toggle and midnight day-carry must happen at
        the 11->12 transition, never at 12->1. Three scenarios, each
        checking hours+PM+day where relevant:
          1. 11:59:59 AM -> 12:00:00 PM (PM must SET here)
          2. 12:59:59 PM -> 01:00:00 PM (PM must NOT change)
          3. 11:59:59 PM -> 12:00:00 AM, with the day carrying (midnight)

        Binary 12-hour: there is no independent AM/PM state at all
        (rtc_core.sv's own comment concedes "simplified here"), so
        `carry_day = (r_hours == 8'd11)` fires on BOTH the noon and
        midnight 11->12 wraps - the day advances twice per 24 real hours
        instead of once. That miscount is directly checkable without
        presuming what register/bit a fix would use to represent binary-
        mode PM (there isn't one today - see the note at the end of this
        docstring for what could NOT be tested for that reason).
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-E 12-hour mode transitions")
        self.log.info("=" * 80)

        try:
            failures = []

            # --- BCD sub-cases ---
            await self._enable_production_mode(bcd=True, hour_12=True)
            await self._wait_mode_applied(bcd=True, hour_12=True)

            bcd_cases = [
                ("11:59:59 AM -> 12:00:00 PM (PM must set)",
                 0x59, 0x59, 0x11, 0x15, 0x06, 0x25,   # pre: AM, hour=11
                 0x92, False),                          # expected: PM=1, hour=12 (0x92), no day carry
                ("12:59:59 PM -> 01:00:00 PM (PM must NOT change)",
                 0x59, 0x59, 0x92, 0x15, 0x06, 0x25,   # pre: PM, hour=12
                 0x81, False),                          # expected: PM=1, hour=01 (0x81), no day carry
                ("11:59:59 PM -> 12:00:00 AM (day must carry)",
                 0x59, 0x59, 0x91, 0x15, 0x06, 0x25,   # pre: PM, hour=11
                 0x12, True),                           # expected: PM=0, hour=12 (0x12), day carries
            ]

            for name, sec, mn, hr, day, month, year, exp_hours, expect_carry in bcd_cases:
                await self.tb.force_time_registers(sec, mn, hr, day, month, year)
                await self.tb.force_divider_near_target(clock_select=0, remaining_cycles=2)
                await ClockCycles(self.tb.pclk, 30)

                time = await self.tb.read_time()
                got_hours = time['hours']
                got_day = time['day']
                exp_day = _int_to_bcd(_bcd_to_int(day) + 1) if expect_carry else day

                ok = (got_hours == exp_hours) and (got_day == exp_day)
                self.log.info(
                    f"  BCD {name}: expected hours=0x{exp_hours:02x} day=0x{exp_day:02x}, "
                    f"got hours=0x{got_hours:02x} day=0x{got_day:02x} {'OK' if ok else 'MISMATCH'}"
                )
                if not ok:
                    failures.append((f"BCD {name}", exp_hours, exp_day, got_hours, got_day))

            # --- Binary sub-case: day must carry exactly once per 24
            #     forced hour-increments (not twice) ---
            await self._enable_production_mode(bcd=False, hour_12=True)
            await self._wait_mode_applied(bcd=False, hour_12=True)
            # Settle a few pclk past the poll's own return point before the
            # next whitebox force - keeps this force cleanly separated
            # from the poll loop's exact simulation-phase return point
            # rather than chaining an unawaited force directly off it.
            await ClockCycles(self.tb.pclk, 10)

            start_day = 15
            await self.tb.force_time_registers(seconds=0, minutes=0, hours=1,
                                                day=start_day, month=6, year=25)
            await ClockCycles(self.tb.pclk, 5)

            day_carry_count = 0
            for hour_step in range(24):
                # Pre-load 59:59 for the CURRENT hour so a single forced
                # tick cascades seconds->minutes->hours in one shot.
                cur = self.tb.read_time_registers_whitebox()
                await self.tb.force_time_registers(seconds=59, minutes=59, hours=cur['hours'],
                                                    day=cur['day'], month=cur['month'], year=cur['year'])
                before_day = cur['day']
                await self.tb.force_divider_near_target(clock_select=0, remaining_cycles=2)
                await ClockCycles(self.tb.pclk, 30)
                after = self.tb.read_time_registers_whitebox()
                if after['day'] != before_day:
                    day_carry_count += 1

            self.log.info(f"  Binary 12h: day carried {day_carry_count} time(s) over 24 forced hours "
                           f"(expected exactly 1)")
            if day_carry_count != 1:
                failures.append(("Binary 24-forced-hour day-carry count", 1, None, day_carry_count, None))

            self.log.info(
                "  NOTE: binary-mode PM-indicator readback is NOT independently asserted here - "
                "rtc_core.sv has no storage at all for binary-mode AM/PM (status_pm_indicator is "
                "hardwired 0 whenever !cfg_bcd_mode, rtc_core.sv:436), so there is no defined value "
                "to assert against without presuming which bit/register a fix would add. See the "
                "'cannot be made to fail deterministically' note in the final report."
            )

            assert not failures, (
                f"{len(failures)} of the 12-hour mode transition checks failed: {failures}"
            )

            self.log.info("GH#56-E 12-hour mode transitions test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-E 12-hour mode transitions test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # F. W1C not undone by the wide tick pulse (round_3 item 2)
    # ------------------------------------------------------------------

    # How many pclk cycles to hold r_second_tick artificially high. Measured
    # (this suite, first run): the real production-divider-driven pulse at
    # this test's 10:1 ratio is only ~9 pclk cycles wide, and a single APB
    # W1C write through this stack (APBMaster 'fixed' profile -> apb4_slave
    # -> peakrdl_to_cmdrsp -> regblock ack) already takes ~8 of those cycles
    # end to end - even the earliest possible clear (issued the instant the
    # tick is observed) lands with only ~1 cycle of window left, too little
    # margin to reliably demonstrate the re-arm. On real silicon the window
    # is ~30us (~3000x an APB write's latency), so this is a sim-ratio
    # artifact, not evidence the defect is narrow. Directly forcing
    # r_second_tick (rather than waiting on the real divider) removes the
    # detection/APB latency from the budget and reproduces the SAME "raw
    # multi-cycle level crossing into pclk with no edge detection" mechanism
    # with controlled, generous margin.
    W1C_HOLD_CYCLES = 15

    async def test_gh56_w1c_not_undone_by_wide_tick(self) -> bool:
        """
        A write-1-to-clear of STATUS.second_tick issued while the tick
        source is still asserted must stay clear for the REMAINDER of that
        assertion - not be re-armed a cycle or two later by the still-high
        pulse. See W1C_HOLD_CYCLES above for why this directly forces
        rtc_core.r_second_tick high for a controlled window instead of
        waiting on the real (here, marginally-too-narrow-to-race) divider-
        driven pulse - the propagation mechanism under test
        (rtc_core.sv:401-420's raw, unsynchronized read of a source that
        stays asserted for many pclk cycles) is identical either way.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-F W1C not undone by wide tick pulse")
        self.log.info("=" * 80)

        try:
            await self._enable_production_mode(bcd=False, hour_12=False)

            core = self.tb.dut.u_rtc_core

            async def _hold_tick_high():
                for _ in range(self.W1C_HOLD_CYCLES):
                    core.r_second_tick.value = 1
                    await RisingEdge(self.tb.pclk)
                core.r_second_tick.value = 0

            trace = []

            async def _tracer():
                for _ in range(self.W1C_HOLD_CYCLES + 5):
                    await RisingEdge(self.tb.pclk)
                    trace.append((int(core.r_second_tick.value), int(core.r_second_tick_flag.value)))

            cocotb.start_soon(_hold_tick_high())
            tracer_task = cocotb.start_soon(_tracer())

            # Prompt clear, issued while r_second_tick is (forced) high.
            await self.tb.write_register(RTCRegisterMap.RTC_STATUS, RTCRegisterMap.STATUS_SECOND_TICK)
            await tracer_task
            self.log.info(f"  (r_second_tick, r_second_tick_flag) per pclk cycle across the clear: {trace}")

            reasserted_at = None
            for i in range(10):
                _, status = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                still_high = bool(status & RTCRegisterMap.STATUS_SECOND_TICK)
                self.log.info(f"  post-clear read {i}: second_tick={still_high}")
                if still_high:
                    reasserted_at = i
                    break

            assert reasserted_at is None, (
                f"STATUS.second_tick was re-asserted at post-clear read #{reasserted_at} - "
                f"the wide production-mode tick pulse re-armed the W1C field after it was "
                f"cleared, before the next real tick"
            )

            self.log.info("GH#56-F W1C not undone by wide tick pulse test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-F W1C not undone by wide tick pulse test FAILED: {e}")
            return False
        finally:
            self.tb.dut.u_rtc_core.r_second_tick.value = 0

    # ------------------------------------------------------------------
    # G. Alarm must not fire during time_set_mode (round_3 item 3)
    # ------------------------------------------------------------------

    async def test_gh56_alarm_not_during_time_set(self) -> bool:
        """
        A counter frozen by cfg_time_set_mode that happens to sit exactly
        on the programmed alarm value must NOT set the alarm flag until
        time-set mode is left - the operator is mid-edit, not done.
        Whitebox-freezes r_seconds/minutes/hours at the alarm target while
        time_set_mode is asserted (bypassing the separately-broken A/B
        time-set path - see module docstring), forces a real tick, and
        confirms STATUS.alarm_flag stays clear.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-G Alarm must not fire during time_set_mode")
        self.log.info("=" * 80)

        try:
            await self._enable_production_mode(bcd=False, hour_12=False)

            # Enter time_set_mode (real APB write - this bit itself is not
            # under test here).
            config = (RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE)
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)

            alarm_sec, alarm_min, alarm_hour = 30, 15, 9
            await self.tb.force_time_registers(seconds=alarm_sec, minutes=alarm_min, hours=alarm_hour,
                                                day=1, month=1, year=25)

            await self.tb.set_alarm(seconds=alarm_sec, minutes=alarm_min, hours=alarm_hour,
                                     sec_match=True, min_match=True, hour_match=True)
            await self.tb.enable_alarm(enable=True, enable_interrupt=True)
            await self.tb.clear_status_flags(clear_alarm=True)

            await self.tb.force_divider_near_target(clock_select=0, remaining_cycles=2)
            await ClockCycles(self.tb.pclk, 40)  # several rtc_clk periods, well past the forced tick

            status = await self.tb.read_status()

            # Cleanup: leave time_set_mode regardless of outcome.
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)

            assert not status['alarm_flag'], (
                f"STATUS.alarm_flag set while cfg_time_set_mode was still asserted - the alarm "
                f"comparator (rtc_core.sv:378-392) is not gated by time_set_mode, only by "
                f"cfg_alarm_enable && r_second_tick, and the tick divider keeps running "
                f"regardless of time_set_mode"
            )

            self.log.info("GH#56-G Alarm not during time_set_mode test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-G Alarm not during time_set_mode test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # H. Address decode: unmapped/aliased addresses must drop + PSLVERR
    # ------------------------------------------------------------------

    async def test_gh56_address_decode_pslverr(self) -> bool:
        """
        Only the mapped registers (0x000-0x030) are software-visible.
        Everything else in the 4KB APB window must be dropped (write
        ignored, read data 0) with PSLVERR - both the genuinely-reserved
        slots inside the regblock's own 6-bit decode space (0x034-0x3F,
        currently silently ack'd with no error) and every address whose
        upper bits alias into that space once truncated
        (rtc_config_regs.sv passes only regblk_addr[5:0] to the regblock -
        0x864 aliases RTC_ALARM_SEC at 0x024 and can silently corrupt the
        live register through an address no map documents).

        The alias-corruption probe targets RTC_ALARM_SEC (sw=rw, hw=r), not
        one of the six time registers - those are `hw=rw` with
        `hwif_in.RTC_*.next` wired unconditionally to rtc_core's live
        counter output (rtc_regs.sv's per-field mux: SW branch only on the
        literal write cycle, HW-mirror branch every other cycle), so a
        plain write outside cfg_time_set_mode is overwritten by the live
        counter on the very next cycle regardless of this defect - that is
        the correct, documented set-time protocol (GH#56-A/B), not a bug,
        and using one of those registers here would conflate the two
        defect classes and give a false setup-sanity failure.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-H Address decode / PSLVERR")
        self.log.info("=" * 80)

        try:
            failures = []

            # --- Reserved-but-in-window address (0x034: just past ALARM_MASK) ---
            write_pkt = await self.tb.write_register(0x034, 0xDEADBEEF)
            if getattr(write_pkt, 'pslverr', 0) != 1:
                failures.append("write to reserved 0x034 did not raise PSLVERR")

            read_pkt, data = await self.tb.read_register(0x034)
            if getattr(read_pkt, 'pslverr', 0) != 1:
                failures.append("read from reserved 0x034 did not raise PSLVERR")

            # --- Alias corruption: 0x864 aliases RTC_ALARM_SEC (0x864 & 0x3F == 0x24) ---
            await self.tb.write_register(RTCRegisterMap.RTC_ALARM_SEC, 0x11)
            _, sentinel_readback = await self.tb.read_register(RTCRegisterMap.RTC_ALARM_SEC)
            if (sentinel_readback & 0xFF) != 0x11:
                failures.append(
                    f"setup sanity check failed: canonical RTC_ALARM_SEC write/read-back "
                    f"mismatch (wrote 0x11, read 0x{sentinel_readback & 0xFF:02x})"
                )

            alias_pkt = await self.tb.write_register(0x864, 0x22)
            if getattr(alias_pkt, 'pslverr', 0) != 1:
                failures.append("write to alias address 0x864 did not raise PSLVERR")

            _, canonical_after = await self.tb.read_register(RTCRegisterMap.RTC_ALARM_SEC)
            if (canonical_after & 0xFF) != 0x11:
                failures.append(
                    f"canonical RTC_ALARM_SEC (0x024) changed from 0x11 to "
                    f"0x{canonical_after & 0xFF:02x} after a write to the unmapped alias 0x864 "
                    f"- the alias was routed through to the real register instead of dropped"
                )

            for f in failures:
                self.log.error(f"  {f}")

            assert not failures, "; ".join(failures)

            self.log.info("GH#56-H Address decode / PSLVERR test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-H Address decode / PSLVERR test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # I. rtc_resetn must actually reset the rtc domain (round_2 item 5)
    # ------------------------------------------------------------------

    async def test_gh56_rtc_resetn_guard(self) -> bool:
        """
        Asserting rtc_resetn must reset rtc_core's counting registers to
        their reset values, without disturbing the pclk-domain (presetn)
        registers. This is a REAL assertion, not a log-only guard, per the
        task brief's rule ("log-only unless the TB can drive it") - the TB
        CAN drive dut.rtc_resetn directly, and apb4_rtc.sv's RTL confirms
        the port is entirely unconnected (never referenced anywhere in the
        module body after its declaration), so this is expected to fail
        deterministically, not probabilistically.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-I rtc_resetn guard")
        self.log.info("=" * 80)

        try:
            await self._enable_production_mode(bcd=False, hour_12=False)

            # Distinguishable non-reset-value state.
            await self.tb.force_time_registers(seconds=0x33, minutes=0x44, hours=0x05,
                                                day=0x09, month=0x07, year=0x21)

            # Sanity: CONFIG (a presetn-domain register) currently reads the
            # value this test just wrote via _enable_production_mode().
            _, config_before = await self.tb.read_register(RTCRegisterMap.RTC_CONFIG)

            self.tb.dut.rtc_resetn.value = 0
            await ClockCycles(self.tb.pclk, 50)
            self.tb.dut.rtc_resetn.value = 1
            await ClockCycles(self.tb.pclk, 5)

            after = self.tb.read_time_registers_whitebox()
            _, config_after = await self.tb.read_register(RTCRegisterMap.RTC_CONFIG)

            self.log.info(f"  rtc-domain time regs after rtc_resetn pulse: {after} (reset values: all 0x00 "
                           f"except day/month=0x01)")
            self.log.info(f"  CONFIG before={config_before:#x} after={config_after:#x} (should be unaffected)")

            assert config_after == config_before, (
                "CONFIG (a presetn-domain register) changed after toggling rtc_resetn alone - "
                "unexpected coupling between the two reset domains"
            )

            reset_expected = {'seconds': 0, 'minutes': 0, 'hours': 0, 'day': 1, 'month': 1, 'year': 0}
            assert after == reset_expected, (
                f"rtc_core's counting registers were NOT reset by asserting rtc_resetn "
                f"(expected {reset_expected}, still hold {after}) - apb4_rtc.sv declares "
                f"rtc_resetn as a port but never wires it to anything"
            )

            self.log.info("GH#56-I rtc_resetn guard test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-I rtc_resetn guard test FAILED: {e}")
            return False
        finally:
            self.tb.dut.rtc_resetn.value = 1

    # ========================================================================
    # Coordinator direction, 2026-09-09: four RED tests against the landed
    # (uncommitted) GH#56 RTL follow-up. This RTL rewrite (rtc_core.sv,
    # rtc_config_regs.sv, rtc_regs.rdl) addresses contracts A-I above via a
    # real toggle-based commit handshake (the CDC primitive rtc_core.sv
    # instantiates for it - not named here, since it has already changed
    # once during this review) for the time-set commit, a coherency window
    # for multi-register reads, and edge-detected status
    # events - see rtc_core.sv's own "CLOCK DOMAINS" header comment. These
    # four tests target defects found reviewing THAT fix; a further RTL
    # follow-up (not authored here - no rtl/** edits) lands after this run.
    #
    # Commit latency budget: the new protocol's commit is a real closed-loop
    # CDC round trip (~5 selected_clk cycles each way plus SYNC_STAGES=3
    # synchronizer latency on each side) - at this suite's 10:1 ratio, order
    # 100-150 pclk cycles. COMMIT_SETTLE_CYCLES budgets well past that.
    # ========================================================================

    COMMIT_SETTLE_CYCLES = 220   # ~20 rtc_clk at the 10:1 test ratio

    # ------------------------------------------------------------------
    # 1. One-sided reset must not fabricate (or silently replay) a commit
    # ------------------------------------------------------------------

    async def test_gh56_one_sided_reset_no_phantom_commit(self) -> bool:
        """
        The time-set commit crosses pclk (presetn domain) -> counter domain
        (rtc_resetn domain) via the commit handshake (rtc_core.sv's CDC
        primitive for it - deliberately not named here; it has already
        changed once during this review, and hardcoding a module name in a
        comment is exactly the kind of doc that goes stale). Per the CDC
        library's own warning (rtl/cdc/CLAUDE.md, "Read the reset section before
        choosing a handshake"): if the two domains reset independently, the
        handshake can fabricate a transfer out of an idle link. Concretely -
        r_req_tog (source/presetn domain) and its synchronizer chain
        (destination/rtc_resetn domain) only agree on "no event happened"
        because both sides moved together; resetting one side alone makes
        the un-reset side's synchronizer see the OTHER side's toggle bit
        snap back to 0 as if it were a brand-new request.

        Main leg: presetn pulsed alone (rtc_resetn held high). Contract: the
        counters keep running the previously committed time - day and month
        must never read 0. Today the phantom event carries whatever
        r_src_data_hold holds after the SAME presetn reset zeroed it, so the
        counters load all-zero (day=0, month=0) -> RED.

        Mirror leg: rtc_resetn pulsed alone (presetn held high). Contract:
        after release the counters read the reset default (2000-01-01
        00:00:00, time_valid=0) and STAY there - no silently reloading the
        last committed time a few counter clocks later. Today the
        destination-side synchronizer resets to 0 while the source's
        (un-reset) req toggle is still at its old non-zero value, which the
        freshly-reset destination reads as a new request and replays the
        stale committed data -> RED.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-1 One-sided reset - no phantom commit")
        self.log.info("=" * 80)

        try:
            failures = []

            # ---------------- Main leg: presetn alone ----------------
            # A full (both-domains) reset first, so the commit handshake's
            # req/ack state both start at a known idle - without this,
            # whether the presetn-only pulse below actually disturbs
            # anything observable depends on how many commits earlier tests
            # in this same simulation happened to issue, which would make
            # the reproduction here a coin flip instead of deterministic.
            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await self.tb.wait_clocks('pclk', 5)

            await self._enable_production_mode(bcd=False, hour_12=False)
            set_a = {'seconds': 10, 'minutes': 20, 'hours': 5, 'day': 15, 'month': 6, 'year': 25}
            await self.tb.set_time(**set_a)
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

            before = await self.tb.read_time()
            self.log.info(f"  main leg: time before the presetn-only pulse: {before}")
            if before != set_a:
                failures.append(
                    f"main leg setup sanity check failed: committed {set_a}, read back {before} "
                    f"(before touching either reset - not this contract's own finding)"
                )

            await self.tb.assert_presetn()
            await ClockCycles(self.tb.pclk, 20)
            await self.tb.deassert_presetn()

            # presetn also reset RTC_CONFIG (it lives in the presetn domain) -
            # restore it. This is expected, ordinary recovery, not part of
            # what this test is checking.
            await self._enable_production_mode(bcd=False, hour_12=False)

            # No natural tick can occur in this short a window (the
            # production divider needs 32768 selected_clk edges), so the
            # correct readback is EXACTLY the committed time, unchanged.
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
            after = await self.tb.read_time()
            status_after = await self.tb.read_status()
            self.log.info(f"  main leg: time after presetn-only pulse + refill: {after}")

            if after['day'] == 0 or after['month'] == 0:
                failures.append(
                    f"main leg: day/month read 0 after a presetn-only reset "
                    f"(after={after}) - the one-sided reset fabricated a commit of "
                    f"all-zero data (phantom request event in the commit handshake)"
                )
            if after != set_a:
                failures.append(
                    f"main leg: time changed from the committed {set_a} to {after} after a "
                    f"presetn-only pulse with no natural tick possible in the window"
                )
            if not status_after['time_valid']:
                failures.append("main leg: status_time_valid dropped after a presetn-only pulse")

            # ---------------- Mirror leg: rtc_resetn alone ----------------
            # Same determinism concern as the main leg above (the mirror
            # leg's bug also depends on req/ack toggle parity) - a full
            # reset first, then exactly one commit, so r_req_tog is a known
            # 1 (not whatever parity the main leg above happened to leave).
            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await self.tb.wait_clocks('pclk', 5)
            await self._enable_production_mode(bcd=False, hour_12=False)

            set_b = {'seconds': 45, 'minutes': 33, 'hours': 17, 'day': 9, 'month': 7, 'year': 87}
            await self.tb.set_time(**set_b)
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

            before_b = await self.tb.read_time()
            if before_b != set_b:
                failures.append(
                    f"mirror leg setup sanity check failed: committed {set_b}, read back "
                    f"{before_b} (before touching either reset - not this contract's own finding)"
                )

            await self.tb.assert_rtc_resetn()
            await ClockCycles(self.tb.pclk, 20)
            await self.tb.deassert_rtc_resetn()

            # Give the (illegitimate) spurious reload every chance to happen
            # before checking - the contract is that it must NOT, however
            # long software waits afterward.
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
            reset_default = {'seconds': 0, 'minutes': 0, 'hours': 0, 'day': 1, 'month': 1, 'year': 0}
            after_b = await self.tb.read_time()
            status_b = await self.tb.read_status()
            self.log.info(f"  mirror leg: time after rtc_resetn-only pulse + settle: {after_b}")

            if after_b != reset_default:
                failures.append(
                    f"mirror leg: expected the reset default {reset_default} after an "
                    f"rtc_resetn-only pulse, got {after_b} - the stale (un-reset) commit "
                    f"handshake state on the presetn side was replayed into the "
                    f"freshly-reset destination as a phantom request"
                )
            if status_b['time_valid']:
                failures.append("mirror leg: status_time_valid is set after an rtc_resetn-only pulse")

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-1 One-sided reset test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-1 One-sided reset test FAILED: {e}")
            return False
        finally:
            self.tb.dut.rtc_resetn.value = 1
            self.tb.dut.presetn.value = 1

    # ------------------------------------------------------------------
    # 2. Polling RTC_SECONDS alone must still see ticks
    # ------------------------------------------------------------------

    async def test_gh56_polling_seconds_sees_ticks(self) -> bool:
        """
        Reading ONLY RTC_SECONDS in a tight loop must still observe the
        value changing at each tick - a poll loop is a legitimate way to
        read the clock (the read-coherency-window contract explicitly says
        "reading RTC_SECONDS again always re-latches, so polling it never
        sees a frozen value"). Today the coherency window opens on the
        first SECONDS read and is only supposed to close on a YEAR read (or
        BURST_TIMEOUT) - but each subsequent SECONDS-only read ALSO matches
        `w_seconds_rd_req` and re-arms the window (resets r_burst_timer to
        0), so a loop that never reads YEAR keeps the window open forever
        and the mirror (`w_mirror_en`) never re-enables -> the loop sees the
        same value forever -> RED.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-2 Polling RTC_SECONDS alone sees ticks")
        self.log.info("=" * 80)

        try:
            await self._enable_production_mode(bcd=False, hour_12=False)
            await self.tb.set_time(seconds=0, minutes=0, hours=0, day=1, month=1, year=25)
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

            _, v0 = await self.tb.read_register(RTCRegisterMap.RTC_SECONDS)
            v_prev = v0 & 0xFF
            self.log.info(f"  seconds before any forced tick: {v_prev}")

            failures = []
            for tick_num in range(2):
                await self.tb.force_divider_near_target(clock_select=0, remaining_cycles=2)
                # Tight loop: nothing but back-to-back RTC_SECONDS reads,
                # spanning the forced tick.
                seen = []
                for _ in range(12):
                    _, v = await self.tb.read_register(RTCRegisterMap.RTC_SECONDS)
                    seen.append(v & 0xFF)
                v_last = seen[-1]
                self.log.info(f"  tick {tick_num}: seconds-only poll sequence: {seen}")

                if v_last == v_prev:
                    failures.append(
                        f"tick {tick_num}: a tight RTC_SECONDS-only poll loop still reads "
                        f"{v_last} (unchanged from {v_prev} before this tick) - the coherency "
                        f"window opened by the first SECONDS read was re-armed by every "
                        f"subsequent SECONDS read and never closed, so the mirror never "
                        f"re-enabled"
                    )
                v_prev = v_last

            # After the tight loop, a proper burst (ending on YEAR) must
            # close the window and show the actual current time.
            _, s = await self.tb.read_register(RTCRegisterMap.RTC_SECONDS)
            for addr in (RTCRegisterMap.RTC_MINUTES, RTCRegisterMap.RTC_HOURS,
                         RTCRegisterMap.RTC_DAY, RTCRegisterMap.RTC_MONTH):
                await self.tb.read_register(addr)
            _, y = await self.tb.read_register(RTCRegisterMap.RTC_YEAR)
            whitebox = self.tb.read_time_registers_whitebox()
            self.log.info(f"  closing burst: seconds={s & 0xFF} year={y & 0xFF} whitebox={whitebox}")

            if (s & 0xFF) != whitebox['seconds']:
                failures.append(
                    f"a full SECONDS..YEAR burst after the poll loop read seconds="
                    f"{s & 0xFF}, but the counter domain currently holds "
                    f"{whitebox['seconds']} - the burst did not show the current time"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-2 Polling RTC_SECONDS test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-2 Polling RTC_SECONDS test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # 3. Alarm must fire at the moment the readable clock shows the value
    # ------------------------------------------------------------------

    async def test_gh56_alarm_fires_at_readable_time(self) -> bool:
        """
        The alarm must assert at the SAME tick that makes the readable
        (shadow) clock show the alarm value - not one tick later. 24h
        binary, seconds-match only, alarm=30, time set to 00:00:28.

        rtc_core's alarm comparator evaluates `r_seconds` (the PRE-update
        counter) on the SAME `w_div_rollover` edge that also updates the
        counter to its NEXT value and publishes that NEXT value into the
        coherent snapshot (r_snap_seconds <= w_next_seconds). So the tick
        that makes the readable clock first show 30 (r_seconds going
        29->30) compares the OLD value (29) against the alarm (30) - no
        match - and the tick after THAT (r_seconds going 30->31) is the one
        that finally matches (comparing 30 against 30), by which time the
        published snapshot already shows 31. Two RED signatures from one
        root cause:
          - at the tick that makes seconds==30, the alarm flag is not yet
            set (it sets one tick later than the contract requires);
          - by the time the flag DOES set, RTC_SECONDS reads 31, not 30.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-3 Alarm fires at the readable time")
        self.log.info("=" * 80)

        try:
            failures = []

            await self._enable_production_mode(bcd=False, hour_12=False)
            await self.tb.set_time(seconds=28, minutes=0, hours=0, day=1, month=1, year=25)
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

            await self.tb.set_alarm(seconds=30, minutes=0, hours=0,
                                     sec_match=True, min_match=False, hour_match=False)
            await self.tb.enable_alarm(enable=True, enable_interrupt=False)
            await self.tb.clear_status_flags(clear_alarm=True)
            await ClockCycles(self.tb.pclk, 10)

            time0 = await self.tb.read_time()
            self.log.info(f"  time after commit + alarm programming: {time0}")

            # Tick A: 28 -> 29 (no match expected either way - sanity only)
            await self.tb.force_divider_near_target(clock_select=0, remaining_cycles=2)
            await ClockCycles(self.tb.pclk, 40)
            time_a = await self.tb.read_time()
            status_a = await self.tb.read_status()
            self.log.info(f"  tick A: time={time_a} alarm_flag={status_a['alarm_flag']}")
            if time_a['seconds'] != 29:
                failures.append(f"tick A setup sanity check failed: seconds={time_a['seconds']}, expected 29")

            # Tick B: 29 -> 30 - the readable clock now shows the alarm
            # value. CONTRACT: the alarm flag must already be set here.
            await self.tb.force_divider_near_target(clock_select=0, remaining_cycles=2)
            await ClockCycles(self.tb.pclk, 40)
            time_b = await self.tb.read_time()
            status_b = await self.tb.read_status()
            self.log.info(f"  tick B: time={time_b} alarm_flag={status_b['alarm_flag']}")
            if time_b['seconds'] != 30:
                failures.append(f"tick B setup sanity check failed: seconds={time_b['seconds']}, expected 30")
            if not status_b['alarm_flag']:
                failures.append(
                    "tick B: RTC_SECONDS reads 30 (the alarm value) but status_alarm_flag is "
                    "NOT set yet - the comparator ran against the pre-advance (29) counter, "
                    "one tick behind the readable clock"
                )

            # The flag is sticky W1C: clear it after tick B so tick C can prove
            # there is no late re-fire (the original RTL fired HERE, one tick
            # after the readable clock passed the alarm value).
            await self.tb.clear_status_flags(clear_alarm=True)
            await ClockCycles(self.tb.pclk, 10)
            status_b2 = await self.tb.read_status()
            if status_b2['alarm_flag']:
                failures.append("alarm flag did not clear on W1C after tick B")
            await self.tb.force_divider_near_target(clock_select=0, remaining_cycles=2)
            await ClockCycles(self.tb.pclk, 40)
            time_c = await self.tb.read_time()
            status_c = await self.tb.read_status()
            self.log.info(f"  tick C: time={time_c} alarm_flag={status_c['alarm_flag']}")
            if status_c['alarm_flag']:
                failures.append(
                    f"alarm flag re-set at tick C (RTC_SECONDS={time_c['seconds']}) - the alarm "
                    f"fired one tick after the readable clock passed the alarm value, not "
                    f"(only) at the moment it showed it"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-3 Alarm fires at the readable time test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-3 Alarm fires at the readable time test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # 4. A stalled commit (rtc_clk stopped) must report a timeout
    # ------------------------------------------------------------------

    async def test_gh56_commit_timeout_is_reported(self) -> bool:
        """
        A time-set commit attempted while rtc_clk is not toggling (crystal
        removed / oscillator fault, or simply clock_select=0 with no clock
        wired yet) cannot complete the commit handshake round trip -
        the destination side never sees the request. rtc_core.sv already
        has a bounded watchdog for exactly this
        (the commit handshake's TIMEOUT_CYCLES=COMMIT_TIMEOUT=65535,
        wired to w_commit_timeout, which does clear time_commit_busy) - but
        nothing surfaces the timeout to software: there is no
        status_commit_timeout output from rtc_core and no field in
        RTC_STATUS. Contract (per the RTL follow-up): RTC_STATUS.
        commit_timeout (RTCRegisterMap.STATUS_COMMIT_TIMEOUT, bit 4 - see
        its definition in rtc_tb.py) sets, sticky, W1C; time_valid stays 0
        (the commit never reached the counters); and a LATER commit, once
        rtc_clk is running again, still works.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-4 Commit timeout is reported")
        self.log.info("=" * 80)

        try:
            failures = []

            # Known-clean starting point: both domains reset, so time_valid
            # and every sticky status bit start at 0.
            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await self.tb.wait_clocks('pclk', 5)

            await self._enable_production_mode(bcd=False, hour_12=False)

            self.tb.stop_rtc_clk()
            self.log.info("  rtc_clk stopped - attempting a commit that cannot complete")

            await self.tb.set_time(seconds=12, minutes=34, hours=5, day=6, month=7, year=25)

            # COMMIT_TIMEOUT (rtc_core.sv) = 65535 pclk cycles; wait past it.
            # ~0.66 ms of sim time at this test's 10ns pclk period.
            await ClockCycles(self.tb.pclk, 65535 + 200)

            status = await self.tb.read_status()
            self.log.info(f"  status after the timeout window: {status}")

            _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            commit_timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)

            if not commit_timeout_bit:
                failures.append(
                    "RTC_STATUS.commit_timeout (bit 4) did not set after a commit stalled "
                    "past COMMIT_TIMEOUT with rtc_clk stopped - nothing reports the stall to "
                    "software today"
                )
            if status['time_valid']:
                failures.append(
                    "status_time_valid is set after a commit that never reached the "
                    "counters (rtc_clk was never running for it)"
                )

            # Recovery: a full reset, rtc_clk running again, and a fresh
            # commit must still work.
            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.start_rtc_clk()
            await self.tb.deassert_reset()
            await self.tb.wait_clocks('pclk', 5)

            await self._enable_production_mode(bcd=False, hour_12=False)
            recovery_time = {'seconds': 40, 'minutes': 15, 'hours': 8, 'day': 20, 'month': 3, 'year': 26}
            await self.tb.set_time(**recovery_time)
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

            after_recovery = await self.tb.read_time()
            status_recovery = await self.tb.read_status()
            self.log.info(f"  time after recovery commit: {after_recovery}")

            if after_recovery != recovery_time:
                failures.append(
                    f"a later commit with rtc_clk running again did not land: expected "
                    f"{recovery_time}, got {after_recovery} - the stalled attempt appears to "
                    f"have wedged the commit path rather than timing out cleanly"
                )
            if not status_recovery['time_valid']:
                failures.append("status_time_valid is not set after the recovery commit landed")

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-4 Commit timeout is reported test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-4 Commit timeout is reported test FAILED: {e}")
            return False
        finally:
            # Guarantee rtc_clk is running for whatever test runs next,
            # regardless of pass/fail above.
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()

    # ========================================================================
    # Coordinator direction, 2026-09-09 (re-review): four more RED tests
    # against a further re-review of the uncommitted GH#56 RTL follow-up.
    # The commit handshake primitive changed again during this review (from
    # a two-phase toggle handshake to a four-phase req/ack/req-clr/ack-clr
    # one - rtc_core.sv's own header names it; deliberately not repeated
    # here, for the same staleness reason as above) specifically to fix the
    # one-sided-reset defect tests 1's main/mirror legs above targeted. These
    # four tests are against NEW defects found reviewing that four-phase
    # version - a further RTL follow-up (not authored here - no rtl/** edits)
    # lands after this run.
    # ========================================================================

    # ------------------------------------------------------------------
    # 5. A timed-out commit must not be cancelled - it lands late, intact
    # ------------------------------------------------------------------

    async def test_gh56_timed_out_commit_lands_intact(self) -> bool:
        """
        Decided contract: a commit_timeout report means "no acknowledge
        arrived within the window", not "the transfer was thrown away". The
        staged data must stay held and the transfer must still land,
        unchanged, whenever the counter clock comes back - with no reset in
        between.

        Whitebox: commit a known, easily-distinguished time, then let
        rtc_clk (the counter-domain clock) run only 1-4 edges after the
        commit before stopping it (tb.stop_rtc_clk()) - too few for the
        request to even finish crossing the destination synchronizer, so
        the transfer is unambiguously still in flight, not already
        delivered. Wait past COMMIT_TIMEOUT with the clock stopped
        (commit_timeout sets, busy drops), then restart rtc_clk with NO
        reset of either domain and let it settle.

        Today rtc_core.sv's watchdog CANCELS the commit on timeout
        (r_commit_cancel -> w_commit_src_rst_n resets the handshake's
        source-side state, including the held data, for two pclk cycles) -
        the design contract this test encodes says that must not happen;
        an abandoned-but-not-cancelled transfer should simply deliver late.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-5 Timed-out commit lands intact (not cancelled)")
        self.log.info("=" * 80)

        try:
            failures = []

            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await self.tb.wait_clocks('pclk', 5)

            await self._enable_production_mode(bcd=False, hour_12=False)

            committed = {'seconds': 37, 'minutes': 22, 'hours': 14, 'day': 17, 'month': 9, 'year': 31}

            # Enter time_set_mode and stage the six fields - all plain APB
            # writes, no rtc_clk dependency (staging registers only mirror
            # off cfg_time_set_mode, not the counter clock).
            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, committed['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, committed['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, committed['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, committed['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, committed['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, committed['year'])
            await ClockCycles(self.tb.pclk, 5)

            # The commit: clear time_set_mode (falling edge). rtc_clk is
            # still running at this instant.
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)

            # Let the counter domain clock only a handful of edges - not
            # enough for the request to finish crossing (SYNC_STAGES=3 plus
            # the destination FSM's own steps).
            await ClockCycles(self.tb.dut.rtc_clk, 3)
            self.tb.stop_rtc_clk()
            self.log.info("  rtc_clk stopped ~3 edges after the commit - transfer still in flight")

            await ClockCycles(self.tb.pclk, 65535 + 200)

            status_after_timeout = await self.tb.read_status()
            _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
            self.log.info(f"  after the timeout window: commit_timeout={timeout_bit} "
                           f"status={status_after_timeout}")
            if not timeout_bit:
                failures.append(
                    "setup sanity check failed: commit_timeout never set with rtc_clk stopped "
                    "(not this contract's own finding - it means the transfer landed before "
                    "the clock was stopped, or COMMIT_TIMEOUT never fired)"
                )

            # Restart the counter clock with NO reset of either domain -
            # this is the whole point: an abandoned transfer must still be
            # deliverable, not require software to start over.
            await self.tb.start_rtc_clk()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

            landed = await self.tb.read_time()
            status_landed = await self.tb.read_status()
            self.log.info(f"  time after restarting rtc_clk (no reset): {landed} "
                           f"time_valid={status_landed['time_valid']}")

            if landed['day'] == 0 or landed['month'] == 0:
                failures.append(
                    f"day/month read 0 after the counter clock resumed post-timeout "
                    f"(landed={landed}) - the abandoned transfer was cancelled and a stale/"
                    f"zeroed retry was delivered instead of the original committed data"
                )
            if landed != committed:
                failures.append(
                    f"the committed time {committed} did not land intact once rtc_clk "
                    f"resumed (no reset in between) - got {landed}. The timeout watchdog "
                    f"CANCELS the transfer (resets the handshake's source-side state,  "
                    f"including the held data) instead of leaving it pending"
                )
            if not status_landed['time_valid']:
                failures.append("status_time_valid is not set after the delayed commit landed")

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-5 Timed-out commit lands intact test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-5 Timed-out commit lands intact test FAILED: {e}")
            return False
        finally:
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()

    # ------------------------------------------------------------------
    # 6. A retry after a timeout must land the retried (second) time
    # ------------------------------------------------------------------

    async def test_gh56_retry_after_timeout_lands(self) -> bool:
        """
        Commit A, let the counter domain clock enough edges to have LOADED
        the data (rtc_core's r_seconds..r_year already updated) but not
        finished the four-phase close-out (the source side is still
        waiting for the ack to fully round-trip), stop rtc_clk, wait past
        the timeout (which fires even though A already landed, because the
        source-side bookkeeping never saw the close-out complete), restart
        the clock, then commit a SECOND, different time B.

        Decided contract: B's request gets a REAL round trip to the
        destination and back - the source-side FSM must hold the request
        asserted for something close to a real crossing (multiple
        SYNC_STAGES-deep synchronizer delays each way), not satisfy it
        instantly off leftover state.

        Confirmed by a whitebox trace of the commit handshake's internal
        state (u_rtc_core.u_commit_cdc) across the restart+retry window:
        today, B's request is raised and immediately (the very next pclk
        cycle) treated as acknowledged - r_req_src drops after being held
        high for only ONE cycle, because the ack synchronizer is still
        reading the STALE ack level A's timeout-abandoned, never-cleanly-
        closed-out transfer left behind (the destination's own req/ack
        state, reset only on rtc_resetn, was never touched by the
        source-only cancel). B's request is "consumed" by that leftover
        state rather than by a real handshake with the destination -
        whether B's data happens to still land afterward (it can, since
        the source's data-hold register was never disturbed and a later,
        unrelated req/ack echo can deliver it) is incidental, not a
        property of the protocol working correctly.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-6 Retry after timeout lands the retried time")
        self.log.info("=" * 80)

        try:
            failures = []

            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await self.tb.wait_clocks('pclk', 5)

            await self._enable_production_mode(bcd=False, hour_12=False)

            time_a = {'seconds': 5, 'minutes': 10, 'hours': 3, 'day': 4, 'month': 2, 'year': 20}
            time_b = {'seconds': 50, 'minutes': 40, 'hours': 21, 'day': 28, 'month': 11, 'year': 44}

            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_a['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_a['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_a['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_a['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_a['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_a['year'])
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)

            # Enough counter-domain edges for the LOAD to have happened
            # (rtc_core.sv: "the load lands ~4-5 selected_clk cycles after
            # the commit"), but not the full ~7-cycle four-phase close-out.
            await ClockCycles(self.tb.dut.rtc_clk, 7)
            self.tb.stop_rtc_clk()
            self.log.info("  rtc_clk stopped ~7 edges after commit A - loaded but not closed out")

            await ClockCycles(self.tb.pclk, 65535 + 200)

            _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
            self.log.info(f"  commit A: commit_timeout after the wait={timeout_bit}")

            # commit_timeout is sticky (W1C) - clear A's EXPECTED timeout so
            # the check after B below is not just re-reading A's stale flag.
            await self.tb.write_register(RTCRegisterMap.RTC_STATUS, RTCRegisterMap.STATUS_COMMIT_TIMEOUT)

            # Stage B's six fields and enter time_set_mode WHILE rtc_clk is
            # still stopped - staging is pure APB (pclk-domain only), so
            # none of this depends on the counter clock. Only the ACTUAL
            # commit trigger (clearing time_set_mode) needs rtc_clk
            # running, so restarting the clock and clearing time_set_mode
            # in the very next step lands B's request as close as possible
            # to the clock's resumption - maximum overlap with whatever
            # A's timeout-abandoned close-out left mid-resolution. A
            # generous wait between restart and B's trigger (tried first)
            # gives that leftover state time to fully drain before B ever
            # starts, which does not exercise the race at all.
            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_b['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_b['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_b['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_b['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_b['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_b['year'])
            await ClockCycles(self.tb.pclk, 5)

            cdc = self.tb.dut.u_rtc_core.u_commit_cdc
            trace = []

            async def _tracer():
                for _ in range(60):
                    await RisingEdge(self.tb.pclk)
                    trace.append((
                        int(cdc.r_src_state.value), int(cdc.r_req_src.value),
                        int(cdc.r_dst_state.value), int(cdc.r_ack_dst.value),
                        int(self.tb.dut.u_rtc_core.r_commit_pend.value),
                        int(self.tb.dut.u_rtc_core.r_commit_busy.value),
                    ))

            tracer_task = cocotb.start_soon(_tracer())

            await self.tb.start_rtc_clk()
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)
            await tracer_task
            self.log.info("  (src_state,req_src,dst_state,ack_dst,commit_pend,commit_busy) per pclk "
                           f"cycle across restart+commit B: {trace}")

            # Find where req_src (index 1) first rises for B's request, and
            # how many consecutive cycles it stays high. A REAL crossing
            # needs on the order of 2*SYNC_STAGES (=6) selected_clk edges
            # each way (~60 pclk at this suite's 10:1 ratio) before the
            # source can legitimately see an ack and drop the request.
            # MIN_REAL_REQ_HOLD_CYCLES is set well below that (still a
            # generous floor, not a tight bound) so this only fires on the
            # "satisfied in ~1 cycle by leftover state" signature, not on
            # ordinary jitter in a genuine round trip.
            MIN_REAL_REQ_HOLD_CYCLES = 10
            req_rise = next((i for i, s in enumerate(trace) if s[1] == 1), None)
            req_hold = 0
            if req_rise is not None:
                for s in trace[req_rise:]:
                    if s[1] != 1:
                        break
                    req_hold += 1

            self.log.info(f"  B's req_src: first raised at trace index {req_rise}, "
                           f"held high for {req_hold} consecutive pclk cycle(s)")

            if req_rise is None:
                failures.append(
                    "B's commit never raised the commit handshake's request (req_src) at all "
                    "within the trace window - setup problem, not necessarily this contract's "
                    "own finding"
                )
            elif req_hold < MIN_REAL_REQ_HOLD_CYCLES:
                failures.append(
                    f"B's request (req_src) was held high for only {req_hold} pclk cycle(s) "
                    f"before being treated as acknowledged - far too fast for a real crossing "
                    f"to the destination and back (needs on the order of "
                    f"{MIN_REAL_REQ_HOLD_CYCLES}+ cycles). The ack synchronizer is still "
                    f"reading the STALE ack level left behind by A's timeout-abandoned, "
                    f"never-cleanly-closed-out transfer - B's request is satisfied by that "
                    f"leftover state instead of a genuine handshake with the destination"
                )

            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

            _, status_raw_b = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            timeout_bit_b = bool(status_raw_b & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
            final_time = await self.tb.read_time()
            self.log.info(f"  time after commit B: {final_time} commit_timeout={timeout_bit_b}")

            if timeout_bit_b:
                failures.append(
                    "commit_timeout is set again after commit B, which had a fully running "
                    "rtc_clk and should complete cleanly"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-6 Retry after timeout lands test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-6 Retry after timeout lands test FAILED: {e}")
            return False
        finally:
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()
            # This test deliberately leaves the commit handshake mid-retry
            # in the RED case, and even in the GREEN case a stray automatic
            # re-send of A can still be resolving after the assertions
            # above are checked - a full reset before the next test runs
            # is mandatory cleanup, not part of what this test checks.
            #
            # The release wait after deassert_reset() MUST cover
            # reset_sync's release synchronizer on selected_clk (rtc_clk in
            # production mode, SYNC_STAGES=3 edges = ~30 pclk at this
            # suite's 10:1 ratio) - the standard 5-pclk-cycle settle used
            # everywhere else in this TB assumes selected_clk=pclk (test
            # mode) and is not enough here. Without this, the next test's
            # whitebox force_time_registers() lands while w_ctr_rst_n is
            # still asserted and gets silently overwritten back to the
            # reset default on the next selected_clk edge - a real bug
            # this cleanup found in itself (2026-09-09).
            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

    # ------------------------------------------------------------------
    # 7. Reading RTC_SECONDS must latch the OTHER five at the same instant
    # ------------------------------------------------------------------

    async def test_gh56_seconds_read_latches_same_instant(self) -> bool:
        """
        Decided contract: reading RTC_SECONDS returns the live shadow
        seconds value and, in that SAME cycle, latches minutes/hours/day/
        month/year (and pm_indicator/time_valid) so every subsequent read
        belongs to the same instant as the seconds value just read - no
        open/close window, no timeout, just "the seconds read is the
        atomic snapshot point". Sweeps a forced tick across a window of
        pclk offsets around the RTC_SECONDS read of an otherwise-normal
        SECONDS..YEAR burst; every burst must be entirely the pre-tick
        snapshot or entirely the post-tick snapshot, never mixed (no
        seconds=00 paired with minutes=59, the still-open-a-cycle-late
        signature this suite's own module docstring names).
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-7 RTC_SECONDS read latches the same instant")
        self.log.info("=" * 80)

        pre = {'seconds': 59, 'minutes': 59, 'hours': 23, 'day': 31, 'month': 12, 'year': 25}
        post = {'seconds': 0, 'minutes': 0, 'hours': 0, 'day': 1, 'month': 1, 'year': 26}

        try:
            await self._enable_production_mode(bcd=False, hour_12=False)

            torn = []
            for k in range(1, 17):
                await self.tb.force_time_registers(**pre)
                await self.tb.force_divider_near_target(clock_select=0, remaining_cycles=k)
                await ClockCycles(self.tb.pclk, 2)

                burst = {}
                for name, addr in (('seconds', RTCRegisterMap.RTC_SECONDS),
                                    ('minutes', RTCRegisterMap.RTC_MINUTES),
                                    ('hours', RTCRegisterMap.RTC_HOURS),
                                    ('day', RTCRegisterMap.RTC_DAY),
                                    ('month', RTCRegisterMap.RTC_MONTH),
                                    ('year', RTCRegisterMap.RTC_YEAR)):
                    _, val = await self.tb.read_register(addr)
                    burst[name] = val & 0xFF

                coherent = (burst == pre) or (burst == post)
                self.log.info(f"  k={k:2d} burst={burst} coherent={coherent}")
                if not coherent:
                    torn.append((k, dict(burst)))

            assert not torn, (
                f"{len(torn)}/16 read bursts were torn (matched neither the pre-tick "
                f"snapshot {pre} nor the post-tick snapshot {post}) - the RTC_SECONDS read "
                f"did not latch the other five fields at the same instant its own value was "
                f"sampled: {torn[:4]}{'...' if len(torn) > 4 else ''}"
            )

            self.log.info("GH#56-7 RTC_SECONDS read latches the same instant test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-7 RTC_SECONDS read latches the same instant test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # 8. The divider must not run while time_set_mode is staging a time
    # ------------------------------------------------------------------

    async def test_gh56_no_tick_during_time_set_mode(self) -> bool:
        """
        Decided contract: the divider is HELD AT ZERO while time_set_mode
        is set - no second_tick, no rtc_second_irq, no alarm evaluation and
        no counter advance until the commit has loaded the new time; the
        first tick after a commit arrives one full second later, not
        whatever was left of the second in progress when time_set_mode was
        entered.

        Whitebox-forces the divider near rollover TWICE while time_set_mode
        stays asserted (so a free-running divider would tick twice), and
        also arms an alarm that matches the STAGED (pre-commit) time to
        check the comparator stays gated too. rtc_core.sv's divider only
        checks `!w_ctr_enable` to hold at zero - not time_set_mode - so
        today it free-runs underneath the staging registers.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-8 No tick during time_set_mode")
        self.log.info("=" * 80)

        try:
            failures = []

            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await self.tb.wait_clocks('pclk', 5)

            staged = {'seconds': 15, 'minutes': 30, 'hours': 9, 'day': 3, 'month': 6, 'year': 30}

            # Enable, arm an alarm that matches the time about to be
            # STAGED (not yet committed), then enter time_set_mode.
            await self._enable_production_mode(bcd=False, hour_12=False)
            await self.tb.set_alarm(seconds=staged['seconds'], minutes=staged['minutes'],
                                     hours=staged['hours'], sec_match=True, min_match=True, hour_match=True)
            await self.tb.enable_alarm(enable=True, enable_interrupt=True)
            await self.tb.clear_status_flags(clear_alarm=True, clear_tick=True)

            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, staged['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, staged['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, staged['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, staged['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, staged['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, staged['year'])
            await ClockCycles(self.tb.pclk, 10)

            # Two forced rollovers while STILL in time_set_mode - a
            # free-running divider ticks (and re-evaluates the alarm) at
            # each one.
            for i in range(2):
                await self.tb.force_divider_near_target(clock_select=0, remaining_cycles=2)
                await ClockCycles(self.tb.pclk, 40)

                status = await self.tb.read_status()
                irq = bool(self.tb.dut.rtc_second_irq.value)
                readback = {
                    'seconds': (await self.tb.read_register(RTCRegisterMap.RTC_SECONDS))[1] & 0xFF,
                    'minutes': (await self.tb.read_register(RTCRegisterMap.RTC_MINUTES))[1] & 0xFF,
                    'hours':   (await self.tb.read_register(RTCRegisterMap.RTC_HOURS))[1]   & 0xFF,
                    'day':     (await self.tb.read_register(RTCRegisterMap.RTC_DAY))[1]     & 0xFF,
                    'month':   (await self.tb.read_register(RTCRegisterMap.RTC_MONTH))[1]   & 0xFF,
                    'year':    (await self.tb.read_register(RTCRegisterMap.RTC_YEAR))[1]    & 0xFF,
                }
                self.log.info(f"  forced rollover {i} during time_set_mode: status={status} "
                               f"irq={irq} staged_readback={readback}")

                if status['second_tick']:
                    failures.append(
                        f"forced rollover {i}: STATUS.second_tick set while time_set_mode is "
                        f"still asserted - the divider is not held at zero during staging"
                    )
                if irq:
                    failures.append(f"forced rollover {i}: rtc_second_irq asserted during time_set_mode")
                if status['alarm_flag']:
                    failures.append(
                        f"forced rollover {i}: alarm flag set during time_set_mode even though "
                        f"the staged (pre-commit) time matches the alarm - the comparator is "
                        f"not gated off the free-running divider either"
                    )
                if readback != staged:
                    failures.append(
                        f"forced rollover {i}: staged registers read {readback}, expected the "
                        f"still-staged {staged} - reading a time register during time_set_mode "
                        f"must return the staged value, not a live/ticked one"
                    )

            # Commit, then confirm the first tick is a full second away (a
            # forced divider "1-away-from-target" must NOT immediately
            # tick on the very next edge - that would mean the divider
            # carried over instead of restarting on the commit).
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

            landed = await self.tb.read_time()
            self.log.info(f"  time after commit (time_set_mode cleared): {landed}")
            if landed != staged:
                failures.append(
                    f"the staged time {staged} did not land on commit - got {landed} "
                    f"(setup sanity check, not necessarily this contract's own finding)"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-8 No tick during time_set_mode test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-8 No tick during time_set_mode test FAILED: {e}")
            return False

    # ========================================================================
    # Coordinator direction, 2026-09-09 (third re-review): four more RED
    # tests against a third re-review of the uncommitted GH#56 RTL follow-up.
    # The commit handshake's cancel-on-timeout mechanism from the previous
    # round is GONE - rtc_core.sv's u_commit_cdc source side is now reset by
    # `rst_n` (presetn) directly, with no local "cancel" reset in between,
    # and the watchdog no longer withdraws an abandoned request; it only
    # reports commit_timeout and leaves the transfer pending (see
    # rtc_core.sv's own header, "WATCHDOG, AND WHAT IT DOES NOT DO"). These
    # four tests are against defects found reviewing THAT version - a
    # further RTL follow-up (not authored here - no rtl/** edits) lands
    # after this run.
    #
    # GH#56-6 (test_gh56_retry_after_timeout_lands, previous round) exercised
    # the NOW-REMOVED cancel mechanism via a stopped-clock timeout; it is
    # left in place as-is (not part of this round's deliverable) and its
    # outcome against this new RTL is reported factually in the run summary
    # rather than redesigned here.
    # ========================================================================

    # ------------------------------------------------------------------
    # 9. A presetn-only reset with a commit mid-flight must not zero it
    # ------------------------------------------------------------------

    async def test_gh56_presetn_with_commit_in_flight_lands_intact(self) -> bool:
        """
        Decided contract: the commit handshake's source side is reset only
        when BOTH domains are reset (presetn AND rtc_resetn, the latter
        synchronized into pclk). A presetn-only reset with a commit in
        flight lets that commit land intact - it must never deliver zeros
        and must never leave a stale acknowledge that could satisfy the
        next commit early.

        Commits a known time, waits ~2 rtc_clk periods (long enough for the
        request to be somewhere inside the destination's synchronizer, not
        yet latched into r_dst_data), pulses ONLY presetn, releases, and
        waits for the commit to land.

        Today rst_n resets u_commit_cdc's source side directly - including
        r_src_data_hold, a plain register with no reset protection from the
        destination's perspective. The request LEVEL that is already
        propagating through the destination's multi-stage synchronizer
        keeps going (that synchronizer lives in the un-reset rtc_resetn
        domain) and is eventually acted on, but by then r_src_data_hold has
        already been zeroed - so the destination latches zeros instead of
        the committed time.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-9 presetn with a commit in flight lands intact")
        self.log.info("=" * 80)

        try:
            failures = []

            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

            await self._enable_production_mode(bcd=False, hour_12=False)

            committed = {'seconds': 41, 'minutes': 26, 'hours': 11, 'day': 23, 'month': 8, 'year': 33}

            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, committed['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, committed['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, committed['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, committed['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, committed['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, committed['year'])
            await ClockCycles(self.tb.pclk, 5)
            # The commit: clear time_set_mode.
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)

            # ~2 rtc_clk periods later - the request is somewhere inside the
            # destination's 3-stage synchronizer, not yet acted on.
            await ClockCycles(self.tb.dut.rtc_clk, 2)

            await self.tb.assert_presetn()
            await ClockCycles(self.tb.pclk, 20)
            await self.tb.deassert_presetn()

            # presetn also reset RTC_CONFIG - restore it (ordinary recovery,
            # not part of what this test checks).
            await self._enable_production_mode(bcd=False, hour_12=False)

            # Wait for the commit to land (~10 rtc_clk periods).
            await ClockCycles(self.tb.dut.rtc_clk, 10)
            await ClockCycles(self.tb.pclk, 20)

            landed = await self.tb.read_time()
            status = await self.tb.read_status()
            self.log.info(f"  time after the presetn-only pulse settled: {landed} "
                           f"time_valid={status['time_valid']}")

            if landed['day'] == 0 or landed['month'] == 0:
                failures.append(
                    f"day/month read 0 after a presetn-only reset with a commit mid-flight "
                    f"(landed={landed}) - the source-side data-hold register was zeroed by "
                    f"the reset while the request was still propagating through the "
                    f"destination's synchronizer, and the destination latched the zeros"
                )
            if landed != committed:
                failures.append(
                    f"the committed time {committed} did not land intact - got {landed} "
                    f"after a presetn-only reset with the commit mid-flight"
                )
            if not status['time_valid']:
                failures.append("status_time_valid is not set after the in-flight commit settled")

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-9 presetn with a commit in flight test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-9 presetn with a commit in flight test FAILED: {e}")
            return False
        finally:
            self.tb.dut.presetn.value = 1
            self.tb.dut.rtc_resetn.value = 1

    # ------------------------------------------------------------------
    # 10. A presetn-only reset after the destination has acked must not
    #     leave a stale acknowledge that satisfies the NEXT commit early
    # ------------------------------------------------------------------

    async def test_gh56_presetn_after_ack_no_stale_ack(self) -> bool:
        """
        Commit A, wait until the destination has loaded and acked but
        before the source has cleared its own request (white-box: ~6-8
        rtc_clk after the commit is enough for u_commit_cdc's destination
        side to reach D_WAIT_REQ_CLR / r_ack_dst=1). Pulse ONLY presetn,
        release, and immediately issue commit B.

        Decided contract: B's request gets a REAL round trip - the source
        FSM must hold req_src asserted for something on the order of a
        real crossing (whitebox-observable, several rtc_clk periods' worth
        of pclk cycles), not satisfy it off leftover destination state.

        Today presetn resets the source side (r_req_src, r_src_state) back
        to idle but the destination side (reset only by rtc_resetn, which
        this test does not touch) is left exactly where it was - still
        showing ack=1, still waiting for the OLD request to drop. B's fresh
        request is read by the source's ack synchronizer as already
        acknowledged in about one pclk cycle, and never reaches the
        destination for a genuine transfer.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-10 presetn after ack leaves no stale ack for the next commit")
        self.log.info("=" * 80)

        try:
            failures = []

            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

            await self._enable_production_mode(bcd=False, hour_12=False)

            time_a = {'seconds': 3, 'minutes': 7, 'hours': 2, 'day': 6, 'month': 1, 'year': 21}
            time_b = {'seconds': 55, 'minutes': 44, 'hours': 19, 'day': 30, 'month': 10, 'year': 45}

            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_a['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_a['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_a['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_a['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_a['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_a['year'])
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)

            # ~6-8 rtc_clk after the commit: destination loaded and acked,
            # source has not yet cleared its own request.
            await ClockCycles(self.tb.dut.rtc_clk, 7)

            cdc = self.tb.dut.u_rtc_core.u_commit_cdc
            self.log.info(f"  pre-reset CDC state: src_state={int(cdc.r_src_state.value)} "
                           f"req_src={int(cdc.r_req_src.value)} dst_state={int(cdc.r_dst_state.value)} "
                           f"ack_dst={int(cdc.r_ack_dst.value)}")

            # Freeze the destination here (whitebox stop of rtc_clk, NOT a
            # reset of either domain) so its stale ack level cannot drain
            # away naturally while B is staged below - staging six fields
            # over individual APB writes takes ~80-170 pclk cycles (~8-17
            # rtc_clk periods), far longer than the ~3 rtc_clk periods the
            # destination's own req/ack synchronizers need to notice A's
            # (already-dropped) request and clean up on their own. Without
            # this, the race this test is checking for cannot be reached at
            # all - the destination has already returned to a clean D_IDLE
            # by the time B's commit fires, and this test passes for the
            # wrong reason (masking the defect, not exercising it).
            self.tb.stop_rtc_clk()

            await self.tb.assert_presetn()
            await ClockCycles(self.tb.pclk, 20)
            await self.tb.deassert_presetn()
            await self._enable_production_mode(bcd=False, hour_12=False)

            # Stage B while the destination is still frozen mid-close-out.
            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_b['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_b['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_b['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_b['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_b['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_b['year'])
            await ClockCycles(self.tb.pclk, 5)

            trace = []

            async def _tracer():
                for _ in range(60):
                    await RisingEdge(self.tb.pclk)
                    trace.append(int(cdc.r_req_src.value))

            tracer_task = cocotb.start_soon(_tracer())
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)
            # Restart rtc_clk a few pclk cycles into the trace, once B's
            # request is up - the destination needs a running clock to
            # ever respond, genuinely or falsely.
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.start_rtc_clk()
            await tracer_task
            self.log.info(f"  req_src per pclk cycle across B's commit: {trace}")

            MIN_REAL_REQ_HOLD_CYCLES = 10
            req_rise = next((i for i, v in enumerate(trace) if v == 1), None)
            req_hold = 0
            if req_rise is not None:
                for v in trace[req_rise:]:
                    if v != 1:
                        break
                    req_hold += 1
            self.log.info(f"  B's req_src: first raised at index {req_rise}, held {req_hold} cycle(s)")

            if req_rise is None:
                failures.append("B's commit never raised req_src within the trace window")
            elif req_hold < MIN_REAL_REQ_HOLD_CYCLES:
                failures.append(
                    f"B's request (req_src) was held high for only {req_hold} pclk cycle(s) "
                    f"before being treated as acknowledged - too fast for a real crossing "
                    f"(needs {MIN_REAL_REQ_HOLD_CYCLES}+). A presetn-only reset left the "
                    f"destination's ack level from A behind (destination is reset only by "
                    f"rtc_resetn), and B's fresh request is satisfied by that stale ack "
                    f"instead of a genuine round trip"
                )

            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
            landed = await self.tb.read_time()
            self.log.info(f"  time after commit B settled: {landed}")
            if landed != time_b:
                failures.append(f"commit B ({time_b}) did not land - final time is {landed}")

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-10 presetn after ack test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-10 presetn after ack test FAILED: {e}")
            return False
        finally:
            self.tb.dut.presetn.value = 1
            self.tb.dut.rtc_resetn.value = 1
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()

    # ------------------------------------------------------------------
    # 11. A commit queued behind a timed-out one must keep busy set and
    #     keep the staged registers showing ITS OWN values
    # ------------------------------------------------------------------

    async def test_gh56_retry_during_timed_out_stall_keeps_staged(self) -> bool:
        """
        Stop rtc_clk, commit A (it can never be acknowledged), wait past
        COMMIT_TIMEOUT (commit_timeout sets - W1C it so the checks below
        are not just re-reading A's flag). With the clock STILL stopped,
        stage and commit B (a different time).

        Decided contract: time_commit_busy stays SET for as long as B (or
        the still-pending A) has not landed, and RTC_SECONDS..YEAR keep
        reading B's STAGED values - not the live counter mirror - for as
        long as the clock is stopped. Then restart rtc_clk: A lands, then
        B lands; the final readable time is B, and commit_timeout does not
        set again for B.

        Today time_commit_busy is cleared by the timeout LEVEL, not its
        rising edge - `if (r_commit_busy && w_commit_timeout) busy<=0`
        re-fires on every cycle the (still-stalled) watchdog level is high,
        so busy drops again right after B's commit sets it, the mirror
        re-enables (rtc_config_regs' w_mirror_en depends on
        !time_commit_busy) and overwrites B's staged registers with the
        live shadow instead of holding B's values.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-11 Retry during a timed-out stall keeps staged values")
        self.log.info("=" * 80)

        try:
            failures = []

            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

            await self._enable_production_mode(bcd=False, hour_12=False)

            time_a = {'seconds': 12, 'minutes': 8, 'hours': 4, 'day': 11, 'month': 3, 'year': 22}
            time_b = {'seconds': 48, 'minutes': 36, 'hours': 20, 'day': 27, 'month': 9, 'year': 41}

            self.tb.stop_rtc_clk()
            self.log.info("  rtc_clk stopped - committing A (can never be acknowledged)")

            await self.tb.set_time(**time_a)

            await ClockCycles(self.tb.pclk, 65535 + 200)

            _, status_raw_a = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            timeout_bit_a = bool(status_raw_a & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
            self.log.info(f"  commit A: commit_timeout after the wait={timeout_bit_a}")
            if not timeout_bit_a:
                failures.append(
                    "setup sanity check failed: commit_timeout never set for A with rtc_clk "
                    "stopped (not this contract's own finding)"
                )
            await self.tb.write_register(RTCRegisterMap.RTC_STATUS, RTCRegisterMap.STATUS_COMMIT_TIMEOUT)

            # Still stopped: stage and commit B.
            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_b['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_b['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_b['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_b['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_b['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_b['year'])
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)
            await ClockCycles(self.tb.pclk, 10)

            # While still stopped: busy must stay set, staged regs must
            # keep reading B's values.
            busy_drops = []
            staged_wrong = []
            for i in range(20):
                busy = int(self.tb.dut.u_rtc_core.r_commit_busy.value)
                readback = {
                    'seconds': (await self.tb.read_register(RTCRegisterMap.RTC_SECONDS))[1] & 0xFF,
                    'minutes': (await self.tb.read_register(RTCRegisterMap.RTC_MINUTES))[1] & 0xFF,
                    'hours':   (await self.tb.read_register(RTCRegisterMap.RTC_HOURS))[1]   & 0xFF,
                    'day':     (await self.tb.read_register(RTCRegisterMap.RTC_DAY))[1]     & 0xFF,
                    'month':   (await self.tb.read_register(RTCRegisterMap.RTC_MONTH))[1]   & 0xFF,
                    'year':    (await self.tb.read_register(RTCRegisterMap.RTC_YEAR))[1]    & 0xFF,
                }
                if not busy:
                    busy_drops.append(i)
                if readback != time_b:
                    staged_wrong.append((i, dict(readback)))
                await ClockCycles(self.tb.pclk, 10)

            self.log.info(f"  while stopped: busy_drops(sample idx)={busy_drops[:5]} "
                           f"staged_wrong(sample idx)={[s[0] for s in staged_wrong[:5]]}")

            if busy_drops:
                failures.append(
                    f"time_commit_busy dropped while B's commit was still pending and rtc_clk "
                    f"was stopped (at sample(s) {busy_drops[:5]}) - busy is cleared by the "
                    f"timeout LEVEL (still asserted for A's stall) instead of its rising edge"
                )
            if staged_wrong:
                failures.append(
                    f"RTC_SECONDS..YEAR did not keep reading B's staged values "
                    f"{time_b} while rtc_clk was stopped - first wrong readback at sample "
                    f"{staged_wrong[0][0]}: {staged_wrong[0][1]} - the counter mirror "
                    f"re-enabled while B's commit was still pending"
                )

            # Restart and let both land; the final time must be B.
            await self.tb.start_rtc_clk()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES * 2)

            final_time = await self.tb.read_time()
            _, status_raw_b = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            timeout_bit_b = bool(status_raw_b & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
            self.log.info(f"  after restart: final_time={final_time} commit_timeout={timeout_bit_b}")

            if final_time != time_b:
                failures.append(
                    f"final readable time is {final_time}, expected B's committed time "
                    f"{time_b} (A was {time_a})"
                )
            if timeout_bit_b:
                failures.append("commit_timeout is set again for B, which should complete cleanly "
                                 "once rtc_clk resumes")

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-11 Retry during timed-out stall test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-11 Retry during timed-out stall test FAILED: {e}")
            return False
        finally:
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()
            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

    # ------------------------------------------------------------------
    # 12. The first second after a commit is exactly one divider period
    # ------------------------------------------------------------------

    async def test_gh56_first_second_after_commit_is_exact(self) -> bool:
        """
        Decided contract: the first second after a commit is EXACTLY one
        divider period - 32768 counter clocks in production mode, 100 in
        clock_select=1 test mode (DIV_TARGET_SYS=99, so target+1=100 edges
        per rtc_core.sv's own comment). Test mode is used here so the
        measurement (white-box, counting selected_clk=pclk edges from the
        load to the first tick) is fast and exact - both clocks are pclk,
        so there is no ratio/synchronizer jitter to account for.

        Today the divider hold condition includes w_commit_active
        (`!w_ctr_enable || w_ctr_time_set || w_commit_active`), and
        w_commit_active (`dst_valid || r_commit_valid_d`) stays asserted
        for ONE extra selected_clk cycle past the load edge itself
        (r_commit_valid_d is a one-cycle-delayed copy of dst_valid, so it
        is still 1 the cycle after dst_valid - and w_commit_load - already
        dropped). That extra held cycle delays the first tick to 101
        instead of 100.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-12 First second after a commit is exact")
        self.log.info("=" * 80)

        try:
            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await self.tb.wait_clocks('pclk', 5)

            # Test mode: clock_select=1, selected_clk=pclk, divider target=99.
            await self.tb.enable_rtc(enable=True, use_sys_clock=True)

            committed = {'seconds': 37, 'minutes': 14, 'hours': 6, 'day': 12, 'month': 4, 'year': 27}

            core = self.tb.dut.u_rtc_core
            samples = []

            async def _sampler():
                for _ in range(400):
                    await RisingEdge(self.tb.pclk)
                    samples.append((int(core.r_seconds.value), int(core.r_second_tick.value)))

            sampler_task = cocotb.start_soon(_sampler())

            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_CLOCK_SELECT | \
                RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, committed['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, committed['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, committed['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, committed['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, committed['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, committed['year'])
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(
                RTCRegisterMap.RTC_CONFIG,
                RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_CLOCK_SELECT
            )

            await sampler_task

            load_idx = next((i for i, s in enumerate(samples) if s[0] == committed['seconds']), None)
            assert load_idx is not None, (
                "setup sanity check failed: r_seconds never showed the committed value "
                "within the sample window (not this contract's own finding)"
            )
            tick_idx = next((i for i, s in enumerate(samples[load_idx:], start=load_idx) if s[1] == 1),
                             None)
            assert tick_idx is not None, (
                "setup sanity check failed: no second_tick observed after the load within "
                "the sample window"
            )
            edges = tick_idx - load_idx
            self.log.info(f"  load at sample {load_idx}, first tick at sample {tick_idx} "
                           f"({edges} selected_clk edges apart, expected 100)")

            # Steady-state period: distance from this tick to the next one.
            tick2_idx = next(
                (i for i, s in enumerate(samples[tick_idx + 1:], start=tick_idx + 1) if s[1] == 1),
                None
            )
            steady_edges = (tick2_idx - tick_idx) if tick2_idx is not None else None
            self.log.info(f"  steady-state period: {steady_edges} edges (expected 100)")

            assert edges == 100, (
                f"the first second after a commit took {edges} selected_clk edges, expected "
                f"exactly 100 - the divider's w_commit_active hold term stays asserted one "
                f"cycle past the load edge (r_commit_valid_d is a one-cycle-delayed copy of "
                f"dst_valid), adding a spurious extra hold cycle"
            )

            self.log.info("GH#56-12 First second after commit is exact test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-12 First second after commit is exact test FAILED: {e}")
            return False

    # ========================================================================
    # Coordinator direction, 2026-09-09 (fourth review round): four more RED
    # tests against a fourth review of the uncommitted GH#56 RTL follow-up.
    # Production mode unless stated. A further RTL follow-up (not authored
    # here - no rtl/** edits) lands after this run.
    # ========================================================================

    # ------------------------------------------------------------------
    # 13. A commit staged entirely under an rtc_resetn stall is dropped,
    #     not stuck and not delivered on release
    # ------------------------------------------------------------------

    async def test_gh56_commit_during_rtc_reset_is_dropped(self) -> bool:
        """
        Decided contract: the pclk-side commit bookkeeping (pending, busy,
        the timeout edge detector) is reset by EITHER presetn or the
        synchronized rtc_resetn, matching the handshake's source side - so
        a commit staged while rtc_resetn is low is DROPPED: busy does not
        hang, no timeout is reported for it, and after rtc_resetn releases
        the counters read the reset default, not the staged time. Software
        re-issues the commit and it works normally.

        Holds rtc_resetn low (presetn stays high) for the whole staging
        sequence and the commit trigger. Today the pclk-side bookkeeping
        (r_commit_pend/r_commit_busy in rtc_core.sv) is reset ONLY by
        rst_n (presetn) - rtc_resetn does not touch it - so time_commit_busy
        latches high on the commit pulse and never has any way to clear
        (the handshake's source side keeps re-trying into a destination
        that is held in reset the whole time), and when rtc_resetn finally
        releases, the STILL-PENDING request is exactly what a freshly
        reset destination sees first - delivering the staged (not reset
        default) time.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-13 Commit during rtc_resetn stall is dropped")
        self.log.info("=" * 80)

        try:
            failures = []

            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

            await self._enable_production_mode(bcd=False, hour_12=False)

            staged = {'seconds': 19, 'minutes': 5, 'hours': 15, 'day': 3, 'month': 11, 'year': 29}

            await self.tb.assert_rtc_resetn()
            self.log.info("  rtc_resetn held low - staging and committing a time under it")

            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, staged['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, staged['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, staged['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, staged['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, staged['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, staged['year'])
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)

            await ClockCycles(self.tb.pclk, 100)

            busy = int(self.tb.dut.u_rtc_core.r_commit_busy.value)
            _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
            self.log.info(f"  ~100 pclk into the rtc_resetn stall: busy={busy} "
                           f"commit_timeout={timeout_bit}")

            if busy:
                failures.append(
                    "time_commit_busy is still set ~100 pclk after a commit staged entirely "
                    "under an rtc_resetn stall - the pclk-side commit bookkeeping is reset "
                    "only by presetn, not by rtc_resetn, so it has no way to clear while the "
                    "destination stays in reset"
                )
            if timeout_bit:
                failures.append("commit_timeout set for a commit staged under an rtc_resetn stall")

            await self.tb.deassert_rtc_resetn()
            await ClockCycles(self.tb.dut.rtc_clk, 10)
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

            reset_default = {'seconds': 0, 'minutes': 0, 'hours': 0, 'day': 1, 'month': 1, 'year': 0}
            after_release = await self.tb.read_time()
            status_after = await self.tb.read_status()
            self.log.info(f"  after rtc_resetn release + settle: {after_release} "
                           f"time_valid={status_after['time_valid']}")

            if after_release != reset_default:
                failures.append(
                    f"expected the reset default {reset_default} after rtc_resetn release, "
                    f"got {after_release} - the staged time {staged} was delivered instead of "
                    f"being dropped, because the commit request was still pending when the "
                    f"destination came out of reset"
                )
            if status_after['time_valid']:
                failures.append("status_time_valid is set after rtc_resetn release with no commit delivered")

            # A fresh commit, now that both domains are out of reset, must work.
            retry_time = {'seconds': 33, 'minutes': 21, 'hours': 9, 'day': 14, 'month': 6, 'year': 30}
            await self.tb.set_time(**retry_time)
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
            landed = await self.tb.read_time()
            self.log.info(f"  time after the fresh retry commit: {landed}")
            if landed != retry_time:
                failures.append(f"a fresh commit after the drop did not land: expected {retry_time}, got {landed}")

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-13 Commit during rtc_resetn stall test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-13 Commit during rtc_resetn stall test FAILED: {e}")
            return False
        finally:
            self.tb.dut.rtc_resetn.value = 1

    # ------------------------------------------------------------------
    # 14. A presetn pulse during a stall must not manufacture a timeout
    # ------------------------------------------------------------------

    async def test_gh56_no_spurious_timeout_after_presetn(self) -> bool:
        """
        Decided contract: commit_timeout can never set itself - a presetn
        pulse during a stall (or at any time) must not produce a
        commit_timeout event after release unless a NEW commit times out.

        Stops rtc_clk, commits, waits past COMMIT_TIMEOUT (commit_timeout
        sets, as expected - W1C it), pulses ONLY presetn, releases, and
        polls RTC_STATUS for ~200 pclk with no new commit issued.

        Today the timeout edge detector (r_commit_timeout_d, edge-detecting
        the CDC's raw watchdog LEVEL w_commit_timeout) is reset by rst_n
        (presetn) to 0, but w_commit_timeout itself is a level driven by
        the handshake's OWN source-side timeout counter, whose reset is
        ALSO rst_n now - so both reset together... but the level can still
        read 1 again very quickly after release if the still-pending
        transfer has not yet reached S_IDLE (the counter's own "cycles ==
        TIMEOUT" comparison can re-trip before the transfer clears), and
        r_commit_timeout_d (having just been reset to 0) sees that as a
        fresh 0->1 edge - manufacturing a commit_timeout event nobody's
        commit actually caused.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-14 No spurious commit_timeout after presetn")
        self.log.info("=" * 80)

        try:
            failures = []

            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

            await self._enable_production_mode(bcd=False, hour_12=False)

            self.tb.stop_rtc_clk()
            await self.tb.set_time(seconds=17, minutes=9, hours=13, day=8, month=5, year=24)

            await ClockCycles(self.tb.pclk, 65535 + 200)

            _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
            self.log.info(f"  commit_timeout after the wait (expected True): {timeout_bit}")
            if not timeout_bit:
                failures.append(
                    "setup sanity check failed: commit_timeout never set with rtc_clk stopped "
                    "(not this contract's own finding)"
                )
            await self.tb.write_register(RTCRegisterMap.RTC_STATUS, RTCRegisterMap.STATUS_COMMIT_TIMEOUT)

            await self.tb.assert_presetn()
            await ClockCycles(self.tb.pclk, 20)
            await self.tb.deassert_presetn()
            await self._enable_production_mode(bcd=False, hour_12=False)

            spurious_at = None
            for i in range(20):
                _, status_raw_i = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                if bool(status_raw_i & RTCRegisterMap.STATUS_COMMIT_TIMEOUT):
                    spurious_at = i
                    break
                await ClockCycles(self.tb.pclk, 10)

            self.log.info(f"  spurious commit_timeout observed at poll index: {spurious_at}")
            if spurious_at is not None:
                failures.append(
                    f"commit_timeout set again (poll #{spurious_at}) after a presetn-only "
                    f"reset with NO new commit issued - the timeout edge detector "
                    f"manufactured an event from the still-pending transfer's watchdog level "
                    f"re-tripping after reset"
                )

            # The originally-pending transfer must still be able to land,
            # and a fresh commit must still work.
            await self.tb.start_rtc_clk()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES * 2)

            fresh_time = {'seconds': 44, 'minutes': 2, 'hours': 18, 'day': 25, 'month': 12, 'year': 36}
            await self.tb.set_time(**fresh_time)
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
            landed = await self.tb.read_time()
            self.log.info(f"  time after a fresh commit post-recovery: {landed}")
            if landed != fresh_time:
                failures.append(f"a fresh commit after recovery did not land: expected {fresh_time}, got {landed}")

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-14 No spurious commit_timeout after presetn test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-14 No spurious commit_timeout after presetn test FAILED: {e}")
            return False
        finally:
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()

    # ------------------------------------------------------------------
    # 15. The counters never take two updates on consecutive cycles - a
    #     natural tick cannot land on the cycle right before the load
    # ------------------------------------------------------------------

    async def test_gh56_no_back_to_back_update_at_commit(self) -> bool:
        """
        White-box: force rtc_core's divider (r_clk_div_counter) to
        TARGET-1 exactly once, K selected_clk edges after the commit
        trigger, then let it run free. A forced TARGET-1 needs exactly two
        MORE free selected_clk edges to roll over (one to reach TARGET,
        one to detect TARGET>=TARGET and tick) - rtc_core.sv's own
        priority chain checks `w_commit_active` (which holds the divider
        at zero) BEFORE the rollover condition, so a continuously-forced
        TARGET-1 can never actually reach TARGET while commit_active is
        already asserted; only a single, well-timed deposit followed by
        free-running gives the divider room to reach the rollover
        naturally at a chosen instant. The commit's own load lands a
        roughly fixed handful of selected_clk edges after the trigger, so
        sweeping K finds the alignment where the natural rollover lands on
        the edge immediately before the load - the tightest
        natural-tick-vs-load race reachable without editing the RTL.

        Contract, for every swept K: the readable time after the commit
        equals the committed time exactly - not +1 s, not torn - and
        r_seconds (sampled every selected_clk edge) takes at most one
        update in any two consecutive edges (rtc_core.sv's own
        a_updates_are_spaced assertion states this as a formal property;
        Verilator does not evaluate `assert property`, so this test checks
        the same thing behaviorally).
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-15 No back-to-back counter update at a commit")
        self.log.info("=" * 80)

        committed = {'seconds': 58, 'minutes': 47, 'hours': 22, 'day': 30, 'month': 7, 'year': 39}
        target = 32767  # DIV_TARGET_RTC, production mode

        try:
            coincident_failures = []

            for k in range(0, 8):
                await self.tb.assert_reset()
                await self.tb.wait_clocks('pclk', 10)
                await self.tb.deassert_reset()
                await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

                await self._enable_production_mode(bcd=False, hour_12=False)

                core = self.tb.dut.u_rtc_core
                samples = []

                async def _sampler():
                    while True:
                        await RisingEdge(self.tb.dut.rtc_clk)
                        samples.append(int(core.r_seconds.value))

                sampler_task = cocotb.start_soon(_sampler())

                config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
                await ClockCycles(self.tb.pclk, 5)
                await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, committed['seconds'])
                await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, committed['minutes'])
                await self.tb.write_register(RTCRegisterMap.RTC_HOURS, committed['hours'])
                await self.tb.write_register(RTCRegisterMap.RTC_DAY, committed['day'])
                await self.tb.write_register(RTCRegisterMap.RTC_MONTH, committed['month'])
                await self.tb.write_register(RTCRegisterMap.RTC_YEAR, committed['year'])
                await ClockCycles(self.tb.pclk, 5)
                # The commit trigger.
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)

                # K selected_clk edges after the trigger, force the divider
                # to TARGET-1 exactly once, then let it run free.
                await ClockCycles(self.tb.dut.rtc_clk, k)
                core.r_clk_div_counter.value = target - 1

                await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
                sampler_task.kill()

                self.log.info(f"  k={k}: r_seconds per selected_clk edge: {samples}")

                back_to_back = []
                for i in range(2, len(samples)):
                    if samples[i] != samples[i - 1] and samples[i - 1] != samples[i - 2]:
                        back_to_back.append((i, samples[i - 2:i + 1]))

                landed = await self.tb.read_time()

                point_failures = []
                if back_to_back:
                    point_failures.append(
                        f"r_seconds updated on two consecutive selected_clk edges "
                        f"{[b[0] for b in back_to_back]} (trace around first: "
                        f"{back_to_back[0][1]}) - a natural tick landed on the cycle right "
                        f"before the commit load"
                    )
                # A forced rollover that lands AFTER the load has already
                # restarted the divider is a state the design cannot reach on
                # its own (the load zeroes the divider); the only legal
                # outcome there is exactly one extra second, never a tear.
                committed_plus_1 = dict(committed); committed_plus_1['seconds'] += 1
                if landed != committed and landed != committed_plus_1:
                    point_failures.append(
                        f"the committed time {committed} did not land exactly - got {landed}"
                    )

                if point_failures:
                    coincident_failures.append((k, point_failures))

            if coincident_failures:
                summary = "; ".join(f"k={k}: {'; '.join(p)}" for k, p in coincident_failures)
                raise AssertionError(
                    f"failed at {len(coincident_failures)}/8 sweep point(s): {summary}"
                )

            self.log.info("GH#56-15 No back-to-back counter update test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-15 No back-to-back counter update test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # 16. busy must hold when a queued commit's completion coincides with
    #     the PREVIOUS (timed-out) transfer's watchdog edge. Runs under a
    #     SEPARATE build with a small COMMIT_TIMEOUT_CYCLES (see
    #     test_apb4_rtc.py's test_rtc_gh56_timeout_sweep pytest wrapper) -
    #     65535 cycles is impractical to sweep, and other tests in this
    #     suite depend on that being the DEFAULT build's value, so this
    #     needs its own elaboration rather than reusing the main one.
    # ------------------------------------------------------------------

    async def test_gh56_busy_holds_when_timeout_meets_idle(self) -> bool:
        """
        Decided contract (coordinator correction 2026-09-09, round-8
        follow-up landed): the queued-commit watchdog now arms at EVERY
        commit pulse - a queued commit (B) has its OWN COMMIT_TIMEOUT_CYCLES
        window counted from ITS OWN commit pulse. Two sub-contracts:
          1. A's own timeout event must not release B: right when A's
             timeout is reported, busy must still read 1 (B is queued
             behind it) - this is the ORIGINAL point of this test and is
             asserted explicitly, independent of the sweep below.
          2. If the counter clock returns BEFORE B's own window (W =
             COMMIT_TIMEOUT_CYCLES pclk measured from B's commit-trigger
             write) elapses, busy holds the whole time and B lands with no
             second commit_timeout report. If the clock is still dead
             AT/AFTER W, B gets its OWN report: commit_timeout sets AGAIN
             and busy drops to 0, with the register mirror resumed -
             measured at COMMIT_TIMEOUT_CYCLES + 1 pclk edges after B's
             commit pulse. When the clock eventually returns, B lands
             (never A) and the flag retires on its own.

        Time is measured in REAL pclk via sim time / the clock period
        (cocotb.utils.get_sim_time), never via an accumulator that ignores
        the cost of the APB reads used to observe it - a step-per-poll
        accumulator silently under-counts real elapsed pclk once the polls
        themselves take multiple cycles each (measured: busy actually
        clears at COMMIT_TIMEOUT_CYCLES + 1 pclk after B's own commit
        pulse, but a naive step=10-per-poll accumulator whose polls cost
        ~70-100 pclk each crosses that window on its FOURTH iteration
        regardless of the swept target, well before the accumulator's own
        count says so). Polls inside the timing-sensitive loops read
        RTC_STATUS only; the six time registers are read once at the end
        of each sweep point.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-16 busy holds when a timeout meets link-idle")
        self.log.info("=" * 80)

        timeout_cycles = int(os.environ.get('TEST_COMMIT_TIMEOUT_CYCLES', '200'))
        pclk_period_ns = int(os.environ.get('TEST_APB_CLOCK_PERIOD', '10'))
        self.log.info(f"  COMMIT_TIMEOUT_CYCLES for this build: {timeout_cycles}")

        def pclk_since(t0_ns: float) -> float:
            return (get_sim_time('ns') - t0_ns) / pclk_period_ns

        try:
            failures = []
            core = self.tb.dut.u_rtc_core
            time_a = {'seconds': 6, 'minutes': 13, 'hours': 5, 'day': 9, 'month': 2, 'year': 18}
            time_b = {'seconds': 51, 'minutes': 29, 'hours': 17, 'day': 22, 'month': 8, 'year': 43}
            w = timeout_cycles  # B's own window, measured from its commit pulse

            # Sweep how long the clock stays stopped, counted from B's
            # commit pulse - straddling W so some points return before it
            # and some at/after it.
            sweep = [timeout_cycles + d for d in (-150, -100, -60, -30, -10, 0, 10, 30, 60, 100)]
            sweep = [s for s in sweep if s > 0]

            point_failures_all = []
            a_wait_iterations = 3 * timeout_cycles // 5 + 40
            b_wait_iterations = 3 * timeout_cycles // 5 + 80

            for stall_cycles in sweep:
                point_failures = []

                await self.tb.assert_reset()
                await self.tb.wait_clocks('pclk', 10)
                await self.tb.deassert_reset()
                await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

                await self._enable_production_mode(bcd=False, hour_12=False)

                self.tb.stop_rtc_clk()
                await self.tb.set_time(**time_a)  # A's commit pulse

                # Queue B behind A while the link is still frozen (so A is
                # definitely still pending).
                config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
                await ClockCycles(self.tb.pclk, 5)
                await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_b['seconds'])
                await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_b['minutes'])
                await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_b['hours'])
                await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_b['day'])
                await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_b['month'])
                await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_b['year'])
                await ClockCycles(self.tb.pclk, 5)
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)
                b_commit_ns = get_sim_time('ns')  # B's own commit pulse

                # Sub-contract 1: A's own timeout must not release B - busy
                # must still read 1 right when A's timeout is reported.
                a_reported = False
                for _ in range(a_wait_iterations):
                    _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                    if status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT:
                        a_reported = True
                        busy_now = int(core.r_commit_busy.value)
                        if not busy_now:
                            point_failures.append(
                                "busy dropped when A's OWN timeout was reported, even "
                                "though B is queued behind it"
                            )
                        break
                    await ClockCycles(self.tb.pclk, 5)

                if not a_reported:
                    point_failures.append(
                        "A's commit_timeout was never reported within the bounded wait"
                    )

                # W1C so any later commit_timeout observation unambiguously
                # belongs to B, not to A's still-latched report.
                await self.tb.write_register(RTCRegisterMap.RTC_STATUS, RTCRegisterMap.STATUS_COMMIT_TIMEOUT)

                if stall_cycles < w:
                    # Clock returns BEFORE B's own window: busy must hold
                    # the whole time (measured in real pclk from B's
                    # commit pulse), then B lands with no second report.
                    busy_dropped_early_at = None
                    while pclk_since(b_commit_ns) < stall_cycles:
                        busy = int(core.r_commit_busy.value)
                        if not busy:
                            busy_dropped_early_at = pclk_since(b_commit_ns)
                            break
                        await ClockCycles(self.tb.pclk, 5)

                    if busy_dropped_early_at is not None:
                        point_failures.append(
                            f"busy dropped at ~{busy_dropped_early_at:.0f} pclk after "
                            f"B's commit pulse, before B's own window (W={w}) even "
                            f"elapsed (stall={stall_cycles})"
                        )

                    await self.tb.start_rtc_clk()
                    await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES * 2)

                    final_time = await self.tb.read_time()
                    _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                    timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)

                    if final_time != time_b:
                        point_failures.append(
                            f"B did not land after the clock returned inside its own "
                            f"window - final={final_time}, expected {time_b}"
                        )
                    if timeout_bit:
                        point_failures.append(
                            "commit_timeout is set even though B landed inside its own "
                            "window - a timeout was reported for a transfer that completed"
                        )

                    self.log.info(
                        f"  stall={stall_cycles} (< W={w}): final={final_time} "
                        f"commit_timeout={timeout_bit}"
                    )

                else:
                    # Clock stays stopped AT/AFTER B's own window: B must
                    # report ITS OWN timeout (measured ~W+1 pclk after its
                    # commit pulse) and release busy, mirror resumed -
                    # while the clock is STILL stopped.
                    b_ok = False
                    busy = None
                    timeout_bit = None
                    for _ in range(b_wait_iterations):
                        _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                        timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
                        busy = int(core.r_commit_busy.value)
                        if timeout_bit and not busy:
                            b_ok = True
                            break
                        await ClockCycles(self.tb.pclk, 5)

                    measured_pclk = pclk_since(b_commit_ns)

                    if not b_ok:
                        _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                        time_valid_now = bool(status_raw & RTCRegisterMap.STATUS_TIME_VALID)
                        staged = await self.tb.read_time()
                        point_failures.append(
                            f"B never reported its OWN commit_timeout=1/busy=0 by "
                            f"~{measured_pclk:.0f} pclk after its commit pulse "
                            f"(window W={w}, stall={stall_cycles}) - stuck at "
                            f"commit_timeout={timeout_bit} busy={busy}; "
                            f"time_valid={time_valid_now}, staged registers read {staged} "
                            f"(still B's staged bytes, not the counter)"
                        )
                    else:
                        self.log.info(
                            f"  stall={stall_cycles} (>= W={w}): B's own report landed "
                            f"at ~{measured_pclk:.0f} pclk after its commit pulse"
                        )

                    await self.tb.start_rtc_clk()
                    await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES * 2)

                    final_time = await self.tb.read_time()
                    _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                    timeout_after_restart = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
                    busy_after_restart = int(core.r_commit_busy.value)

                    if b_ok:
                        if final_time != time_b:
                            point_failures.append(
                                f"after the clock returned, B did not land - "
                                f"final={final_time}, expected {time_b} (A must never land)"
                            )
                        if timeout_after_restart:
                            point_failures.append(
                                "commit_timeout is still set after B landed and the link "
                                "settled - it should have retired on its own"
                            )
                        if busy_after_restart:
                            point_failures.append(
                                "time_commit_busy is still set after B landed and the "
                                "link settled"
                            )

                if point_failures:
                    point_failures_all.append((stall_cycles, point_failures))

            if point_failures_all:
                summary = "; ".join(
                    f"stall={s}: {'; '.join(p)}" for s, p in point_failures_all
                )
                failures.append(
                    f"failed at {len(point_failures_all)}/{len(sweep)} sweep point(s): {summary}"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-16 busy holds when timeout meets idle test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-16 busy holds when timeout meets idle test FAILED: {e}")
            return False
        finally:
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()

    # ------------------------------------------------------------------
    # GH#56 coordinator direction 2026-09-09 (fifth review round): five
    # more RED tests. Checked against the CURRENT rtc_core.sv /
    # rtc_config_regs.sv, re-read in full this round.
    #
    # GH56-17/21 share one root cause: u_snap_pulse_sync and u_event_sync
    # (rtc_core.sv) are both pclk-domain synchronizers whose DESTINATION
    # side is reset by `rst_n` (presetn) - the LOCAL domain's own reset,
    # which is the usual CDC convention but is wrong for THESE two,
    # because their SOURCE-side state (the toggle bit inside sync_pulse,
    # and the counter-domain levels r_second_tick/r_alarm_match) lives in
    # the counter domain and is reset only by rtc_resetn. A presetn pulse
    # therefore resets only one side of what is, in effect, a toggle/level
    # comparison - exactly the asymmetric-reset problem rtc_core.sv's own
    # header already documents at length for the time-set commit link
    # (which is why that one is four-phase and reset with the far domain,
    # not presetn). The fix the decided contracts describe is the same
    # move applied to these two synchronizers: reset their destination
    # side with the far reset (w_rtc_rst_n_pclk), not with presetn.
    #
    # GH56-19/20 share a different root cause: RTC_CONFIG is a plain
    # peakrdl register with hw=r, reset by presetn like every other
    # register in the file, and cfg_rtc_enable/cfg_clock_select cross to
    # the counter domain unconditionally (u_cfg_sync has no qualifying
    # "this value is valid" input). There is no config-valid flag as the
    # decided contract describes, so a presetn pulse's reset-default
    # RTC_CONFIG (0x0) crosses within a few selected_clk cycles and is
    # indistinguishable from a real software write of 0x0 - it stops the
    # counter (GH56-19) and, in test mode, flips selected_clk back to
    # rtc_clk out from under a running test-mode configuration (GH56-20).
    #
    # GH56-18 is a direct read of rtc_core.sv's own watchdog-event gate:
    #   assign w_commit_timeout_evt = w_commit_timeout && !r_commit_timeout_d &&
    #                                 r_commit_inflight && !w_commit_src_ready &&
    #                                 !r_commit_pend;
    # The trailing `!r_commit_pend` unconditionally suppresses the timeout
    # EVENT (not just re-attributing it) whenever a retry is queued behind
    # the stalled transfer - the opposite of "a stall is always reported".
    # ------------------------------------------------------------------

    async def test_gh56_presetn_over_load_parity(self) -> bool:
        """
        Decided contract: completion evidence (the snapshot pulse that
        tells pclk a commit landed) and the commit bookkeeping share the
        FAR reset, so a presetn pulse can neither destroy nor fabricate a
        snapshot pulse. Commits twice back to back in production mode so
        the second commit's snapshot pulse has the OPPOSITE sync_pulse
        toggle parity from the first, and for each one asserts presetn for
        a window covering the counter-domain load edge (~20 pclk starting
        ~2 rtc_clk (=20 pclk at the 10:1 ratio) after the commit trigger).

        Contract for BOTH parities: time_commit_busy clears within ~50
        pclk after the load, and the readable time is exactly the
        committed time - never a stuck busy (the pulse got reset away
        under one parity) and never the pre-commit time published as the
        commit's answer (the pulse got fabricated under the other parity,
        because u_snap_pulse_sync's destination-side reset (presetn) and
        source-side toggle state (counter domain, reset only by
        rtc_resetn) briefly disagree about whether a toggle already
        happened).
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-17 presetn over the commit-load edge, both toggle parities")
        self.log.info("=" * 80)

        try:
            failures = []
            await self._enable_production_mode(bcd=False, hour_12=False)

            commits = [
                {'seconds': 11, 'minutes': 22, 'hours': 9, 'day': 5, 'month': 6, 'year': 24},
                {'seconds': 42, 'minutes': 17, 'hours': 20, 'day': 19, 'month': 11, 'year': 30},
            ]

            core = self.tb.dut.u_rtc_core

            for idx, t in enumerate(commits):
                config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
                await ClockCycles(self.tb.pclk, 5)
                await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, t['seconds'])
                await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, t['minutes'])
                await self.tb.write_register(RTCRegisterMap.RTC_HOURS, t['hours'])
                await self.tb.write_register(RTCRegisterMap.RTC_DAY, t['day'])
                await self.tb.write_register(RTCRegisterMap.RTC_MONTH, t['month'])
                await self.tb.write_register(RTCRegisterMap.RTC_YEAR, t['year'])
                await ClockCycles(self.tb.pclk, 5)
                # Trigger: time_set_mode's falling edge.
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)

                # The load lands ~4-5 selected_clk cycles after the commit
                # (rtc_core.sv header) - ~40-50 pclk at the 10:1 ratio.
                # Land presetn starting ~2 rtc_clk (20 pclk) after the
                # trigger, held ~20 pclk, bracketing that edge.
                await ClockCycles(self.tb.pclk, 20)
                await self.tb.assert_presetn()
                await ClockCycles(self.tb.pclk, 20)
                await self.tb.deassert_presetn()
                await ClockCycles(self.tb.pclk, 5)

                busy_cleared = False
                for _ in range(10):
                    busy = int(core.r_commit_busy.value)
                    if not busy:
                        busy_cleared = True
                        break
                    await ClockCycles(self.tb.pclk, 5)

                if not busy_cleared:
                    failures.append(
                        f"commit {idx} (time={t}): time_commit_busy is still set ~50 pclk "
                        f"after a presetn pulse over the load edge - the snapshot pulse "
                        f"appears to have been reset away"
                    )
                    # Force it settled before the next iteration so a stuck
                    # busy from this parity does not also corrupt the other.
                    await self.tb.assert_reset()
                    await self.tb.wait_clocks('pclk', 10)
                    await self.tb.deassert_reset()
                    await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
                    await self._enable_production_mode(bcd=False, hour_12=False)
                    continue

                final = await self.tb.read_time()
                if final != t:
                    failures.append(
                        f"commit {idx} (time={t}): readable time after presetn-over-load "
                        f"is {final}, expected exactly the committed time {t} (a fabricated "
                        f"pulse would publish stale/pre-commit data instead)"
                    )

                await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-17 presetn over commit-load edge (both parities) test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-17 presetn over commit-load edge (both parities) test FAILED: {e}")
            return False
        finally:
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()

    async def test_gh56_stall_with_retry_still_reports_timeout(self) -> bool:
        """
        Decided contract: a stall is always reported - commit_timeout SETS
        when the in-flight transfer exceeds the watchdog window even if a
        retry is queued behind it; the queued commit keeps busy and its
        staged values, and lands after the stalled one.

        Today rtc_core.sv's w_commit_timeout_evt ANDs in `!r_commit_pend`,
        which unconditionally suppresses the timeout EVENT whenever a
        retry (B) is queued behind the stalled transfer (A) - the opposite
        of "always reported".

        Stops rtc_clk, commits A (which stalls), then at half the
        COMMIT_TIMEOUT_CYCLES window stages and commits B (queuing it
        behind A while A is provably still un-acknowledged), keeps rtc_clk
        stopped past the full window, and checks commit_timeout / busy /
        the staged registers - then restarts the clock and confirms A
        lands, then B lands last.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-18 Stall with a queued retry still reports commit_timeout")
        self.log.info("=" * 80)

        # rtc_core.sv's COMMIT_TIMEOUT_CYCLES default (this build uses no
        # RTL parameter override).
        timeout_cycles = 65535

        try:
            failures = []
            await self._enable_production_mode(bcd=False, hour_12=False)

            time_a = {'seconds': 3, 'minutes': 14, 'hours': 6, 'day': 8, 'month': 2, 'year': 21}
            time_b = {'seconds': 45, 'minutes': 50, 'hours': 18, 'day': 27, 'month': 9, 'year': 35}

            self.tb.stop_rtc_clk()
            await self.tb.set_time(**time_a)  # stalls: rtc_clk is stopped

            half = timeout_cycles // 2
            await ClockCycles(self.tb.pclk, half)

            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_b['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_b['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_b['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_b['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_b['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_b['year'])
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)  # B queued

            # Continue past the FULL window (measured from A's own trigger),
            # clock still stopped, plus margin.
            remaining = (timeout_cycles - half) + 200
            await ClockCycles(self.tb.pclk, remaining)

            core = self.tb.dut.u_rtc_core
            busy = int(core.r_commit_busy.value)
            _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
            staged = await self.tb.read_time()

            if not timeout_bit:
                failures.append(
                    "commit_timeout did NOT set after A's watchdog window expired, even "
                    "though B is queued behind it and A never acknowledged - a stall must "
                    "always be reported regardless of a queued retry"
                )
            if not busy:
                failures.append("time_commit_busy dropped while B was still queued/pending")
            if staged != time_b:
                failures.append(
                    f"staged registers read {staged} instead of B's staged values {time_b} "
                    f"while B is pending"
                )

            # W1C the (expected) timeout bit before restarting so a later
            # read is unambiguous.
            await self.tb.write_register(RTCRegisterMap.RTC_STATUS, RTCRegisterMap.STATUS_COMMIT_TIMEOUT)

            await self.tb.start_rtc_clk()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES * 2)

            final_time = await self.tb.read_time()
            if final_time != time_b:
                failures.append(
                    f"final landed time is {final_time}, expected B's time {time_b} "
                    f"(A should land first, then B, with B the final answer)"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-18 stall-with-queued-retry commit_timeout test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-18 stall-with-queued-retry commit_timeout test FAILED: {e}")
            return False
        finally:
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()

    async def test_gh56_presetn_does_not_stop_the_clock(self) -> bool:
        """
        Decided contract: a bus reset does not stop or re-clock the RTC -
        the counter domain keeps its last run/enable state and clock
        source across presetn, applying a new RTC_CONFIG only after
        software writes it (a config-valid flag, set by any RTC_CONFIG
        write and cleared by presetn, should gate the crossed
        enable/clock_select). After presetn, timekeeping continues from
        where it was, and RTC_CONFIG itself reads its reset value until
        software writes it.

        Today there is no such gating flag: RTC_CONFIG.rtc_enable is a
        plain peakrdl field, reset to 0 by presetn like every other
        register, and crosses via u_cfg_sync unconditionally - so a
        presetn pulse's reset-default (enable=0) crosses within a few
        selected_clk cycles and stops the counter exactly as if software
        had written enable=0, even with rtc_resetn untouched.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-19 presetn does not stop the running clock")
        self.log.info("=" * 80)

        try:
            failures = []
            await self._enable_production_mode(bcd=False, hour_12=False)

            start_time = {'seconds': 10, 'minutes': 20, 'hours': 8, 'day': 4, 'month': 6, 'year': 25}
            await self.tb.force_time_registers(**start_time, time_valid=True)
            await ClockCycles(self.tb.pclk, 5)

            # Bus-only reset: rtc_resetn untouched, RTC_CONFIG never
            # rewritten afterwards.
            await self.tb.assert_presetn()
            await ClockCycles(self.tb.pclk, 10)
            await self.tb.deassert_presetn()
            await ClockCycles(self.tb.pclk, 10)

            _, config_after = await self.tb.read_register(RTCRegisterMap.RTC_CONFIG)
            if config_after != 0:
                failures.append(
                    f"RTC_CONFIG reads 0x{config_after:x} after presetn, expected the "
                    f"reset value 0x0 (all fields reset to 0 in rtc_regs.rdl)"
                )

            # Whitebox-advance 3 "seconds" of counter time via forced
            # rollovers. The counter domain must still be running/enabled
            # internally REGARDLESS of what the now-reset RTC_CONFIG reads,
            # per the decided config-valid-gating contract.
            for _ in range(3):
                await self.tb.force_divider_near_target(clock_select=0, remaining_cycles=2)
                await ClockCycles(self.tb.dut.rtc_clk, 3)

            final = await self.tb.read_time()
            expected_seconds = (start_time['seconds'] + 3) % 60
            if int(final['seconds']) != expected_seconds:
                failures.append(
                    f"readable seconds after presetn + 3 forced ticks is "
                    f"{final['seconds']}, expected {expected_seconds} - the counter "
                    f"did not keep running through the presetn pulse"
                )

            # Writing RTC_CONFIG enable=0 afterwards must stop the clock as
            # usual - the gating flag being cleared by presetn must not
            # ALSO block a genuine software write from taking effect.
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, 0)
            await ClockCycles(self.tb.pclk, 10)
            before_disable_check = self.tb.read_time_registers_whitebox()['seconds']
            await self.tb.force_divider_near_target(clock_select=0, remaining_cycles=2)
            await ClockCycles(self.tb.dut.rtc_clk, 3)
            after_disable_check = self.tb.read_time_registers_whitebox()['seconds']
            if after_disable_check != before_disable_check:
                failures.append(
                    f"writing RTC_CONFIG enable=0 after the presetn pulse did not stop "
                    f"the counter (seconds advanced from {before_disable_check} to "
                    f"{after_disable_check})"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-19 presetn does not stop the clock test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-19 presetn does not stop the clock test FAILED: {e}")
            return False

    async def test_gh56_presetn_does_not_switch_clock(self) -> bool:
        """
        Decided contract (same config-valid-flag mechanism as GH56-19, this
        time exercised against clock_select): running in TEST mode
        (clock_select=1, selected_clk=pclk) with a commit in flight, a
        presetn pulse must not switch selected_clk away from the clock
        that was actually programmed until software writes RTC_CONFIG
        again - the commit lands intact and the counter domain keeps
        running on the test clock (divider period stays 100 selected_clk
        edges, white-box).

        Today RTC_CONFIG.clock_select resets to 0 (=rtc_clk) on presetn
        exactly like every other field and crosses unconditionally, so the
        combinational mux (`selected_clk = cfg_clock_select ? clk :
        rtc_clk`) flips away from pclk the moment the reset-default
        crosses, even though software never rewrote RTC_CONFIG.

        The exact pclk-cycle offset between the commit trigger and the
        in-flight window is not hand-derived; sweeps a small range so at
        least one point catches presetn while the commit is genuinely
        still crossing.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-20 presetn does not switch the test-mode clock")
        self.log.info("=" * 80)

        try:
            failures = []
            committed = {'seconds': 33, 'minutes': 12, 'hours': 7, 'day': 14, 'month': 3, 'year': 27}
            core = self.tb.dut.u_rtc_core

            for k in range(0, 10):
                await self.tb.assert_reset()
                await self.tb.wait_clocks('pclk', 10)
                await self.tb.deassert_reset()
                await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)

                base_config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_CLOCK_SELECT
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, base_config)
                await ClockCycles(self.tb.pclk, 5)

                stage_cfg = base_config | RTCRegisterMap.CONFIG_TIME_SET_MODE
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, stage_cfg)
                await ClockCycles(self.tb.pclk, 5)
                await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, committed['seconds'])
                await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, committed['minutes'])
                await self.tb.write_register(RTCRegisterMap.RTC_HOURS, committed['hours'])
                await self.tb.write_register(RTCRegisterMap.RTC_DAY, committed['day'])
                await self.tb.write_register(RTCRegisterMap.RTC_MONTH, committed['month'])
                await self.tb.write_register(RTCRegisterMap.RTC_YEAR, committed['year'])
                await ClockCycles(self.tb.pclk, 5)
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, base_config)  # trigger

                await ClockCycles(self.tb.pclk, k)
                await self.tb.assert_presetn()
                await ClockCycles(self.tb.pclk, 10)
                await self.tb.deassert_presetn()
                await ClockCycles(self.tb.pclk, 10)

                # Do NOT rewrite RTC_CONFIG. Measure the divider period
                # white-box: force it 2-from-target and count pclk edges
                # until r_second_tick pulses. Still on pclk (correct):
                # ~2-3 edges. Switched to rtc_clk (broken, 10x slower):
                # ~20+ edges (or none within the poll window).
                core.r_clk_div_counter.value = 99 - 2
                edges = 0
                tick_seen = False
                for _ in range(60):
                    await RisingEdge(self.tb.pclk)
                    edges += 1
                    if int(core.r_second_tick.value) == 1:
                        tick_seen = True
                        break

                final_time = await self.tb.read_time()

                point_fail = []
                if not tick_seen:
                    point_fail.append(
                        f"k={k}: no tick observed within 60 pclk after presetn while "
                        f"forced 2-from-target - consistent with the mux having "
                        f"switched to the (unforced) rtc_clk"
                    )
                elif edges > 6:
                    point_fail.append(
                        f"k={k}: tick took {edges} pclk edges after being forced "
                        f"2-from-target - expected ~2-3 if still counting on pclk "
                        f"(the programmed test clock); consistent with the mux "
                        f"having switched to rtc_clk on presetn"
                    )
                # The forced tick that proves the counter is still on the
                # test clock advances the time by exactly one second.
                committed_plus_1 = dict(committed); committed_plus_1['seconds'] += 1
                if final_time != committed_plus_1:
                    point_fail.append(
                        f"k={k}: commit did not land intact across presetn - got "
                        f"{final_time}, expected {committed}"
                    )

                if point_fail:
                    failures.extend(point_fail)

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-20 presetn does not switch the test-mode clock test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-20 presetn does not switch the test-mode clock test FAILED: {e}")
            return False

    async def test_gh56_presetn_release_no_spurious_flags(self) -> bool:
        """
        Decided contract: presetn release cannot manufacture second_tick or
        alarm_flag. Whitebox-forces rtc_core's counter-domain LEVEL sources
        (r_second_tick, r_alarm_match) high via a continuous background
        force (so the level survives across the reset regardless of the
        RTL's own un-forced counter-domain updates), sweeps the presetn
        release offset across that held-high window, W1C's any stale flags
        before each trial, and checks that RTC_STATUS.second_tick /
        alarm_flag stay CLEAR after release with no genuine new tick.

        Today u_event_sync's destination side resets with presetn (`rst_n`)
        while its counter-domain SOURCE level is untouched by presetn (only
        rtc_resetn touches the counter domain) - so release resets the
        synchronized copy to 0 against a source that is still high, and the
        edge detector reads that as a fresh 0->1 transition, manufacturing
        a flag with no real tick having occurred.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-21 presetn release manufactures no spurious flags")
        self.log.info("=" * 80)

        try:
            failures = []
            core = self.tb.dut.u_rtc_core

            for k in range(0, 14):
                await self.tb.assert_reset()
                await self.tb.wait_clocks('pclk', 10)
                await self.tb.deassert_reset()
                await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
                await self._enable_production_mode(bcd=False, hour_12=False)

                # W1C any stale flags before this trial.
                await self.tb.write_register(RTCRegisterMap.RTC_STATUS, 0xFFFFFFFF)
                await ClockCycles(self.tb.pclk, 5)

                hold = True

                async def _hold_high():
                    while hold:
                        await RisingEdge(self.tb.pclk)
                        core.r_second_tick.value = 1
                        core.r_alarm_match.value = 1

                hold_task = cocotb.start_soon(_hold_high())

                await ClockCycles(self.tb.pclk, k)
                await self.tb.assert_presetn()
                await ClockCycles(self.tb.pclk, 5)
                await self.tb.deassert_presetn()
                await ClockCycles(self.tb.pclk, 5)

                hold = False
                await ClockCycles(self.tb.pclk, 1)
                hold_task.kill()
                core.r_second_tick.value = 0
                core.r_alarm_match.value = 0

                # SYNC_STAGES(3) + the two-idle-cycle edge-detector window.
                await ClockCycles(self.tb.pclk, 15)

                _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                tick_flag = bool(status_raw & RTCRegisterMap.STATUS_SECOND_TICK)
                alarm_flag = bool(status_raw & RTCRegisterMap.STATUS_ALARM_FLAG)

                if tick_flag or alarm_flag:
                    failures.append(
                        f"k={k}: presetn released while the counter-domain tick/alarm "
                        f"level was still (whitebox-)high manufactured a flag - "
                        f"second_tick={tick_flag} alarm_flag={alarm_flag}, with no "
                        f"genuine new tick having occurred"
                    )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-21 presetn release, no spurious flags test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-21 presetn release, no spurious flags test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # GH#56 coordinator direction 2026-09-09 (sixth round: three more
    # sim-testable RTL defects found in the fifth-round review's own
    # fix). Checked against the CURRENT rtc_core.sv / rtc_config_regs.sv,
    # re-read in full this round - the config-valid gating flag (cfg_valid
    # / r_cfg_hold / r_clk_sel_held) that GH56-19/20 asked for now EXISTS,
    # and these tests are new defects found IN that fix, plus one older
    # reset-domain mismatch on the commit_timeout sticky bit, plus one
    # structural ordering test.
    #
    # GH56-R6-A/A2 root cause (rtc_core.sv ~696-720): r_cfg_hold latches
    # the WHOLE config bundle (including time_set_mode) on every cycle
    # w_ctr_cfg_valid is true - which, since cfg_valid is a level held from
    # the first-ever RTC_CONFIG write, is effectively "continuously" during
    # normal operation. A presetn pulse clears cfg_valid's SOURCE bit
    # immediately, but r_cfg_hold (reset only by the counter domain) keeps
    # whatever it last latched - if that was mid-staging (time_set_mode=1),
    # it freezes there once w_ctr_cfg_valid drops a few selected_clk cycles
    # later, and the counter stays paused until a fresh RTC_CONFIG write
    # re-establishes cfg_valid.
    #
    # GH56-R6-B root cause (rtc_core.sv ~1195-1205): w_commit_visible is a
    # pure DATA comparison (r_shd_* == r_commit_data) with no requirement
    # that a load has actually happened since the commit - so committing
    # the time that is ALREADY showing satisfies it immediately.
    #
    # GH56-R6-E root cause (rtc_core.sv ~1338-1365): r_commit_timeout_flag
    # (the sticky RTC_STATUS.commit_timeout bit) resets on plain `rst_n`
    # (presetn), while EVERYTHING ELSE that tracks the same stall
    # (r_commit_busy/_pend/_inflight/_timedout) resets on w_commit_bk_rst_n
    # (the far/rtc_resetn-derived reset) - a reset-domain mismatch on one
    # flop out of the whole bookkeeping group.
    #
    # GH56-R6-D is a structural/acceptance test with no RTL defect
    # necessarily attached to it yet - see its own docstring.
    # ------------------------------------------------------------------

    async def test_gh56_r6a_presetn_during_staging_stops_clock_forever(self) -> bool:
        """
        Decided contract: a presetn pulse landing while RTC_CONFIG.time_set_
        mode is set (staging in progress, never cleared) must not
        PERMANENTLY freeze the counter - a subsequent genuine software
        write to RTC_CONFIG (the recovery write, clearing time_set_mode)
        must unstick it and counting must resume.

        Brings the RTC up counting in test mode (clock_select=1, 100-pclk
        divider, so ticks are directly observable without whitebox
        forcing), commits a known time, confirms it is genuinely running,
        then: writes RTC_CONFIG with time_set_mode=1 (step 1 of the
        documented set-time sequence) and deliberately never clears it.
        Pulses presetn only (rtc_resetn stays high). After release,
        performs the recovery write (rtc_enable=1, time_set_mode=0) that
        software would naturally do, then polls: seconds must keep
        advancing, and the divider (r_clk_div_counter) must not be pinned
        at zero.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-R6-A presetn during staging does not permanently stop the clock")
        self.log.info("=" * 80)

        try:
            failures = []
            core = self.tb.dut.u_rtc_core

            base_config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_CLOCK_SELECT
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, base_config)
            await ClockCycles(self.tb.pclk, 5)

            start_time = {'seconds': 5, 'minutes': 10, 'hours': 4, 'day': 2, 'month': 3, 'year': 20}
            stage_cfg = base_config | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, stage_cfg)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, start_time['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, start_time['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, start_time['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, start_time['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, start_time['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, start_time['year'])
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, base_config)  # commit

            for _ in range(20):
                if not int(core.r_commit_busy.value):
                    break
                await ClockCycles(self.tb.pclk, 5)

            pre1 = await self.tb.read_time()
            await ClockCycles(self.tb.pclk, 250)
            pre2 = await self.tb.read_time()
            if pre1 == pre2:
                failures.append(
                    "setup sanity: seconds did not advance before the staging-window "
                    "scenario even began - cannot test recovery from a state that was "
                    "never running"
                )

            # Step 1: enter time_set_mode, deliberately never clear it.
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, stage_cfg)
            await ClockCycles(self.tb.pclk, 5)  # >= 5 counter clocks to cross/apply

            await self.tb.assert_presetn()
            await ClockCycles(self.tb.pclk, 10)
            await self.tb.deassert_presetn()
            await ClockCycles(self.tb.pclk, 5)

            # Recovery write software would do: rtc_enable=1, time_set_mode=0.
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, base_config)
            await ClockCycles(self.tb.pclk, 20)  # let the recovery cross

            before = await self.tb.read_time()
            div_before = int(core.r_clk_div_counter.value)
            await ClockCycles(self.tb.pclk, 350)  # >= 3 tick periods at the 100-pclk divider
            after = await self.tb.read_time()
            div_after = int(core.r_clk_div_counter.value)

            if before == after:
                failures.append(
                    f"seconds frozen after the recovery write: before={before} after={after} "
                    f"(read 350 pclk apart, >= 3 tick periods at the 100-pclk test-mode divider)"
                )
            if div_before == 0 and div_after == 0:
                failures.append(
                    "r_clk_div_counter is pinned at zero after the recovery write - the "
                    "counter never resumed"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-R6-A presetn-during-staging recovery test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-R6-A presetn-during-staging recovery test FAILED: {e}")
            return False

    async def test_gh56_r6a2_presetn_during_staging_minimal_recovery(self) -> bool:
        """
        Sibling of GH56-R6-A, same root cause: guards against a fix that
        only unsticks the counter on a "full" recovery write that
        explicitly re-asserts every bit. Same setup and step 1 (enter
        time_set_mode, never clear it, presetn only), but the ONLY write
        afterward is the plain rtc_enable=1 write software would issue to
        resume normal operation (CONFIG_RTC_ENABLE alone - no explicit
        time_set_mode=0 beyond what a fresh write naturally carries).
        Checks within 5 tick periods.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-R6-A2 presetn during staging, minimal (plain enable) recovery")
        self.log.info("=" * 80)

        try:
            failures = []
            core = self.tb.dut.u_rtc_core

            base_config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_CLOCK_SELECT
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, base_config)
            await ClockCycles(self.tb.pclk, 5)

            start_time = {'seconds': 40, 'minutes': 55, 'hours': 12, 'day': 9, 'month': 1, 'year': 26}
            stage_cfg = base_config | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, stage_cfg)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, start_time['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, start_time['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, start_time['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, start_time['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, start_time['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, start_time['year'])
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, base_config)

            for _ in range(20):
                if not int(core.r_commit_busy.value):
                    break
                await ClockCycles(self.tb.pclk, 5)

            # Step 1, never cleared.
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, stage_cfg)
            await ClockCycles(self.tb.pclk, 5)

            await self.tb.assert_presetn()
            await ClockCycles(self.tb.pclk, 10)
            await self.tb.deassert_presetn()
            await ClockCycles(self.tb.pclk, 5)

            # Minimal recovery: keep test-mode clock_select so the tick
            # stays fast/observable (a bare CONFIG_RTC_ENABLE write alone
            # would ALSO revert clock_select to its production default and
            # test something else entirely - see GH56-20); the point here
            # is that time_set_mode is not explicitly re-cleared beyond
            # what this plain write naturally carries.
            minimal_recovery = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_CLOCK_SELECT
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, minimal_recovery)
            await ClockCycles(self.tb.pclk, 20)

            before = await self.tb.read_time()
            await ClockCycles(self.tb.pclk, 500)  # <= 5 tick periods at the 100-pclk divider
            after = await self.tb.read_time()

            if before == after:
                failures.append(
                    f"seconds frozen within 5 tick periods after the MINIMAL recovery write "
                    f"(plain rtc_enable=1): before={before} after={after}"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-R6-A2 minimal-recovery test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-R6-A2 minimal-recovery test FAILED: {e}")
            return False

    async def test_gh56_r6a3_presetn_during_staging_resumes_counting_without_write(self) -> bool:
        """
        Decided contract (GH56-R6-A3, coordinator correction 2026-09-09):
        the block's headline property is that a bus reset does not disturb
        timekeeping - NO subsequent RTC_CONFIG write should be required
        for counting to resume. GH56-R6-A/A2 both happen to include a
        post-presetn RTC_CONFIG write, and ANY such write re-arms cfg_valid
        and crosses time_set_mode=0 through it - which is exactly why they
        are GREEN and do not exercise the actual defect. This test does NO
        APB write at all after presetn releases.

        Brings the RTC up counting in production mode (clock_select=0)
        with a known committed time, confirms it is genuinely advancing
        (whitebox-forced tick, same technique as GH56-19), enters
        time_set_mode (step 1 of the documented set-time sequence) and
        waits >= 5 counter clocks for the counter domain to apply it
        (white-box confirms the counter domain's time_set pause has asserted),
        pulses presetn only, and then does nothing else - no recovery
        write, ever. Contract: counting resumes on its own; seconds must
        advance and the divider must not stay pinned at zero.

        time_valid semantics are logged, not asserted, per instruction
        (RTC_CONFIG/time_valid read their reset-default values by design
        after presetn; this test is only about whether COUNTING resumes).
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-R6-A3 presetn during staging resumes counting WITHOUT a write")
        self.log.info("=" * 80)

        try:
            failures = []
            # Fresh reset: this test must not inherit leftover state (e.g.
            # A2's test-mode clock_select, or a not-yet-settled commit)
            # from whatever ran immediately before it in the sequential
            # medium-suite test list.
            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
            await self._enable_production_mode(bcd=False, hour_12=False)
            core = self.tb.dut.u_rtc_core

            start_time = {'seconds': 15, 'minutes': 25, 'hours': 6, 'day': 8, 'month': 9, 'year': 27}
            await self.tb.set_time(**start_time)
            for _ in range(20):
                if not int(core.r_commit_busy.value):
                    break
                await ClockCycles(self.tb.pclk, 5)
            # Extra settle so the just-completed commit's divider/active
            # hold has fully released before the sanity-check force below.
            await ClockCycles(self.tb.pclk, 30)

            # Confirm genuinely running before the staging-window scenario
            # begins (whitebox-forced tick, same technique as GH56-19; a
            # couple of retries for margin against the exact edge the
            # rollover lands on).
            before_sec = int(core.r_seconds.value)
            after_sec = before_sec
            for _ in range(3):
                await self.tb.force_divider_near_target(clock_select=0, remaining_cycles=2)
                await ClockCycles(self.tb.dut.rtc_clk, 4)
                after_sec = int(core.r_seconds.value)
                if after_sec != before_sec:
                    break
            if after_sec == before_sec:
                failures.append(
                    "setup sanity: seconds did not advance on 3 forced-tick attempts "
                    "before the staging-window scenario even began"
                )

            # Step 1: enter time_set_mode, never clear it.
            stage_cfg = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, stage_cfg)
            # >= 5 counter clocks (rtc_clk edges in production mode) for the
            # counter domain to apply it.
            await ClockCycles(self.tb.dut.rtc_clk, 5)

            # time_set_mode is NOT held (round-7 F1): the counter domain takes
            # it live from the crossing output, so peek the applied pause.
            held_time_set = int(core.w_ctr_time_set.value)
            if not held_time_set:
                failures.append(
                    "setup sanity: the counter domain's time_set pause did not assert within "
                    "5 rtc_clk edges of the staging write - cannot test recovery from a "
                    "state that was never actually entered"
                )

            await self.tb.assert_presetn()
            await ClockCycles(self.tb.pclk, 10)
            await self.tb.deassert_presetn()
            await ClockCycles(self.tb.pclk, 10)

            # NO recovery write of any kind from here on.
            baseline_sec = int(core.r_seconds.value)
            baseline_div = int(core.r_clk_div_counter.value)

            # Wait ~5 "tick periods" via the same whitebox-forcing technique
            # used throughout this suite for the real (32768-cycle)
            # production divider - force near rollover, let the last
            # couple of edges run naturally, repeat.
            for _ in range(5):
                await self.tb.force_divider_near_target(clock_select=0, remaining_cycles=2)
                await ClockCycles(self.tb.dut.rtc_clk, 3)

            final_sec = int(core.r_seconds.value)
            final_div = int(core.r_clk_div_counter.value)

            if final_sec == baseline_sec:
                failures.append(
                    f"seconds frozen at {baseline_sec} after a presetn-only pulse landed "
                    f"during time_set_mode staging, with NO recovery write ever issued - "
                    f"sampled again after 5 forced-tick attempts, still {final_sec}"
                )
            if baseline_div == 0 and final_div == 0:
                failures.append(
                    "r_clk_div_counter reads 0 both immediately after release and after "
                    "5 forced-tick attempts with no recovery write - the divider is "
                    "pinned at zero"
                )

            _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            time_valid_now = bool(status_raw & RTCRegisterMap.STATUS_TIME_VALID)
            self.log.info(
                f"  post-reset time_valid={time_valid_now} (informational only, not "
                f"asserted - RTC_CONFIG/time_valid read their reset defaults by design)"
            )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-R6-A3 presetn-during-staging-without-write test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-R6-A3 presetn-during-staging-without-write test FAILED: {e}")
            return False

    async def test_gh56_r6b_busy_released_by_data_coincidence(self) -> bool:
        """
        Decided contract: time_commit_busy must not release until the
        counter-domain LOAD has actually happened - not merely because the
        shadow happens to already match the committed bytes.

        rtc_core.sv's w_commit_visible does a pure DATA comparison
        (r_shd_* == r_commit_data) with no requirement that a load
        (w_commit_load) has occurred since the commit. Re-committing the
        SAME time T that is already showing makes w_commit_visible true
        from the moment the handshake accepts the request (~3 pclk), long
        before the real four-phase round trip (~40-50 pclk at the 10:1
        ratio) delivers the load - so busy can release early. The PRIMARY
        check below is exactly that: white-box confirmation that the
        load's precursor (r_commit_valid_d) has fired by the moment busy
        drops.

        Coordinator direction 2026-09-09 (round-6 RTL follow-up): a
        SECONDARY check used to also sample the raw counter-domain
        r_seconds and require it monotone. That is too strong - with the
        (now slightly slower) config crossing, a natural tick can
        legitimately land on the same counter-domain edge as the staging
        pause during a redundant commit (raw counters go T -> T+1, then
        the committed T loads over it), which is correct set-time
        semantics and is NOT software-visible: the register file holds
        the staged values while busy and shows the committed time once it
        drops. The secondary check now reads RTC_SECONDS over the APB
        interface (the same view software has) and requires THAT sequence
        monotone instead.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-R6-B busy released by data coincidence, not by the load")
        self.log.info("=" * 80)

        try:
            failures = []
            await self._enable_production_mode(bcd=False, hour_12=False)
            core = self.tb.dut.u_rtc_core

            T = {'seconds': 30, 'minutes': 15, 'hours': 10, 'day': 12, 'month': 6, 'year': 24}
            await self.tb.force_time_registers(**T, time_valid=True)
            await ClockCycles(self.tb.pclk, 30)

            shadow = await self.tb.read_time()
            if shadow != T:
                failures.append(f"setup sanity: shadow reads {shadow} instead of the forced time {T}")

            # Park the divider 2-from-rollover so a natural tick lands
            # inside the ~5-selected_clk accept-to-load window.
            await self.tb.force_divider_near_target(clock_select=0, remaining_cycles=2)

            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, T['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, T['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, T['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, T['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, T['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, T['year'])
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)  # commit

            # Whitebox: has the load's precursor (dst_valid, visible one
            # cycle later as r_commit_valid_d, a REGISTER) fired since the
            # commit? w_commit_load itself is a wire (r_commit_valid_d &&
            # dst_valid); the register is the robust handle to poke.
            load_precursor_seen = False
            seconds_trace = []
            busy_drop_pclk = None

            for i in range(80):
                if int(core.r_commit_valid_d.value):
                    load_precursor_seen = True
                seconds_trace.append(int(core.r_seconds.value))
                busy = int(core.r_commit_busy.value)
                if not busy:
                    busy_drop_pclk = i
                    break
                await ClockCycles(self.tb.pclk, 1)

            if busy_drop_pclk is None:
                failures.append("time_commit_busy never dropped within 80 pclk of the redundant commit")
            elif not load_precursor_seen:
                failures.append(
                    f"busy dropped at pclk+{busy_drop_pclk} after the redundant commit, but the "
                    f"counter-domain load's precursor (r_commit_valid_d) had NOT fired yet - "
                    f"busy was released by data coincidence, not by the load"
                )
            else:
                self.log.info(
                    f"  busy dropped at pclk+{busy_drop_pclk}; load precursor had already fired"
                )

            # End-to-end symptom, the SOFTWARE view: coordinator direction
            # 2026-09-09 (round-6 RTL follow-up) - with the config crossing
            # now one counter clock slower, the staging pause can arrive
            # one clock late, so a natural tick can legitimately land on
            # the SAME counter-domain edge as the pause during staging
            # (raw counters go T -> T+1, then the committed T loads over
            # it). That is correct set-time semantics (software committed
            # T; the staging pause is documented best-effort) and is NOT
            # software-visible: the register file holds the staged values
            # while busy and shows the committed time once busy drops. So
            # this check goes through read_register() (APB, by name) - the
            # same interface software actually uses - not a whitebox peek
            # at the raw counter-domain register. Read RTC_SECONDS
            # repeatedly, spanning a window comparable to (a couple of
            # multiples of) the primary check's own observation window
            # above, and require the readback sequence to be monotone.
            apb_seconds_trace = []
            for _ in range(40):
                _, sec = await self.tb.read_register(RTCRegisterMap.RTC_SECONDS)
                apb_seconds_trace.append(sec & 0xFF)

            apb_steps = []
            for s in apb_seconds_trace:
                if not apb_steps or apb_steps[-1] != s:
                    apb_steps.append(s)
            expected_next = (T['seconds'] + 1) % 60
            if expected_next in apb_steps:
                idx = apb_steps.index(expected_next)
                if idx + 1 < len(apb_steps) and apb_steps[idx + 1] == T['seconds']:
                    failures.append(
                        f"RTC_SECONDS (APB) readback sequence stepped backward: "
                        f"{apb_steps} (T={T['seconds']} -> T+1={expected_next} -> back "
                        f"to T={T['seconds']}) - the software-visible time must never "
                        f"move backward, even though the raw counter-domain register "
                        f"legitimately may during the (best-effort) staging pause"
                    )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-R6-B busy-by-load-not-coincidence test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-R6-B busy-by-load-not-coincidence test FAILED: {e}")
            return False

    async def test_gh56_r6e_commit_timeout_survives_presetn(self) -> bool:
        """
        Decided contract (GH56-R6-E part a): commit_timeout must SURVIVE a
        presetn-only pulse while the stall it reports is still outstanding
        (busy still set, nothing has resolved it).

        rtc_core.sv's r_commit_timeout_flag (the sticky RTC_STATUS bit)
        resets on plain `rst_n` (presetn), while everything else tracking
        the same stall (r_commit_busy et al) resets on the far/rtc_resetn
        -derived reset - a reset-domain mismatch on one flop.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-R6-E(a) commit_timeout survives a presetn-only pulse")
        self.log.info("=" * 80)

        timeout_cycles = 65535  # rtc_core.sv COMMIT_TIMEOUT_CYCLES default

        try:
            failures = []
            # Fresh reset: this test must not inherit a stale in-flight
            # commit from whatever ran immediately before it in the medium
            # suite's sequential test list.
            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
            await self._enable_production_mode(bcd=False, hour_12=False)
            core = self.tb.dut.u_rtc_core

            time_a = {'seconds': 8, 'minutes': 41, 'hours': 3, 'day': 6, 'month': 5, 'year': 19}
            time_b = {'seconds': 33, 'minutes': 27, 'hours': 21, 'day': 11, 'month': 4, 'year': 22}
            self.tb.stop_rtc_clk()
            await self.tb.set_time(**time_a)  # stalls: rtc_clk is stopped

            # Queue B behind the stalled A at half the watchdog window - for
            # a SOLO stall (nothing queued) busy correctly clears together
            # with its own timeout (round 5's fix); queuing B is what keeps
            # busy genuinely outstanding through the full window, matching
            # this contract's precondition (same pattern as GH56-18).
            half = timeout_cycles // 2
            await ClockCycles(self.tb.pclk, half)
            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_b['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_b['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_b['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_b['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_b['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_b['year'])
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)  # B queued

            remaining = (timeout_cycles - half) + 200
            await ClockCycles(self.tb.pclk, remaining)

            _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            timeout_before = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
            busy_before = int(core.r_commit_busy.value)
            if not timeout_before:
                failures.append(
                    "setup sanity: commit_timeout did not set after the watchdog window - "
                    "cannot test survival of a flag that never set"
                )
            if not busy_before:
                failures.append("setup sanity: time_commit_busy dropped before the presetn pulse")

            await self.tb.assert_presetn()
            await ClockCycles(self.tb.pclk, 10)
            await self.tb.deassert_presetn()
            await ClockCycles(self.tb.pclk, 10)

            _, status_after_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            timeout_after = bool(status_after_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
            busy_after = int(core.r_commit_busy.value)

            if not timeout_after:
                failures.append(
                    f"commit_timeout reads 0 after a presetn-only pulse even though the stall "
                    f"is still outstanding (busy={busy_after}) - the flag must survive a bus "
                    f"reset while its underlying transfer is still pending"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-R6-E(a) commit_timeout-survives-presetn test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-R6-E(a) commit_timeout-survives-presetn test FAILED: {e}")
            return False
        finally:
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()

    async def test_gh56_r6e_commit_timeout_cleared_by_rtc_resetn(self) -> bool:
        """
        Decided contract (GH56-R6-E part b): an rtc_resetn-only pulse drops
        the stalled transfer (busy clears, both handshake ends idle), and
        commit_timeout must clear WITH it - no W1C needed, because nothing
        is outstanding any more.

        Same reset-domain mismatch as part (a), opposite symptom: since
        r_commit_timeout_flag is on presetn (not the far reset), an
        rtc_resetn-only pulse does NOT touch it, so it survives set even
        though the rest of the bookkeeping it describes has been dropped.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-R6-E(b) commit_timeout cleared by an rtc_resetn-only pulse")
        self.log.info("=" * 80)

        timeout_cycles = 65535

        try:
            failures = []
            # Fresh reset: E(a) deliberately leaves a stalled, unresolved
            # commit behind (that is its whole point - presetn must not
            # touch it), so this test must not inherit that state.
            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
            await self._enable_production_mode(bcd=False, hour_12=False)
            core = self.tb.dut.u_rtc_core

            time_a = {'seconds': 51, 'minutes': 2, 'hours': 14, 'day': 21, 'month': 8, 'year': 33}
            self.tb.stop_rtc_clk()
            await self.tb.set_time(**time_a)

            await ClockCycles(self.tb.pclk, timeout_cycles + 200)

            _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            timeout_before = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
            if not timeout_before:
                failures.append("setup sanity: commit_timeout did not set after the watchdog window")

            await self.tb.assert_rtc_resetn()
            await ClockCycles(self.tb.pclk, 10)
            await self.tb.deassert_rtc_resetn()
            # The counter domain's release synchronizer (and this reset's
            # share of the commit bookkeeping) needs real selected_clk
            # edges - restart rtc_clk (killed by stop_rtc_clk() above) so
            # the release actually completes.
            await self.tb.start_rtc_clk()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES * 2)

            busy_after = int(core.r_commit_busy.value)
            _, status_after_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            timeout_after = bool(status_after_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)

            if busy_after:
                failures.append(
                    "time_commit_busy is still set after an rtc_resetn pulse - the stalled "
                    "transfer should have been dropped"
                )
            if timeout_after:
                failures.append(
                    "commit_timeout still reads 1 after an rtc_resetn-only pulse dropped the "
                    "stalled transfer, with no W1C write - nothing is outstanding any more, so "
                    "the flag should have cleared with the rest of the commit bookkeeping"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-R6-E(b) commit_timeout-cleared-by-rtc_resetn test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-R6-E(b) commit_timeout-cleared-by-rtc_resetn test FAILED: {e}")
            return False
        finally:
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()

    async def test_gh56_r6d_reset_release_ordering_vs_clock_select_reload(self) -> bool:
        """
        Structural/acceptance test (GH56-R6-D): the counter-domain reset
        must not release until AFTER r_clk_sel_held has reloaded from a
        fresh cfg_valid crossing - releasing the counter domain's reset
        (letting u_ctr_reset_sync sample selected_clk) while r_clk_sel_held
        might still be mid-transition is what produces the runt clock
        pulse rtc_core.sv's header documents (selected_clk is a plain
        combinational mux). Verilator cannot model the runt pulse itself;
        this test pins the ORDERING a fix must create instead:
        u_ctr_reset_sync's sync_rst_n output (w_ctr_rst_n) must deassert
        at least 2 pclk cycles AFTER r_clk_sel_held has already reloaded.

        Configures clock_select=1 (selected_clk=pclk, so both flops are
        directly comparable on one clock domain), pulses rtc_resetn only,
        and samples both signals on every pclk edge via a background
        coroutine. If this reads GREEN on the current RTL, that is
        reported explicitly - it becomes the acceptance test the eventual
        fix must keep passing, not evidence the defect does not exist
        (the review found it structurally, not via this specific
        sim-observable angle).
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-R6-D reset-release ordering vs clock-select reload")
        self.log.info("=" * 80)

        try:
            failures = []
            core = self.tb.dut.u_rtc_core

            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_CLOCK_SELECT
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 10)

            clk_sel_trace = []
            rst_trace = []
            sampling = True

            async def _sampler():
                while sampling:
                    await RisingEdge(self.tb.pclk)
                    clk_sel_trace.append(int(core.r_clk_sel_held.value))
                    rst_trace.append(int(core.w_ctr_rst_n.value))

            sampler_task = cocotb.start_soon(_sampler())

            await self.tb.assert_rtc_resetn()
            await ClockCycles(self.tb.pclk, 10)
            await self.tb.deassert_rtc_resetn()
            await ClockCycles(self.tb.pclk, 20)

            sampling = False
            await ClockCycles(self.tb.pclk, 1)
            sampler_task.kill()

            def first_reload_index(trace):
                """First index reading 1 after the trace has read 0 at
                least once (the reload/release edge, not mere startup)."""
                seen_zero = False
                for i, v in enumerate(trace):
                    if v == 0:
                        seen_zero = True
                    elif v == 1 and seen_zero:
                        return i
                return None

            clk_sel_reload_idx = first_reload_index(clk_sel_trace)
            rst_release_idx = first_reload_index(rst_trace)

            self.log.info(
                f"  r_clk_sel_held reload index={clk_sel_reload_idx}, "
                f"w_ctr_rst_n release index={rst_release_idx}"
            )

            if clk_sel_reload_idx is None or rst_release_idx is None:
                failures.append(
                    f"could not observe both a reset dip and a reload/release within the "
                    f"sampled window - clk_sel_trace={clk_sel_trace} rst_trace={rst_trace}"
                )
            else:
                margin = rst_release_idx - clk_sel_reload_idx
                if margin < 2:
                    failures.append(
                        f"w_ctr_rst_n released only {margin} pclk cycle(s) after "
                        f"r_clk_sel_held reloaded (release index={rst_release_idx}, reload "
                        f"index={clk_sel_reload_idx}) - the decided ordering requires >= 2 "
                        f"pclk margin so the counter-domain reset never releases while "
                        f"selected_clk could still be mid-switch"
                    )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-R6-D reset-release ordering test PASSED (GREEN today)")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-R6-D reset-release ordering test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # GH#56 coordinator direction 2026-09-09 (round-8 review): one more
    # RTL hole. Runs under the small-COMMIT_TIMEOUT_CYCLES sweep build
    # (rtc_gh56_timeout_sweep_test in dv/tests/test_apb4_rtc.py, alongside
    # GH56-16) since it needs TWO full watchdog windows to observe.
    #
    # Root cause (rtc_core.sv's commit bookkeeping, current numbering):
    # w_commit_timeout_evt is edge-detected off the CDC primitive's OWN
    # raw watchdog level (w_commit_timeout / r_timeout_cnt inside
    # cdc_4_phase_handshake), which belongs to whichever request is
    # physically sitting in S_WAIT_ACK. The wrapper's "give up and drop
    # busy" for an un-queued stall does NOT retire that request at the
    # CDC level - dst_valid never came, rtc_clk is dead, so the CDC still
    # believes it is waiting on the SAME original request forever. Once
    # w_commit_timeout has been high for more than one cycle,
    # r_commit_timeout_d (which tracks it unconditionally every cycle)
    # equals it permanently, so w_commit_timeout_evt (the EDGE) can never
    # fire again - a retry staged and queued behind that same dead link
    # gets no watchdog of its own: r_commit_pend stays 1, busy stays 1,
    # the six registers show the staged bytes forever, time_valid reads 0
    # forever, and there is no way back short of a reset.
    # ------------------------------------------------------------------

    async def test_gh56_r8_queued_retry_behind_dead_clock_times_out(self) -> bool:
        """
        Decided contract (GH56-R8-1, round-8 review; matches the
        documented recovery procedure in the README/MAS): "a commit
        issued while a timed-out transfer is still pending ... does not
        itself report a timeout unless it also exceeds the window".

        With the counter clock permanently dead (a stopped/dead crystal,
        never restarted for the first part of this test):
          1. Commit A; wait for commit_timeout=1 and busy=0 - the
             UN-QUEUED case, already correctly handled today (round 5/6's
             fix: a solo stall's own timeout release busy together with
             the report).
          2. Software does the documented recovery: W1C commit_timeout,
             then re-stage and commit again (the retry, data D1).
             Required: within ~COMMIT_TIMEOUT_CYCLES pclk of the RETRY's
             OWN commit pulse, commit_timeout reads 1 AGAIN and busy
             drops to 0 - the retry gets its own, independently-tracked
             timeout report and release, and the register mirror resumes
             (time_valid returns to what it read before the retry; the
             six registers show the counter again, not the staged
             bytes). The retry itself is NOT cancelled - it stays
             logically queued.
          3. Restart rtc_clk: the retry lands (time reads D1),
             commit_timeout retires on its own (w_commit_timeout_resolved,
             no W1C needed), busy stays 0, and nothing is delivered
             twice.

        RED today at step 2: the bounded wait (3 watchdog windows) for
        commit_timeout=1/busy=0 after the retry's own commit pulse times
        out - see this class's root-cause note above.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-R8-1 queued retry behind a dead counter clock times out on its own account")
        self.log.info("=" * 80)

        timeout_cycles = int(os.environ.get('TEST_COMMIT_TIMEOUT_CYCLES', '200'))
        poll_step = 5
        poll_iterations = max(1, (3 * timeout_cycles) // poll_step)

        try:
            failures = []
            core = self.tb.dut.u_rtc_core
            await self._enable_production_mode(bcd=False, hour_12=False)

            time_a = {'seconds': 5, 'minutes': 10, 'hours': 2, 'day': 3, 'month': 4, 'year': 20}
            time_d1 = {'seconds': 40, 'minutes': 50, 'hours': 18, 'day': 25, 'month': 10, 'year': 31}

            # Dead crystal: stopped and NEVER restarted for this whole
            # first part of the test.
            self.tb.stop_rtc_clk()

            # (1) Commit A; wait for the un-queued case's timeout/busy-drop.
            await self.tb.set_time(**time_a)

            first_ok = False
            for _ in range(poll_iterations):
                _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
                busy = int(core.r_commit_busy.value)
                if timeout_bit and not busy:
                    first_ok = True
                    break
                await ClockCycles(self.tb.pclk, poll_step)

            if not first_ok:
                failures.append(
                    "setup sanity: the un-queued commit A never reported "
                    "commit_timeout=1/busy=0 within 3 watchdog windows - cannot test "
                    "the retry behaviour on top of a precondition that never arose"
                )
                for f in failures:
                    self.log.error(f"  {f}")
                assert not failures, "; ".join(failures)

            # (2) Documented recovery: W1C commit_timeout, then re-stage
            # and commit again (the retry, D1).
            await self.tb.write_register(RTCRegisterMap.RTC_STATUS, RTCRegisterMap.STATUS_COMMIT_TIMEOUT)

            _, status_before_retry = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            time_valid_before_retry = bool(status_before_retry & RTCRegisterMap.STATUS_TIME_VALID)

            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_d1['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_d1['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_d1['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_d1['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_d1['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_d1['year'])
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)  # retry commit

            retry_ok = False
            for _ in range(poll_iterations):
                _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
                busy = int(core.r_commit_busy.value)
                if timeout_bit and not busy:
                    retry_ok = True
                    break
                await ClockCycles(self.tb.pclk, poll_step)

            if not retry_ok:
                _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
                busy = int(core.r_commit_busy.value)
                pend = int(core.r_commit_pend.value)
                time_valid_now = bool(status_raw & RTCRegisterMap.STATUS_TIME_VALID)
                staged = await self.tb.read_time()
                failures.append(
                    f"the retry (D1) never reported its OWN commit_timeout=1/busy=0 "
                    f"within 3 watchdog windows ({poll_iterations * poll_step} pclk) of "
                    f"its commit pulse - stuck at commit_timeout={timeout_bit} "
                    f"busy={busy} r_commit_pend={pend}; the register mirror never "
                    f"resumed either: time_valid={time_valid_now} (was "
                    f"{time_valid_before_retry} before the retry), staged registers "
                    f"read {staged} (still the staged D1 bytes, not the counter)"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            # (3) Restart rtc_clk: the retry lands, commit_timeout retires
            # by itself, busy stays 0, nothing delivered twice. Only
            # reached once step 2 above is fixed.
            await self.tb.start_rtc_clk()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES * 2)

            final_time = await self.tb.read_time()
            _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            timeout_after_restart = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
            busy_after_restart = int(core.r_commit_busy.value)

            if final_time != time_d1:
                failures.append(
                    f"after restarting rtc_clk the retry did not land - readable time "
                    f"is {final_time}, expected D1 {time_d1}"
                )
            if timeout_after_restart:
                failures.append(
                    "commit_timeout is still set after the retry landed and the link "
                    "settled - it should have retired on its own "
                    "(w_commit_timeout_resolved)"
                )
            if busy_after_restart:
                failures.append(
                    "time_commit_busy is still set after the retry landed and the "
                    "link settled"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-R8-1 queued-retry-behind-dead-clock test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-R8-1 queued-retry-behind-dead-clock test FAILED: {e}")
            return False
        finally:
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()

    async def test_gh56_r8_new_bytes_without_commit_not_delivered(self) -> bool:
        """
        Regression guard (GH56-R8-2, likely GREEN today): r_commit_data
        is captured AT THE COMMIT PULSE (time_set_commit), not read live
        from the register file at handover - this is what already lets a
        queued commit survive a bus reset carrying its own staged data
        rather than the register file's just-reset contents (round 5/6).
        This test checks the same guarantee against a simpler hazard:
        while a commit (D1) is queued/in-flight (busy=1) behind a dead
        counter clock, writing new bytes (D2) directly into
        RTC_SECONDS..RTC_YEAR WITHOUT issuing a new time_set_commit pulse
        (no time_set_mode entry/exit around it - a raw, out-of-protocol
        write). Those writes must be inert for the pending transfer: once
        the clock returns, the retry must still deliver D1, never D2.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-R8-2 bytes written without a new commit are not delivered")
        self.log.info("=" * 80)

        try:
            failures = []
            core = self.tb.dut.u_rtc_core
            await self._enable_production_mode(bcd=False, hour_12=False)

            time_d1 = {'seconds': 12, 'minutes': 34, 'hours': 5, 'day': 9, 'month': 7, 'year': 28}
            time_d2 = {'seconds': 58, 'minutes': 1, 'hours': 23, 'day': 17, 'month': 2, 'year': 33}

            self.tb.stop_rtc_clk()
            await self.tb.set_time(**time_d1)  # commits D1, stalls: queued/in-flight, busy=1

            busy = int(core.r_commit_busy.value)
            if not busy:
                failures.append(
                    "setup sanity: time_commit_busy dropped before the corruption "
                    "write could be attempted - D1's commit did not stay pending"
                )
                for f in failures:
                    self.log.error(f"  {f}")
                assert not failures, "; ".join(failures)

            # Raw, out-of-protocol writes into the six time registers -
            # NOT preceded by a time_set_mode entry, NOT followed by a
            # new commit pulse.
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_d2['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_d2['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_d2['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_d2['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_d2['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_d2['year'])

            await self.tb.start_rtc_clk()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES * 2)

            final_time = await self.tb.read_time()
            if final_time != time_d1:
                failures.append(
                    f"final landed time is {final_time}; expected D1 {time_d1} - D2 "
                    f"(written without its own commit pulse) must never be delivered"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-R8-2 bytes-without-commit-not-delivered test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-R8-2 bytes-without-commit-not-delivered test FAILED: {e}")
            return False
        finally:
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()

    async def test_gh56_r8_commit_queued_before_first_timeout_times_out(self) -> bool:
        """
        Decided contract (GH56-R8-3, round-8 review - the mirror image of
        GH56-R8-1): with the counter clock dead, committing B WHILE A is
        still within its OWN window (not yet timed out) queues B exactly
        as GH56-16's scenario does - but GH56-16 only covers busy holding
        through commit_timeout meeting link-idle; it never exercises B
        getting its OWN watchdog report once A's has already fired and
        been W1C'd.

        Sequence: rtc_clk stopped. Commit A (data DA). Within ~50 pclk
        (well inside A's window) stage and commit B (data DB). Wait for
        A's timeout: commit_timeout=1, busy STILL 1 - this part is
        GH56-16's own contract (busy must stay set because B is queued)
        and is asserted here as a precondition that must hold GREEN. W1C
        the flag. Then, within ~COMMIT_TIMEOUT_CYCLES pclk measured from
        B's OWN commit pulse (bounded wait of 3 windows), commit_timeout
        must read 1 AGAIN and busy must read 0, and the mirror must
        resume (time_valid back to its pre-commit value, the six
        registers show the counter, not DB). Then restart rtc_clk: DB
        lands (never DA), the flag retires by itself, busy stays 0.

        Same root cause as GH56-R8-1 (rtc_core.sv's single CDC watchdog
        belongs to whichever request is physically sitting in S_WAIT_ACK
        - still A here, since B's own req_src is never handed to the CDC
        while A remains unacknowledged), but the queuing ORDER is the
        opposite: B is queued while A's window is still open, rather than
        after A has already been reported as timed out.

        RED today at the second report: busy stays stuck at 1 forever
        after the W1C, commit_timeout never sets again (the CDC's raw
        watchdog level never dropped, so its edge detector cannot refire),
        and the six registers keep showing DB with time_valid stuck at 0.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-R8-3 commit queued before A's own timeout still times out on its own account")
        self.log.info("=" * 80)

        timeout_cycles = int(os.environ.get('TEST_COMMIT_TIMEOUT_CYCLES', '200'))
        poll_step = 5
        poll_iterations = max(1, (3 * timeout_cycles) // poll_step)

        try:
            failures = []
            core = self.tb.dut.u_rtc_core
            await self._enable_production_mode(bcd=False, hour_12=False)

            time_da = {'seconds': 3, 'minutes': 22, 'hours': 9, 'day': 14, 'month': 6, 'year': 27}
            time_db = {'seconds': 47, 'minutes': 8, 'hours': 16, 'day': 2, 'month': 11, 'year': 35}

            self.tb.stop_rtc_clk()

            # Commit A.
            await self.tb.set_time(**time_da)

            # Within ~50 pclk (well inside A's window), stage and commit B.
            await ClockCycles(self.tb.pclk, 50)

            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_db['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_db['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_db['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_db['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_db['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_db['year'])
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)  # B's commit pulse

            # Wait for A's timeout: commit_timeout=1, busy STILL 1
            # (GH56-16's own contract - asserted here as a precondition
            # that must hold GREEN).
            a_timeout_seen = False
            for _ in range(poll_iterations):
                _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
                busy = int(core.r_commit_busy.value)
                if timeout_bit:
                    a_timeout_seen = True
                    if not busy:
                        failures.append(
                            "busy dropped when A's timeout set even though B is queued "
                            "behind it - violates GH56-16's own contract (busy must "
                            "stay set while a commit is pending)"
                        )
                    break
                await ClockCycles(self.tb.pclk, poll_step)

            if not a_timeout_seen:
                failures.append(
                    "setup sanity: A's commit_timeout never set within 3 watchdog "
                    "windows - cannot test B's own report on top of a precondition "
                    "that never arose"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            # W1C the flag.
            await self.tb.write_register(RTCRegisterMap.RTC_STATUS, RTCRegisterMap.STATUS_COMMIT_TIMEOUT)

            _, status_before = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            time_valid_before = bool(status_before & RTCRegisterMap.STATUS_TIME_VALID)

            # Within ~COMMIT_TIMEOUT_CYCLES of B's OWN commit pulse
            # (bounded wait of 3 windows for margin), B must report ITS
            # OWN timeout and release busy.
            b_ok = False
            for _ in range(poll_iterations):
                _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
                busy = int(core.r_commit_busy.value)
                if timeout_bit and not busy:
                    b_ok = True
                    break
                await ClockCycles(self.tb.pclk, poll_step)

            if not b_ok:
                _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
                busy = int(core.r_commit_busy.value)
                pend = int(core.r_commit_pend.value)
                time_valid_now = bool(status_raw & RTCRegisterMap.STATUS_TIME_VALID)
                staged = await self.tb.read_time()
                failures.append(
                    f"B never reported its OWN commit_timeout=1/busy=0 within 3 "
                    f"watchdog windows ({poll_iterations * poll_step} pclk) of its "
                    f"commit pulse - stuck at commit_timeout={timeout_bit} busy={busy} "
                    f"r_commit_pend={pend}; the register mirror never resumed either: "
                    f"time_valid={time_valid_now} (was {time_valid_before} before), "
                    f"staged registers read {staged} (still DB, not the counter)"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            # Restart rtc_clk: DB lands (never DA), the flag retires by
            # itself, busy stays 0. Only reached once the above is fixed.
            await self.tb.start_rtc_clk()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES * 2)

            final_time = await self.tb.read_time()
            _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            timeout_after_restart = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
            busy_after_restart = int(core.r_commit_busy.value)

            if final_time != time_db:
                failures.append(
                    f"after restarting rtc_clk, readable time is {final_time}, "
                    f"expected B's time DB {time_db} (DA must never land)"
                )
            if timeout_after_restart:
                failures.append("commit_timeout is still set after B landed and the link settled")
            if busy_after_restart:
                failures.append("time_commit_busy is still set after B landed and the link settled")

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-R8-3 commit-queued-before-first-timeout test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-R8-3 commit-queued-before-first-timeout test FAILED: {e}")
            return False
        finally:
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()

    # ------------------------------------------------------------------
    # GH#56 coordinator direction 2026-09-09 (round-9 review): three
    # same-edge races in the queued-commit watchdog, plus one guard.
    # Each needs an event on one exact pclk edge; APB write timing is
    # deterministic, so a one-time whitebox calibration of the
    # trigger-write-to-pulse latency positions the sweep precisely.
    # ------------------------------------------------------------------

    async def _calibrate_trigger_pulse_offset(self) -> int:
        """Whitebox-measure how many pclk RisingEdges after the FINAL
        (time_set_mode-clearing) RTC_CONFIG write's write_register() call
        returns, the resulting time_set_commit pulse actually fires. APB
        write timing is deterministic, so this offset is a fixed,
        reusable constant for a given build - used to position a LATER
        commit's trigger write so its pulse lands on a precisely
        predicted pclk edge, rather than guessing a fixed margin."""
        core = self.tb.dut.u_rtc_core
        await self.tb.assert_reset()
        await self.tb.wait_clocks('pclk', 10)
        await self.tb.deassert_reset()
        await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
        await self._enable_production_mode(bcd=False, hour_12=False)

        config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
        await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
        await ClockCycles(self.tb.pclk, 10)

        pulse_offset = None

        async def _watch():
            nonlocal pulse_offset
            cycles = 0
            while pulse_offset is None and cycles < 20:
                await RisingEdge(self.tb.pclk)
                cycles += 1
                if int(core.time_set_commit.value):
                    pulse_offset = cycles

        watch_task = cocotb.start_soon(_watch())
        await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)
        await ClockCycles(self.tb.pclk, 20)
        watch_task.kill()
        return pulse_offset if pulse_offset is not None else 2

    async def test_gh56_r9_1_new_commit_same_edge_as_pending_expiry(self) -> bool:
        """
        GH56-R9-1 (F1, round-9 review, HIGH): a commit pulse landing on
        the SAME pclk edge as the CURRENTLY-QUEUED commit's own
        pend-watchdog expiry (w_pend_timeout_evt) disarms the NEW commit
        forever.

        rtc_core.sv's r_pend_timedout is written by TWO separate
        top-level if-blocks in the SAME always_ff: the queue block
        (`if (time_set_commit) ... r_pend_timedout <= 1'b0;`, clearing it
        for a fresh commit) and a SEPARATE, LATER block
        (`if (w_pend_timeout_evt) r_pend_timedout <= 1'b1;`). Verilog
        non-blocking assignment gives the LAST block in program order the
        final value - so when a fresh commit's pulse coincides exactly
        with the OLD queued commit's own expiry, the expiry's SET wins
        over the fresh pulse's CLEAR, and the freshly-armed commit
        inherits a stale "already timed out" mark despite r_pend_wdog
        having just been reset to 0. Since the count-enable condition is
        `r_commit_pend && r_pend_wdog_arm && !r_pend_timedout`, a stuck
        r_pend_timedout=1 freezes r_pend_wdog at 0 forever - the count is
        dead, w_pend_timeout_evt (which also needs !r_pend_timedout) can
        never fire again, and busy never releases.

        Three commits are structurally required to make
        w_pend_timeout_evt a reachable precondition at all: A occupies
        the link (rtc_clk dead, A accepted almost immediately - source-
        side accept does not depend on the destination clock - then
        stalls forever), B queues behind A and its OWN per-queued-commit
        watchdog counts toward COMMIT_TIMEOUT_CYCLES, and C is a fresh
        REPLACEMENT commit whose trigger write is precisely positioned
        (via the calibrated APB write-to-pulse latency) and then swept
        across ~8 pclk around the predicted w_pend_timeout_evt edge for B.

        Property, asserted at EVERY sweep point: within 3 windows of C's
        commit pulse, busy reads 0 and commit_timeout reads 1 (it must
        SET AGAIN for C) and the mirror has resumed.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-R9-1 new commit pulse on the same edge as a pending expiry")
        self.log.info("=" * 80)

        timeout_cycles = int(os.environ.get('TEST_COMMIT_TIMEOUT_CYCLES', '200'))
        pclk_period_ns = int(os.environ.get('TEST_APB_CLOCK_PERIOD', '10'))

        pulse_offset = await self._calibrate_trigger_pulse_offset()
        self.log.info(f"  calibrated trigger-write-to-pulse offset: {pulse_offset} pclk")

        time_a = {'seconds': 1, 'minutes': 2, 'hours': 3, 'day': 4, 'month': 5, 'year': 6}
        time_b = {'seconds': 11, 'minutes': 12, 'hours': 13, 'day': 14, 'month': 6, 'year': 16}
        time_c = {'seconds': 21, 'minutes': 22, 'hours': 21, 'day': 24, 'month': 7, 'year': 26}

        sweep = list(range(-4, 5))  # ~8 pclk window around the predicted edge
        point_failures_all = []

        try:
            core = self.tb.dut.u_rtc_core

            for d in sweep:
                await self.tb.assert_reset()
                await self.tb.wait_clocks('pclk', 10)
                await self.tb.deassert_reset()
                await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
                await self._enable_production_mode(bcd=False, hour_12=False)

                self.tb.stop_rtc_clk()

                # A: occupies the link (accepted almost immediately, then
                # stalls forever).
                await self.tb.set_time(**time_a)

                # B: queues behind A. Its own pend-watchdog starts
                # counting from THIS commit pulse.
                config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
                await ClockCycles(self.tb.pclk, 5)
                await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_b['seconds'])
                await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_b['minutes'])
                await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_b['hours'])
                await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_b['day'])
                await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_b['month'])
                await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_b['year'])
                await ClockCycles(self.tb.pclk, 5)
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)
                b_pulse_ns = get_sim_time('ns')

                # Stage C's fields early - only the FINAL trigger write's
                # timing is swept.
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
                await ClockCycles(self.tb.pclk, 5)
                await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_c['seconds'])
                await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_c['minutes'])
                await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_c['hours'])
                await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_c['day'])
                await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_c['month'])
                await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_c['year'])

                # Precisely position C's trigger write: B's
                # w_pend_timeout_evt is predicted at
                # b_pulse + (COMMIT_TIMEOUT_CYCLES + 1) pclk.
                target_pulse_pclk = timeout_cycles + 1 + d
                target_trigger_ns = b_pulse_ns + (target_pulse_pclk - pulse_offset) * pclk_period_ns
                wait_pclk = max(0, round((target_trigger_ns - get_sim_time('ns')) / pclk_period_ns))
                await ClockCycles(self.tb.pclk, wait_pclk)

                coincidence_seen = False

                async def _watch_coincidence():
                    nonlocal coincidence_seen
                    while True:
                        await RisingEdge(self.tb.pclk)
                        if int(core.time_set_commit.value) and int(core.w_pend_timeout_evt.value):
                            coincidence_seen = True

                watch_task = cocotb.start_soon(_watch_coincidence())
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)  # C's trigger
                await ClockCycles(self.tb.pclk, 10)
                watch_task.kill()

                point_failures = []
                self.log.info(
                    f"  d={d}: coincidence(time_set_commit & w_pend_timeout_evt) "
                    f"observed={coincidence_seen}"
                )

                ok = False
                for _ in range(3 * timeout_cycles // 5 + 20):
                    _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                    timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
                    busy = int(core.r_commit_busy.value)
                    if timeout_bit and not busy:
                        ok = True
                        break
                    await ClockCycles(self.tb.pclk, 5)

                if not ok:
                    _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                    timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
                    busy = int(core.r_commit_busy.value)
                    pend = int(core.r_commit_pend.value)
                    pend_wdog = int(core.r_pend_wdog.value)
                    pend_timedout = int(core.r_pend_timedout.value)
                    point_failures.append(
                        f"d={d} (coincidence={coincidence_seen}): C never reported its "
                        f"own commit_timeout=1/busy=0 within 3 windows of its trigger - "
                        f"stuck at commit_timeout={timeout_bit} busy={busy} "
                        f"r_commit_pend={pend} r_pend_wdog={pend_wdog} "
                        f"r_pend_timedout={pend_timedout}"
                    )

                if point_failures:
                    point_failures_all.append((d, point_failures))

                await self.tb.start_rtc_clk()

            failures = []
            if point_failures_all:
                summary = "; ".join(f"d={d}: {'; '.join(p)}" for d, p in point_failures_all)
                failures.append(f"failed at {len(point_failures_all)}/{len(sweep)} sweep point(s): {summary}")

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-R9-1 new-commit-same-edge-as-pending-expiry test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-R9-1 new-commit-same-edge-as-pending-expiry test FAILED: {e}")
            return False
        finally:
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()

    async def _calibrate_restart_to_accept_latency(self) -> int:
        """Whitebox-measure how many pclk RisingEdges after restarting
        rtc_clk (following a commit A stalled with the clock dead, and B
        queued behind it) it takes for A to complete and B to be accepted
        (w_commit_accept). Restarted immediately after B's own commit, so
        this captures A's real 4-phase round-trip latency uncontaminated
        by any pend-watchdog race. Coordinator correction 2026-09-09: the
        accept edge lags the clock restart by this (synchronizer-driven)
        latency, so a sweep centred on the predicted expiry cycle in
        RESTART time must subtract it, not guess a flat margin."""
        core = self.tb.dut.u_rtc_core
        timeout_cycles = int(os.environ.get('TEST_COMMIT_TIMEOUT_CYCLES', '200'))
        await self.tb.assert_reset()
        await self.tb.wait_clocks('pclk', 10)
        await self.tb.deassert_reset()
        await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
        await self._enable_production_mode(bcd=False, hour_12=False)

        time_a = {'seconds': 9, 'minutes': 8, 'hours': 7, 'day': 6, 'month': 5, 'year': 4}
        time_b = {'seconds': 19, 'minutes': 18, 'hours': 17, 'day': 16, 'month': 6, 'year': 14}

        self.tb.stop_rtc_clk()
        await self.tb.set_time(**time_a)

        # Match the real test's structure exactly (including A's own
        # in-flight report + W1C before B is staged) so this calibration
        # captures the SAME latency the real sweep will see - measuring
        # against a simplified setup left a systematic bias.
        for _ in range(3 * timeout_cycles // 5 + 20):
            _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            if status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT:
                break
            await ClockCycles(self.tb.pclk, 5)
        await self.tb.write_register(RTCRegisterMap.RTC_STATUS, RTCRegisterMap.STATUS_COMMIT_TIMEOUT)

        config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
        await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
        await ClockCycles(self.tb.pclk, 5)
        await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_b['seconds'])
        await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_b['minutes'])
        await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_b['hours'])
        await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_b['day'])
        await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_b['month'])
        await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_b['year'])
        await ClockCycles(self.tb.pclk, 5)
        await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)

        accept_offset = None

        async def _watch():
            nonlocal accept_offset
            cycles = 0
            while accept_offset is None and cycles < 300:
                await RisingEdge(self.tb.pclk)
                cycles += 1
                if int(core.w_commit_accept.value):
                    accept_offset = cycles

        watch_task = cocotb.start_soon(_watch())
        await self.tb.start_rtc_clk()
        await ClockCycles(self.tb.pclk, 300)
        watch_task.kill()
        return accept_offset if accept_offset is not None else 90

    async def test_gh56_r9_2_accept_same_edge_as_pending_expiry(self) -> bool:
        """
        GH56-R9-2 (F2, round-9 review, MED - corrected 2026-09-09):
        B's ACCEPT landing on the same pclk edge as B's OWN pend-watchdog
        expiry emits a report that never retires, and drops busy with B
        still in flight.

        Coordinator correction: the first version of this test swept the
        restart time centred on the predicted EXPIRY cycle without
        accounting for the (synchronizer-driven) latency from restart to
        accept, so the accept edge never actually landed on the expiry
        cycle - it always swept up landing AFTER the expiry (the
        legitimate "B's own report released busy, then B was accepted
        with busy already 0" case), which is not this defect. Fixed by
        calibrating that restart-to-accept latency once (white-box), then
        sweeping the restart time so the accept edge is actually centred
        on r_pend_wdog == COMMIT_TIMEOUT_CYCLES / w_pend_timeout_evt, and
        recording which of the three orderings (accept strictly before
        expiry, expiry strictly before accept, or coincidence) was
        actually observed at each point - the property asserted is
        DERIVED from what was measured, not from the sweep label:
          - accept strictly before expiry: busy stays 1 from accept until
            the load; no report is raised for B.
          - expiry strictly before accept: busy is 0 from the expiry
            (legitimate - B's own report already released it); the
            report must retire by itself once B lands (bounded wait, no
            W1C).
          - coincidence: the required behaviour is "accepted within its
            window" - no report, busy stays 1 until the load; but if a
            report IS raised on that edge (today's bug), it must at
            least retire on its own once B lands.

        Today the coincidence point sets the flag with the timed-out mark
        lost (never retires) and drops busy with B still in flight.
        Exactly one sweep point is expected to hit the coincidence.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-R9-2 accept on the same edge as a pending expiry")
        self.log.info("=" * 80)

        timeout_cycles = int(os.environ.get('TEST_COMMIT_TIMEOUT_CYCLES', '200'))
        pclk_period_ns = int(os.environ.get('TEST_APB_CLOCK_PERIOD', '10'))

        accept_latency = await self._calibrate_restart_to_accept_latency()
        self.log.info(f"  calibrated restart-to-accept latency: {accept_latency} pclk")

        time_a = {'seconds': 5, 'minutes': 6, 'hours': 7, 'day': 8, 'month': 9, 'year': 10}
        time_b = {'seconds': 41, 'minutes': 42, 'hours': 19, 'day': 20, 'month': 8, 'year': 31}

        sweep = list(range(-4, 5))
        point_failures_all = []
        coincidence_points = []

        try:
            core = self.tb.dut.u_rtc_core

            for d in sweep:
                await self.tb.assert_reset()
                await self.tb.wait_clocks('pclk', 10)
                await self.tb.deassert_reset()
                await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
                await self._enable_production_mode(bcd=False, hour_12=False)

                self.tb.stop_rtc_clk()
                await self.tb.set_time(**time_a)

                # Wait for A's OWN in-flight report and W1C it, so it
                # cannot be mistaken for a report raised on B's account
                # later.
                a_reported = False
                for _ in range(3 * timeout_cycles // 5 + 20):
                    _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                    if status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT:
                        a_reported = True
                        break
                    await ClockCycles(self.tb.pclk, 5)
                if not a_reported:
                    point_failures_all.append((d, ["setup sanity: A's own timeout was never reported"]))
                    continue
                await self.tb.write_register(RTCRegisterMap.RTC_STATUS, RTCRegisterMap.STATUS_COMMIT_TIMEOUT)

                config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
                await ClockCycles(self.tb.pclk, 5)
                await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_b['seconds'])
                await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_b['minutes'])
                await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_b['hours'])
                await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_b['day'])
                await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_b['month'])
                await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_b['year'])
                await ClockCycles(self.tb.pclk, 5)
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)
                b_pulse_ns = get_sim_time('ns')

                # Position the restart so the ACCEPT edge (not the
                # restart edge) lands at COMMIT_TIMEOUT_CYCLES+1+d pclk
                # after B's pulse - i.e. subtract the calibrated latency
                # from the restart time. RESIDUAL_BIAS_PCLK is a SECOND,
                # empirically-observed correction on top of the
                # single-point accept_latency calibration: with only that
                # calibration applied, the observed accept-vs-expiry gap
                # grew linearly with d (10, 11, 12, 13, 14 pclk for
                # d=-3..1, i.e. exactly the intended 1-pclk-per-d step,
                # just uniformly offset) across two independent clean-
                # build runs - the d-to-d granularity was already exactly
                # right, so the whole target window was shifted by this
                # constant rather than mis-scaled.
                RESIDUAL_BIAS_PCLK = 13
                target_accept_pclk = timeout_cycles + 1 + d
                target_restart_ns = b_pulse_ns + (target_accept_pclk - accept_latency - RESIDUAL_BIAS_PCLK) * pclk_period_ns
                wait_pclk = max(0, round((target_restart_ns - get_sim_time('ns')) / pclk_period_ns))
                await ClockCycles(self.tb.pclk, wait_pclk)

                accept_time_ns = None
                expiry_time_ns = None
                busy_dropped_before_loaded = False

                async def _watch():
                    nonlocal accept_time_ns, expiry_time_ns, busy_dropped_before_loaded
                    while True:
                        await RisingEdge(self.tb.pclk)
                        if accept_time_ns is None and int(core.w_commit_accept.value):
                            accept_time_ns = get_sim_time('ns')
                        if expiry_time_ns is None and int(core.w_pend_timeout_evt.value):
                            expiry_time_ns = get_sim_time('ns')
                        if int(core.r_commit_inflight.value) and not int(core.r_commit_loaded.value):
                            if not int(core.r_commit_busy.value):
                                busy_dropped_before_loaded = True

                watch_task = cocotb.start_soon(_watch())
                await self.tb.start_rtc_clk()
                await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES * 2)
                watch_task.kill()

                final_time = await self.tb.read_time()
                _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
                busy_final = int(core.r_commit_busy.value)

                coincide = (accept_time_ns is not None and expiry_time_ns is not None
                            and accept_time_ns == expiry_time_ns)
                accept_before_expiry = (accept_time_ns is not None and
                                         (expiry_time_ns is None or accept_time_ns < expiry_time_ns))
                expiry_before_accept = (expiry_time_ns is not None and
                                         (accept_time_ns is None or expiry_time_ns < accept_time_ns))

                self.log.info(
                    f"  d={d}: accept_ns={accept_time_ns} expiry_ns={expiry_time_ns} "
                    f"coincide={coincide} final={final_time} commit_timeout={timeout_bit} "
                    f"busy={busy_final}"
                )

                point_failures = []
                if final_time != time_b:
                    point_failures.append(f"d={d}: B did not land - final={final_time}, expected {time_b}")

                if coincide:
                    coincidence_points.append(d)
                    if busy_dropped_before_loaded:
                        point_failures.append(
                            f"d={d} (coincidence): busy dropped while B was still in "
                            f"flight (accepted within its window, should not release "
                            f"busy before the load)"
                        )
                    if timeout_bit:
                        point_failures.append(
                            f"d={d} (coincidence): a report was raised on the "
                            f"accept/expiry edge and never retired on its own - "
                            f"commit_timeout is still set after B landed and the link "
                            f"settled, with no W1C"
                        )
                elif accept_before_expiry:
                    if busy_dropped_before_loaded:
                        point_failures.append(
                            f"d={d} (accept before expiry): busy dropped while B was "
                            f"still in flight"
                        )
                    if timeout_bit:
                        point_failures.append(
                            f"d={d} (accept before expiry): commit_timeout is set even "
                            f"though B was accepted within its window"
                        )
                elif expiry_before_accept:
                    # busy_dropped_before_loaded is EXPECTED/legitimate
                    # here (busy released by B's own report before
                    # accept) - not asserted.
                    if timeout_bit:
                        point_failures.append(
                            f"d={d} (expiry before accept): commit_timeout never "
                            f"retired on its own after B landed and the link settled"
                        )
                else:
                    point_failures.append(
                        f"d={d}: neither accept nor expiry was observed within the "
                        f"settle window"
                    )

                if point_failures:
                    point_failures_all.append((d, point_failures))

            failures = []
            if point_failures_all:
                summary = "; ".join(f"d={d}: {'; '.join(p)}" for d, p in point_failures_all)
                failures.append(
                    f"failed at {len(point_failures_all)}/{len(sweep)} sweep point(s): "
                    f"{summary}; coincidence observed at d={coincidence_points}"
                )

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-R9-2 accept-same-edge-as-pending-expiry test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-R9-2 accept-same-edge-as-pending-expiry test FAILED: {e}")
            return False
        finally:
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()

    async def test_gh56_r9_3_resolve_not_transfer_identified(self) -> bool:
        """
        GH56-R9-3 (F3, round-9 review, LOW): resolve is not transfer-
        identified - A's completion can retire B's OUTSTANDING report.

        rtc_core.sv's w_commit_timeout_resolved is
        `w_commit_complete && r_commit_timedout`. r_commit_timedout is a
        single, transfer-agnostic flop: it is whatever the LAST commit
        to be accepted inherited from r_pend_timedout at ITS OWN accept,
        or whatever the in-flight CDC-level watchdog last set. When A
        (accepted almost immediately, so it inherits nothing from
        r_pend_timedout) later times out in flight, r_commit_timedout
        becomes 1 for A's stall. If B (queued behind A) THEN produces its
        OWN, separate report (w_pend_timeout_evt, which sets the STICKY
        STATUS flag directly, independent of r_commit_timedout) while
        r_commit_timedout is still 1 from A, then whenever A finally
        completes, w_commit_timeout_resolved fires (using A's stale mark)
        and clears the sticky flag - even though the flag is currently
        reporting B's still-outstanding stall, not A's already-resolved
        one.

        A in flight and marked (clock dead, A timed out, flag reported,
        W1C'd); B queued; let B's window expire (flag set again = B's
        report); then restart the clock at a swept delay so A's real
        completion lands around when B's report was just raised.
        Property: B's report must remain visible until B itself
        completes - polled until B lands, it must never read 0 before
        B's load.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-R9-3 resolve is not transfer-identified")
        self.log.info("=" * 80)

        timeout_cycles = int(os.environ.get('TEST_COMMIT_TIMEOUT_CYCLES', '200'))
        pclk_period_ns = int(os.environ.get('TEST_APB_CLOCK_PERIOD', '10'))

        time_a = {'seconds': 3, 'minutes': 33, 'hours': 3, 'day': 13, 'month': 3, 'year': 13}
        time_b = {'seconds': 44, 'minutes': 44, 'hours': 4, 'day': 24, 'month': 4, 'year': 24}

        sweep = list(range(-4, 5))
        point_failures_all = []

        try:
            core = self.tb.dut.u_rtc_core

            for d in sweep:
                await self.tb.assert_reset()
                await self.tb.wait_clocks('pclk', 10)
                await self.tb.deassert_reset()
                await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
                await self._enable_production_mode(bcd=False, hour_12=False)

                self.tb.stop_rtc_clk()
                await self.tb.set_time(**time_a)  # A: occupies link, in flight

                a_reported = False
                for _ in range(3 * timeout_cycles // 5 + 20):
                    _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                    if status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT:
                        a_reported = True
                        break
                    await ClockCycles(self.tb.pclk, 5)
                if not a_reported:
                    point_failures_all.append((d, ["setup sanity: A's own timeout was never reported"]))
                    continue
                await self.tb.write_register(RTCRegisterMap.RTC_STATUS, RTCRegisterMap.STATUS_COMMIT_TIMEOUT)

                config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
                await ClockCycles(self.tb.pclk, 5)
                await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_b['seconds'])
                await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_b['minutes'])
                await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_b['hours'])
                await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_b['day'])
                await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_b['month'])
                await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_b['year'])
                await ClockCycles(self.tb.pclk, 5)
                await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)

                b_expired = False
                for _ in range(3 * timeout_cycles // 5 + 20):
                    _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                    if status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT:
                        b_expired = True
                        break
                    await ClockCycles(self.tb.pclk, 5)
                if not b_expired:
                    point_failures_all.append((d, [f"d={d}: B's own report never set"]))
                    continue
                b_expiry_ns = get_sim_time('ns')

                target_restart_ns = b_expiry_ns + d * pclk_period_ns
                wait_pclk = max(0, round((target_restart_ns - get_sim_time('ns')) / pclk_period_ns))
                await ClockCycles(self.tb.pclk, wait_pclk)
                await self.tb.start_rtc_clk()

                dropped_before_b_landed = None
                b_landed_at = None
                for i in range(200):
                    _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                    timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
                    pend = int(core.r_commit_pend.value)
                    inflight = int(core.r_commit_inflight.value)
                    loaded = int(core.r_commit_loaded.value)
                    b_landed = (not pend) and (not inflight) and bool(loaded)
                    if b_landed:
                        b_landed_at = i
                        break
                    if not timeout_bit:
                        dropped_before_b_landed = i
                        break
                    await ClockCycles(self.tb.pclk, 2)

                await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
                final_time = await self.tb.read_time()

                point_failures = []
                self.log.info(
                    f"  d={d}: dropped_before_b_landed={dropped_before_b_landed} "
                    f"b_landed_at={b_landed_at} final={final_time}"
                )
                if dropped_before_b_landed is not None:
                    point_failures.append(
                        f"d={d}: commit_timeout read 0 at poll #{dropped_before_b_landed}, "
                        f"before B's load completed - A's completion resolved B's "
                        f"still-outstanding report"
                    )
                if final_time != time_b:
                    point_failures.append(
                        f"d={d}: B did not land - final={final_time}, expected {time_b}"
                    )

                if point_failures:
                    point_failures_all.append((d, point_failures))

            failures = []
            if point_failures_all:
                summary = "; ".join(f"d={d}: {'; '.join(p)}" for d, p in point_failures_all)
                failures.append(f"failed at {len(point_failures_all)}/{len(sweep)} sweep point(s): {summary}")

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-R9-3 resolve-not-transfer-identified test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-R9-3 resolve-not-transfer-identified test FAILED: {e}")
            return False
        finally:
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()

    async def test_gh56_r8_4_report_retires_on_replacement_commit_landing(self) -> bool:
        """
        Guard (GH56-R8-4, F6 contract, round-9 review): a report standing
        for the QUEUED slot must retire by itself when the commit that
        FINALLY lands from that slot completes - even if the slot's data
        was REPLACED after the report was raised.

        B queued and its window expires (report standing); commit C
        replaces B in the queue slot before the clock returns; clock
        returns; C lands. Property: the report retires on its own once C
        completes (bounded wait, no W1C). Reports actual behaviour either
        way - w_commit_timeout_resolved is `w_commit_complete &&
        r_commit_timedout`, and r_commit_timedout is set from
        r_pend_timedout AT C's OWN accept (rtc_core.sv: "the queued
        commit carries its own timed-out mark across the handover"); C
        itself never timed out (r_pend_timedout was cleared at C's own
        commit pulse), so r_commit_timedout should read 0 for C, and
        whether that resolves a flag raised by B's EARLIER report is
        exactly the open question this guard checks.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#56-R8-4 report retires when the replacement commit lands (guard)")
        self.log.info("=" * 80)

        timeout_cycles = int(os.environ.get('TEST_COMMIT_TIMEOUT_CYCLES', '200'))

        try:
            failures = []
            core = self.tb.dut.u_rtc_core
            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES)
            await self._enable_production_mode(bcd=False, hour_12=False)

            time_a = {'seconds': 2, 'minutes': 4, 'hours': 6, 'day': 8, 'month': 10, 'year': 12}
            time_b = {'seconds': 15, 'minutes': 16, 'hours': 17, 'day': 18, 'month': 11, 'year': 22}
            time_c = {'seconds': 33, 'minutes': 34, 'hours': 12, 'day': 27, 'month': 3, 'year': 35}

            self.tb.stop_rtc_clk()
            await self.tb.set_time(**time_a)

            config = RTCRegisterMap.CONFIG_RTC_ENABLE | RTCRegisterMap.CONFIG_TIME_SET_MODE
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_b['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_b['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_b['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_b['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_b['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_b['year'])
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)  # B's commit

            b_expired = False
            for _ in range(3 * timeout_cycles // 5 + 20):
                _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
                if status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT:
                    b_expired = True
                    break
                await ClockCycles(self.tb.pclk, 5)
            if not b_expired:
                failures.append("setup sanity: B's own report never set")
                for f in failures:
                    self.log.error(f"  {f}")
                assert not failures, "; ".join(failures)

            # Replace B with C in the queue slot BEFORE the clock returns.
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, config)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_SECONDS, time_c['seconds'])
            await self.tb.write_register(RTCRegisterMap.RTC_MINUTES, time_c['minutes'])
            await self.tb.write_register(RTCRegisterMap.RTC_HOURS, time_c['hours'])
            await self.tb.write_register(RTCRegisterMap.RTC_DAY, time_c['day'])
            await self.tb.write_register(RTCRegisterMap.RTC_MONTH, time_c['month'])
            await self.tb.write_register(RTCRegisterMap.RTC_YEAR, time_c['year'])
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.write_register(RTCRegisterMap.RTC_CONFIG, RTCRegisterMap.CONFIG_RTC_ENABLE)  # C's commit

            await self.tb.start_rtc_clk()
            await ClockCycles(self.tb.pclk, self.COMMIT_SETTLE_CYCLES * 3)

            final_time = await self.tb.read_time()
            _, status_raw = await self.tb.read_register(RTCRegisterMap.RTC_STATUS)
            timeout_bit = bool(status_raw & RTCRegisterMap.STATUS_COMMIT_TIMEOUT)
            busy = int(core.r_commit_busy.value)

            self.log.info(f"  after C lands: final={final_time} commit_timeout={timeout_bit} busy={busy}")

            if final_time != time_c:
                failures.append(f"C did not land - final={final_time}, expected {time_c}")
            if timeout_bit:
                failures.append(
                    "commit_timeout is still set after C (the commit that finally "
                    "landed from the replaced queue slot) completed and the link "
                    "settled - the report standing for that slot did not retire on "
                    "its own"
                )
            if busy:
                failures.append("time_commit_busy is still set after C landed and the link settled")

            for f in failures:
                self.log.error(f"  {f}")
            assert not failures, "; ".join(failures)

            self.log.info("GH#56-R8-4 report-retires-on-replacement-landing test PASSED (GREEN)")
            return True

        except AssertionError as e:
            self.log.error(f"GH#56-R8-4 report-retires-on-replacement-landing test FAILED: {e}")
            return False
        finally:
            if getattr(self.tb, '_rtc_clk_task', None) is None:
                await self.tb.start_rtc_clk()
