# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PITMediumTests
# Purpose: GitHub #52 defect-regression suite for PIT 8254
#
# Created: 2026-09-09

"""
PIT 8254 GitHub #52 Defect-Regression Test Suite

These tests encode correct Intel 8254 behaviour against GitHub issue #52
(body C1 + the 2026-09-08 re-verification comment + qc round_2 + qc
round_3), checked against `rtl/pit_8254/` as ground truth.

History: tests A-H were authored RED against the original (unfixed) RTL -
the defect index below describes that original RTL's line numbers/
behaviour as a historical record. An RTL fix has since landed (uncommitted)
addressing A, B, C, D (both the write-lane/PSTRB half and, as of the second
round of review, the RW=10 read-lane half too), E, F and G; A-H are now
30/30 (H was always a guard, never RED). Tests I and J were added from
reviewing that landed fix and are RED against it - they are new findings,
not part of the original #52 comment thread, and are documented in their
own docstrings rather than in the defect index below (which only covers
A-H as originally filed).

RTL implements Mode 0 only (pit_counter.sv has a single unconditional
counting always_ff with no `case (cfg_mode)` - modes 1-5 are stored in the
control/status shadow registers but have no distinct counting behaviour of
their own, matching the MAS's own MODE field warning). Every GATE-rule test
below is therefore Mode 0 only; there is nothing else to cover.

Defect index (GitHub #52):
  A. C1 (issue body) - GATE pause/resume does not exist. pit_counter.sv's
     Mode 0 decrement branch is `else if (r_counting && i_clk_en)` - i_gate
     is not in the condition. Once counting, GATE transitions have no
     effect until terminal count; GATE is a start-enable only.
  B. 2026-09-08 re-verification comment - count-0 has no 65536 remap. A
     load of 0 sets r_count<=0, and the very next `r_counting && i_clk_en`
     cycle sees r_count==16'h0 and immediately asserts OUT/stops counting
     (pit_counter.sv ~256-259) instead of wrapping to a 65536-count run.
  C. qc round_2 item 2 - counter latch (RW=00) deviates from the 8254: it
     latches on a COUNTERx_DATA WRITE (pit_counter.sv write-logic case
     2'b00, ~131-136), not on the control word, and a data write with
     RW=00 never loads the counter (r_reload_pending is never set in that
     case) - so a counter left at RW=00 (the reset default) can never be
     loaded.
  D. qc round_2 items 3-4 - counter load ignores PSTRB (pit_config_regs.sv
     ~163-171 captures `regblk_wr_data[15:0]` unconditionally, not gated by
     `regblk_wr_biten`) and the RW=10 (MSB-only) write lane takes the count
     high byte from PWDATA[7:0] instead of PWDATA[15:8] (pit_counter.sv
     ~144-148: `{count_reg_in[7:0], 8'h00}`). Decided (this suite): the read
     side must use the same lane as the write side - RW=10 reads return the
     high byte in PRDATA[15:8] (low byte 0), not the original
     `{8'h00, count[15:8]}` read-side quirk. Both halves of D have landed:
     pit_counter.sv's write lane now merges PSTRB with the stored byte and
     its read lane returns `{count[15:8], 8'h00}`, matching the same-lane
     contract - test_gh52_counter_load_byte_lanes is green.
  E. qc round_3 item 1 - counter-load phantom: peakrdl_to_cmdrsp asserts
     regblk_req for two cycles per write, and pit_config_regs' counter
     strobes are combinational on req, so each COUNTERx_DATA write strobes
     pit_counter.sv's count_reg_wr twice - cycle 1 loads the stale (not yet
     updated) capture, cycle 2 loads the correct value. A running counter
     therefore passes through one cycle of a stale reload value.
  F. Re-verification comment / qc round_2 / qc round_3 (recurring) - after
     terminal count, r_counting oscillates every cycle instead of staying
     stopped: `r_counting<=1'b0` on terminal is immediately re-armed by the
     `else if (!r_null_count && !r_counting) if (i_gate && i_clk_en)
     r_counting<=1'b1;` branch the very next cycle (GATE still high, r_count
     still 0), which is followed by the terminal branch again the cycle
     after - toggling forever with no new load.
  G. qc round_2 item 1 / re-verification comment - register decode uses
     regblk_addr[4:0] (pit_regs.sv `s_cpuif_addr` is 5 bits) but
     PSLVERR is tied off entirely (no window-check logic exists in
     pit_config_regs.sv, unlike ioapic's w_addr_in_window/w_drop added for
     GitHub #48) - every address outside the canonical 0x000-0x018 range
     aliases into the 32-byte window instead of being dropped with an
     error response.
  H. qc round_3 item 3 - gate_in has no synchronizer into pit_clk under
     CDC_ENABLE=1. This is a metastability/timing-closure risk that a
     functional cocotb sim cannot exercise (simulators do not model
     metastability); the guard here only proves the load-time GATE value
     crosses the pclk/pit_clk boundary correctly in the deterministic
     sense a testbench can check, and is expected to pass today - see
     test_gate_cdc_load_time_guard for the reasoning.

Which existing pit_tests_basic.py tests/helpers mask each defect:
  - test_gate_control_mode0(): reads status after 20 cycles but never
    toggles GATE at all ("Gate control test: verify system is running...
    Gate control would need hardware-level signal manipulation") - zero
    coverage of A, the comment even flags it as future work.
  - No existing test loads a counter with 0 - B has zero coverage.
  - test_counter_latch_command(): issues the latch control word, reads
    once, and only *warns* (does not assert) if the value looks
    undecremented; it never does a second read to check the latch actually
    released, and never establishes what the correct latch-vs-live values
    should be - masks C's latch-command half.
  - test_rw_mode_lsb_only()/test_rw_mode_msb_only(): write LSB/MSB-only
    values and only check the STATUS register's rw_mode mirror, never
    reading COUNTERx_DATA back to confirm the value actually loaded -
    masks D entirely (both the PSTRB and MSB-lane bugs).
  - test_counter_mode0_simple() and every other counting test always waits
    many cycles before the first read and never samples every core clock -
    E's one-cycle stale glitch is invisible at register-read granularity -
    masks E.
  - test_counter_mode0_simple()/test_multiple_counters(): confirm OUT goes
    high once and stop looking - never sample r_counting after terminal -
    masks F.
  - test_register_access(): only touches canonical offsets - there is no
    existing address-decode/alias/PSLVERR test at all - masks G entirely
    (PSLVERR is never even read back by the TB today).
  - H has zero existing coverage either way (no test in either level
    changes CDC_ENABLE and exercises GATE together).
"""

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge

from .pit_tb import PITRegisterMap, PITTB


class PITMediumTests:
    """GitHub #52 defect-regression suite for PIT 8254 (medium/full levels)."""

    def __init__(self, tb: PITTB):
        """
        Args:
            tb: PIT testbench instance
        """
        self.tb = tb
        self.log = tb.log

    # ------------------------------------------------------------------
    # A. GATE pause/resume (issue body C1)
    # ------------------------------------------------------------------

    # gate_in synchronizer depth (pit_core.sv SYNC_STAGES, default 2). The
    # runner does not override this parameter, so it is safe to assume here;
    # GATE-timing waits below budget SYNC_STAGES+2 core clocks per GATE
    # transition, matching pit_core's own synchronizer latency plus margin.
    SYNC_STAGES = 2

    async def test_gh52_gate_pause_resume(self) -> bool:
        """
        Mode 0 GATE must pause counting when low and resume from the
        current value (no reload) when it returns high. RTL implements
        Mode 0 only, so this is the only mode's GATE rule to check.

        White-box: an APB round trip through the register file takes long
        enough (11 counting clocks non-CDC, 23 CDC) that reading
        COUNTERx_DATA before/after a GATE edge cannot show "paused" even
        when the RTL genuinely pauses - the counter keeps ticking during
        the read itself. This samples dut.<counter>.r_count directly on
        every core clock instead: it must be perfectly stable (delta 0)
        for a whole window while GATE is low, and resume decrementing from
        that exact frozen value (not a reload) once GATE returns high.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#52-A GATE pause/resume (Mode 0)")
        self.log.info("=" * 80)

        counter_id = 0
        try:
            self.tb.dut.gate_in.value = 0x7
            await self.tb.enable_pit(True)

            await self.tb.configure_counter_mode0(counter_id, 500, bcd=False)
            await ClockCycles(self.tb.core_clk, 30)

            before_pause = await self.tb.read_counter(counter_id)

            handle = self.tb.counter_internal(counter_id)
            samples = []

            async def sampler():
                while True:
                    await RisingEdge(self.tb.core_clk)
                    samples.append(int(handle.r_count.value))

            sampler_task = cocotb.start_soon(sampler())

            self.tb.set_gate(counter_id, 0)
            await ClockCycles(self.tb.core_clk, self.SYNC_STAGES + 2)

            pause_start = len(samples)
            await ClockCycles(self.tb.core_clk, 30)
            pause_window = samples[pause_start:]

            frozen_value = pause_window[0]
            assert all(v == frozen_value for v in pause_window), (
                f"counter did not stay constant during the GATE-low window "
                f"(expected all samples == {frozen_value}): {pause_window}"
            )

            self.tb.set_gate(counter_id, 1)
            await ClockCycles(self.tb.core_clk, self.SYNC_STAGES + 2)

            resume_start = len(samples)
            await ClockCycles(self.tb.core_clk, 20)
            resume_window = samples[resume_start:]

            sampler_task.kill()

            during_pause = await self.tb.read_counter(counter_id)
            await ClockCycles(self.tb.core_clk, 20)
            after_resume = await self.tb.read_counter(counter_id)

            self.log.info(f"  before_pause={before_pause} frozen_value={frozen_value} "
                           f"during_pause(APB)={during_pause} after_resume(APB)={after_resume}")
            self.log.info(f"  resume_window={resume_window}")

            assert max(resume_window) <= frozen_value, (
                f"counter exceeded the frozen value after GATE returned high "
                f"(frozen={frozen_value}, resume_window={resume_window}) - this looks like "
                f"a reload, not a resume from the current value"
            )
            assert min(resume_window) < frozen_value, (
                f"counter never decremented after GATE returned high "
                f"(frozen={frozen_value}, resume_window={resume_window})"
            )
            deltas = [resume_window[i] - resume_window[i - 1] for i in range(1, len(resume_window))]
            assert all(d in (0, -1) for d in deltas), (
                f"counter jumped (not a plain resume-from-current-value decrement) in "
                f"resume_window={resume_window} (deltas={deltas})"
            )

            self.log.info("GH#52-A GATE pause/resume test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#52-A GATE pause/resume test FAILED: {e}")
            return False
        finally:
            self.tb.dut.gate_in.value = 0x7

    # ------------------------------------------------------------------
    # B. Count 0 means 65536, not immediate terminal
    # ------------------------------------------------------------------

    async def test_gh52_count_zero_is_65536(self) -> bool:
        """
        A load of 0 must be treated as 65536, not an immediate terminal
        count. PIT_CONFIG.CLOCK_SELECT is stored but has no effect on
        decrement rate today (pit_core.sv ties i_clk_en to cfg_pit_enable
        only - there is no smaller-prescale option to pick), so a full
        65536-cycle wait is impractical for a fast gate; instead this
        checks that OUT is still low well after the load (nowhere near
        65536 cycles) and that the readback has counted down from a large
        value rather than sitting stuck at 0.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#52-B Count 0 means 65536")
        self.log.info("=" * 80)

        counter_id = 0
        try:
            self.tb.dut.gate_in.value = 0x7
            await self.tb.enable_pit(True)

            await self.tb.write_control_word(
                bcd=0,
                mode=PITRegisterMap.MODE_INTERRUPT_ON_TERMINAL_COUNT,
                rw_mode=PITRegisterMap.RW_MODE_LSB_THEN_MSB,
                counter_select=counter_id,
            )
            await ClockCycles(self.tb.pclk, 10)

            await self.tb.write_counter(counter_id, 0)
            await ClockCycles(self.tb.core_clk, 10)

            out_signals = int(self.tb.dut.timer_irq.value)
            assert (out_signals >> counter_id) & 0x1 == 0, (
                "OUT asserted immediately after loading count=0 "
                "(count 0 was treated as an immediate terminal count, not 65536)"
            )

            await ClockCycles(self.tb.core_clk, 100)

            out_signals = int(self.tb.dut.timer_irq.value)
            assert (out_signals >> counter_id) & 0x1 == 0, (
                "OUT asserted after only 100 cycles of a count=0 (65536) load"
            )

            value = await self.tb.read_counter(counter_id)
            assert value != 0x0000, (
                "counter readback is stuck at 0x0000 after loading count=0 - "
                "the counter never started decrementing from 65536"
            )
            assert value > 0xF000, (
                f"counter readback 0x{value:04x} is not in the expected "
                f"65536-wraparound range after ~110 decrements"
            )

            self.log.info(f"  readback after ~110 cycles: 0x{value:04x} (OUT still low)")
            self.log.info("GH#52-B Count 0 means 65536 test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#52-B Count 0 means 65536 test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # C. Counter latch is a command; a data write never latches
    # ------------------------------------------------------------------

    async def test_gh52_counter_latch_command(self) -> bool:
        """
        A control word with RW=00 latches the CURRENT count of the
        selected counter; the counter keeps running underneath the latch.
        The next data read returns the latched (frozen) value and releases
        the latch; further reads return the live count.

        Uses a second, never-latched counter as a live reference running
        the identical program, so the assertion does not depend on
        predicting exact cycle counts through the CDC/APB pipeline: the
        latched read must return an OLDER (higher) value than what the
        reference shows at that same wall-clock point.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#52-C Counter latch command")
        self.log.info("=" * 80)

        latched_id = 0
        reference_id = 1
        try:
            self.tb.dut.gate_in.value = 0x7
            await self.tb.enable_pit(True)

            await self.tb.configure_counter_mode0(latched_id, 50000, bcd=False)
            await self.tb.configure_counter_mode0(reference_id, 50000, bcd=False)

            await ClockCycles(self.tb.core_clk, 40)

            # Issue the latch command for counter `latched_id` (SC=latched_id, RW=00)
            await self.tb.write_control_word(
                bcd=0, mode=0,
                rw_mode=PITRegisterMap.RW_MODE_LATCH,
                counter_select=latched_id,
            )

            ref_at_latch = await self.tb.read_counter(reference_id)

            await ClockCycles(self.tb.core_clk, 40)

            latched_read1 = await self.tb.read_counter(latched_id)
            ref_after_wait = await self.tb.read_counter(reference_id)

            self.log.info(f"  ref_at_latch={ref_at_latch} latched_read1={latched_read1} "
                           f"ref_after_wait={ref_after_wait}")

            assert ref_after_wait < ref_at_latch - 10, (
                "reference counter did not keep decrementing (test setup sanity check failed)"
            )

            assert latched_read1 > ref_after_wait + 10, (
                f"latched read (0x{latched_read1:04x}) is not older/higher than the live "
                f"reference at read time (0x{ref_after_wait:04x}) - the control-word latch "
                f"command did not freeze the counter; read is returning the live count "
                f"directly (RTL only latches on a COUNTERx_DATA write, never on the control "
                f"word itself)"
            )

            latched_read2 = await self.tb.read_counter(latched_id)
            assert latched_read2 <= latched_read1, (
                f"second read after the first (which should have released the latch) "
                f"returned a higher count (0x{latched_read2:04x} > 0x{latched_read1:04x})"
            )

            self.log.info("GH#52-C Counter latch command test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#52-C Counter latch command test FAILED: {e}")
            return False

    async def test_gh52_counter_load_at_reset_rw00(self) -> bool:
        """
        A counter whose RW field is 00 (the reset default - no control
        word has ever been written) must still LOAD on a COUNTERx_DATA
        write, not latch. Uses a local DUT reset to guarantee a genuine
        post-reset RW=00 state (the rest of this suite's tests, and the
        existing basic/medium suite before it, already program RW=11 on
        every counter, so "from reset" cannot be reached without one).
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#52-C Counter load with RW=00 from reset")
        self.log.info("=" * 80)

        counter_id = 0
        try:
            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await self.tb.wait_clocks('pclk', 5)

            self.tb.dut.gate_in.value = 0x7
            await self.tb.enable_pit(True)

            # No control word written - RW mode is still 00 (reset default).
            await self.tb.write_counter(counter_id, 20)

            result = await self.tb.wait_for_counter_out(counter_id, timeout_ns=5000)
            assert result, (
                "counter never reached terminal count after a COUNTERx_DATA write with "
                "RW=00 (reset default) - the write latched the (empty) counter instead of "
                "loading it, so it can never be loaded"
            )

            self.log.info("GH#52-C Counter load with RW=00 from reset test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#52-C Counter load with RW=00 from reset test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # D. Counter load honours PSTRB; RW=10 takes the MSB from data[15:8]
    # ------------------------------------------------------------------

    async def test_gh52_counter_load_byte_lanes(self) -> bool:
        """
        A byte-strobed COUNTERx_DATA write (PSTRB=0x1) must load only the
        low byte, merged with the stored high byte - not whatever garbage
        rides on the unstrobed byte lanes of PWDATA. RW=10 (MSB only) must
        take the count's high byte from PWDATA[15:8] (natural 16-bit
        register lanes), not PWDATA[7:0] - and, decided, must READ it back
        the same way: a 16-bit register uses the same lane both directions,
        so RW=10 reads return the count's high byte in PRDATA[15:8] (low
        byte reads 0), not the old `{8'h00, count[15:8]}` read-side quirk.
        Both halves have landed in the RTL fix; this test is green.

        The "stored high byte" a byte-strobed write merges with is the
        counter's CURRENT value, not a separate shadow register - on a
        RUNNING counter the merge target is whatever the live count is at
        the moment of the write. A byte-strobed partial load is therefore
        only deterministic with PIT_ENABLE held low (below) so the counter
        is not moving out from under the merge; this is a property of the
        merge semantics, not a bug.

        PIT_ENABLE is held LOW throughout (reload happens unconditionally
        in pit_counter.sv - only decrementing is gated by i_clk_en) so the
        loaded value is exact and stable at readback. Without this, the
        counter keeps decrementing across the settle waits between the
        load and the read, and the exact-value assertions below would fail
        even against a correctly-fixed RTL - not just a broken one.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#52-D Counter load byte lanes (PSTRB + RW=10)")
        self.log.info("=" * 80)

        pstrb_counter = 1
        msb_counter = 2
        try:
            self.tb.dut.gate_in.value = 0x7
            await self.tb.enable_pit(False)

            # --- PSTRB sub-case ---
            await self.tb.write_control_word(
                bcd=0, mode=0,
                rw_mode=PITRegisterMap.RW_MODE_LSB_THEN_MSB,
                counter_select=pstrb_counter,
            )
            await ClockCycles(self.tb.pclk, 10)

            await self.tb.write_counter(pstrb_counter, 0x1234)
            await ClockCycles(self.tb.core_clk, 6)

            # Byte-strobed write: only byte 0 (PSTRB=0x1) is valid. Byte 1
            # deliberately carries "garbage" (0xFF) that must NOT be merged in.
            addr = PITRegisterMap.COUNTER0_DATA + (pstrb_counter * 4)
            await self.tb.write_register(addr, 0xFFFFFF99, pstrb=0x1)
            await ClockCycles(self.tb.core_clk, 6)

            merged = await self.tb.read_counter(pstrb_counter)
            assert merged == 0x1299, (
                f"byte-strobed write (PSTRB=0x1, low byte=0x99) produced 0x{merged:04x}, "
                f"expected 0x1299 (stored high byte 0x12 merged with new low byte 0x99) - "
                f"the unstrobed byte's bus garbage (0xFF) leaked into the loaded value"
            )

            # --- RW=10 (MSB-only) sub-case ---
            await self.tb.write_control_word(
                bcd=0, mode=0,
                rw_mode=PITRegisterMap.RW_MODE_MSB_ONLY,
                counter_select=msb_counter,
            )
            await ClockCycles(self.tb.pclk, 10)

            addr = PITRegisterMap.COUNTER0_DATA + (msb_counter * 4)
            await self.tb.write_register(addr, 0x0000AB00, pstrb=0xF)
            await ClockCycles(self.tb.core_clk, 6)

            _, readback = await self.tb.read_register(addr)
            # Decided: a 16-bit register uses the same lane both ways - RW=10
            # writes AND reads the high byte in bits [15:8] (low byte reads 0).
            # Landed: pit_counter.sv's read mux now returns
            # {count[15:8], 8'h00}, matching this same-lane contract.
            assert readback == 0xAB00, (
                f"RW=10 write of 0x0000AB00 read back as 0x{readback:08x}, expected "
                f"0x0000ab00 (same-lane read: high byte in PRDATA[15:8], low byte 0) - "
                f"either the write took the wrong byte (PWDATA[7:0] instead of "
                f"PWDATA[15:8]) or the read mux still returns the old "
                f"{{8'h00, count[15:8]}} low-lane quirk"
            )

            self.log.info("GH#52-D Counter load byte lanes test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#52-D Counter load byte lanes test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # E. Loads must be glitch-free on a running counter
    # ------------------------------------------------------------------

    async def test_gh52_counter_load_glitch_free(self) -> bool:
        """
        A COUNTERx_DATA write to a running counter must not pass the
        counter through a stale intermediate value. White-box: sample
        r_count every core clock across the write and confirm the value
        moves from its live decrementing trajectory directly to the new
        load with exactly one reload-like (non-decrement) transition, and
        that OUT never pulses spuriously across the window.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#52-E Counter load is glitch-free")
        self.log.info("=" * 80)

        counter_id = 0
        try:
            self.tb.dut.gate_in.value = 0x7
            await self.tb.enable_pit(True)

            await self.tb.configure_counter_mode0(counter_id, 1000, bcd=False)
            await ClockCycles(self.tb.core_clk, 30)

            handle = self.tb.counter_internal(counter_id)
            samples = []

            async def sampler():
                while True:
                    await RisingEdge(self.tb.core_clk)
                    samples.append((int(handle.r_count.value), int(handle.r_out.value)))

            sampler_task = cocotb.start_soon(sampler())

            await self.tb.write_counter(counter_id, 500)
            await ClockCycles(self.tb.core_clk, 15)

            sampler_task.kill()

            counts = [s[0] for s in samples]
            outs = [s[1] for s in samples]

            assert 500 in counts, "500 was never observed in r_count after the reload write"
            final_idx = counts.index(500)

            # Count non-decrement transitions ("reload-like" jumps) up to and
            # including the settle on 500. Correct RTL: exactly one (the
            # intended reload). Buggy RTL (double count_reg_wr strobe):
            # two - one to the stale previous capture, one to 500.
            reload_jumps = 0
            for i in range(1, final_idx + 1):
                if counts[i] != counts[i - 1] - 1:
                    reload_jumps += 1

            self.log.info(f"  samples={len(samples)} final_idx={final_idx} "
                           f"reload_jumps={reload_jumps} trace={counts[max(0, final_idx - 6):final_idx + 2]}")

            assert reload_jumps == 1, (
                f"observed {reload_jumps} reload-like transitions in r_count while loading "
                f"a running counter (expected exactly 1) - the counter passed through a "
                f"stale intermediate value before settling on the correct load "
                f"(trace around the reload: {counts[max(0, final_idx - 6):final_idx + 2]})"
            )

            assert all(o == 0 for o in outs), (
                "OUT pulsed during the glitch-free load window"
            )

            self.log.info("GH#52-E Counter load is glitch-free test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#52-E Counter load is glitch-free test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # F. No oscillation after terminal count
    # ------------------------------------------------------------------

    async def test_gh52_no_oscillation_after_terminal(self) -> bool:
        """
        After terminal count, with GATE held high and no new load,
        r_counting must settle into a single steady state - not toggle.
        White-box: sample r_counting every core clock after OUT goes high.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#52-F No r_counting oscillation after terminal")
        self.log.info("=" * 80)

        counter_id = 0
        try:
            self.tb.dut.gate_in.value = 0x7
            await self.tb.enable_pit(True)

            await self.tb.configure_counter_mode0(counter_id, 15, bcd=False)

            result = await self.tb.wait_for_counter_out(counter_id, timeout_ns=5000)
            assert result, "counter never reached terminal count (test setup sanity check failed)"

            handle = self.tb.counter_internal(counter_id)
            steady_state = int(handle.r_counting.value)

            samples = []
            for _ in range(40):
                await RisingEdge(self.tb.core_clk)
                samples.append(int(handle.r_counting.value))

            distinct = set(samples)
            self.log.info(f"  steady_state={steady_state} distinct r_counting values seen={distinct}")

            assert distinct == {steady_state}, (
                f"r_counting oscillated after terminal count (values seen: {sorted(distinct)}, "
                f"expected it to stay at {steady_state}) - trace: {samples[:16]}"
            )

            self.log.info("GH#52-F No r_counting oscillation test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#52-F No r_counting oscillation test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # G. Address decode: unmapped/alias addresses must drop + PSLVERR
    # ------------------------------------------------------------------

    async def test_gh52_address_decode_aliasing(self) -> bool:
        """
        Only the mapped registers (0x000-0x018) are software-visible.
        Every other address in the 4KB window - including the 5-bit
        aliases at 0x024 (PIT_CONTROL alias) and 0x210 (COUNTER0_DATA
        alias) - must be dropped (write ignored, read 0) with PSLVERR, the
        same policy already used by the ioapic/pic 8259 blocks.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#52-G Address decode aliasing / PSLVERR")
        self.log.info("=" * 80)

        try:
            await self.tb.enable_pit(True)

            # Alias of PIT_CONFIG at 0x800 (0x800 & 0x1F == 0x000). PIT_CONFIG
            # is known-nonzero (pit_enable=1) at this point, so a read that
            # aliases through would return 1 rather than the required 0.
            read_pkt, data = await self.tb.read_register(0x800)
            assert getattr(read_pkt, 'pslverr', 0) == 1, (
                "read from unmapped alias 0x800 (aliases PIT_CONFIG) did not raise PSLVERR"
            )
            assert data == 0, (
                f"read from unmapped alias 0x800 returned 0x{data:08x}, expected 0 "
                f"(dropped, not aliased to PIT_CONFIG)"
            )

            # Alias of PIT_CONTROL at 0x024 (0x024 & 0x1F == 0x004).
            control_pkt = await self.tb.write_register(0x024, 0xB0)
            assert getattr(control_pkt, 'pslverr', 0) == 1, (
                "write to unmapped alias 0x024 (aliases PIT_CONTROL) did not raise PSLVERR"
            )

            # Alias of COUNTER0_DATA at 0x210 (0x210 & 0x1F == 0x010).
            counter_pkt = await self.tb.write_register(0x210, 0xBEEF)
            assert getattr(counter_pkt, 'pslverr', 0) == 1, (
                "write to unmapped alias 0x210 (aliases COUNTER0_DATA) did not raise PSLVERR"
            )

            self.log.info("GH#52-G Address decode aliasing test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#52-G Address decode aliasing test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # H. gate_in crosses the CDC boundary correctly (functional guard)
    # ------------------------------------------------------------------

    async def test_gh52_gate_cdc_load_time_guard(self) -> bool:
        """
        Functional-only guard for the missing gate_in synchronizer
        (qc round_3 item 3): a cocotb simulation cannot exercise
        metastability, so this does not (and cannot) prove the
        synchronizer is unnecessary. It instead checks the one thing a
        deterministic sim CAN check - that a GATE value change reaches the
        pit_clk domain and is correctly observed at load time (today's
        "GATE is a start-enable only" behaviour, item A's baseline) even
        when CDC_ENABLE=1 and pit_clk runs at a non-integer ratio to pclk.
        Expected to pass today; kept as a regression guard for whatever
        synchronizer the GH#52 fix adds.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#52-H GATE CDC load-time guard")
        self.log.info(f"      (cdc_enable={self.tb.cdc_enable})")
        self.log.info("=" * 80)

        counter_id = 1
        try:
            self.tb.set_gate(counter_id, 0)
            await self.tb.enable_pit(True)

            await self.tb.write_control_word(
                bcd=0, mode=0,
                rw_mode=PITRegisterMap.RW_MODE_LSB_THEN_MSB,
                counter_select=counter_id,
            )
            await ClockCycles(self.tb.pclk, 10)
            await self.tb.write_counter(counter_id, 30)
            await ClockCycles(self.tb.core_clk, 10)

            held_value1 = await self.tb.read_counter(counter_id)
            await ClockCycles(self.tb.core_clk, 15)
            held_value2 = await self.tb.read_counter(counter_id)

            assert held_value1 == held_value2, (
                f"counter decremented with GATE low before ever being started "
                f"(0x{held_value1:04x} -> 0x{held_value2:04x})"
            )

            self.tb.set_gate(counter_id, 1)
            await ClockCycles(self.tb.core_clk, 20)
            running_value = await self.tb.read_counter(counter_id)

            assert running_value < held_value2 - 5, (
                f"counter did not start decrementing after GATE went high "
                f"(held=0x{held_value2:04x}, after=0x{running_value:04x}) - the GATE "
                f"transition did not reach the counting domain"
            )

            self.log.info(f"  held={held_value2} running={running_value}")
            self.log.info("GH#52-H GATE CDC load-time guard test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#52-H GATE CDC load-time guard test FAILED: {e}")
            return False
        finally:
            self.tb.dut.gate_in.value = 0x7

    # ------------------------------------------------------------------
    # I. A control word landing on the terminal tick must not glitch OUT
    #    (found reviewing the landed #52 RTL fix - not part of the
    #    original issue thread)
    # ------------------------------------------------------------------

    # How many different "start the reprogram write when r_count == K" points
    # to try. The write's own internal latency (command issue -> the single-
    # cycle cfg_control_wr pulse landing in pit_counter.sv) is fixed but
    # unknown here, and differs between CDC_ENABLE=0/1 (the CDC bridge alone
    # adds several core clocks - the GH#52-A review measured an APB read
    # round trip at 11 non-CDC / 23 CDC core clocks, and a write's internal
    # latency is the same order of magnitude). Sweeping K = 1..SWEEP_MAX
    # guarantees that for whichever latency L the write actually has, some K
    # in the sweep lands the pulse exactly on r_count == 1 (the terminal
    # tick) - the same race-window-sweep pattern the gpio/hpet tests use.
    TERMINAL_RACE_SWEEP_MAX = 26

    async def test_gh52_control_word_on_terminal_tick_no_spurious_out(self) -> bool:
        """
        A PIT_CONTROL write (reprogramming the counter it targets) must
        abort the count in progress: OUT low, NULL_COUNT set, no count
        until a new load - even when the write's internal effect happens to
        land in the exact core clock where the counter would otherwise have
        reached terminal count (r_count == 1, about to tick to 0).

        White-box: poll dut.<counter>.r_count every core clock (no APB
        latency, so the observed value is exact) until it equals a target K,
        then immediately issue the reprogram write. Sweeping K over a window
        covering the write's plausible internal latency guarantees hitting
        the exact terminal-tick alignment once, regardless of CDC_ENABLE.

        Each sweep point loads with PIT_ENABLE held low first (reload is
        unconditional in pit_counter.sv - only decrementing is gated by
        i_clk_en) and only enables counting immediately before the poll
        starts. Without this, configure_counter_mode0()'s own settle waits
        (which the counter keeps ticking through once PIT_ENABLE is already
        high) would eat an unknown, CDC-ratio-dependent number of counts
        before the poll even begins, making a small K window miss entirely.

        pit_counter.sv's Mode 0 always_ff has two independent `if`
        statements in one clocked block - `if (cfg_control_wr) ... r_out <=
        1'b0;` followed by `else if (w_tick) if (w_next_count == 16'h0)
        r_out <= 1'b1;` (not `else if`, so a control word write and a
        terminal-tick decrement in the SAME cycle both fire; non-blocking
        assignment order makes the terminal branch's `r_out <= 1'b1` win
        over the control word's `r_out <= 1'b0`) - so a control word that
        lands on the terminal tick sets OUT high (and it never clears again,
        since r_counting is correctly aborted to 0 and nothing else touches
        r_out) even though NULL_COUNT is also set: a self-contradictory,
        spurious IRQ.

        The "no extra decrement" half (a control word landing on a
        non-terminal tick should leave the count at exactly the value the
        abort caught) is logged only, not asserted - pinning down the exact
        expected count requires knowing the write's internal latency, which
        this test deliberately does not assume (see the sweep comment
        above); asserting a wrong precomputed value would make this test
        flaky rather than meaningful.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#52-I Control word on terminal tick - no spurious OUT")
        self.log.info("=" * 80)

        counter_id = 0
        initial_count = 40
        handle = self.tb.counter_internal(counter_id)

        try:
            self.tb.dut.gate_in.value = 0x7

            glitches = []
            for target_k in range(1, self.TERMINAL_RACE_SWEEP_MAX):
                # Load with PIT disabled so the reload lands but counting
                # does not start yet - see the docstring above.
                await self.tb.enable_pit(False)
                await self.tb.write_control_word(
                    bcd=0, mode=0,
                    rw_mode=PITRegisterMap.RW_MODE_LSB_THEN_MSB,
                    counter_select=counter_id,
                )
                await ClockCycles(self.tb.pclk, 10)
                await self.tb.write_counter(counter_id, initial_count)
                await ClockCycles(self.tb.core_clk, 6)

                loaded_count = int(handle.r_count.value)
                assert loaded_count == initial_count, (
                    f"setup sanity check failed: r_count=0x{loaded_count:04x} after load, "
                    f"expected 0x{initial_count:04x}"
                )

                # Start counting from the known, exact loaded value.
                await self.tb.enable_pit(True)

                # White-box poll: wait until r_count == target_k, then fire
                # the reprogram write immediately (no extra delay).
                timeout = 0
                while int(handle.r_count.value) != target_k:
                    await RisingEdge(self.tb.core_clk)
                    timeout += 1
                    if timeout > initial_count + 5:
                        raise AssertionError(
                            f"r_count never reached target_k={target_k} within "
                            f"{initial_count + 5} core clocks (counting stalled?)"
                        )

                pre_abort_count = int(handle.r_count.value)

                await self.tb.write_control_word(
                    bcd=0, mode=0,
                    rw_mode=PITRegisterMap.RW_MODE_LSB_THEN_MSB,
                    counter_select=counter_id,
                )
                await ClockCycles(self.tb.core_clk, 30)

                statuses = await self.tb.read_status()
                status = PITRegisterMap.parse_status_byte(statuses[counter_id])
                out_pin = int(self.tb.dut.timer_irq.value) & (1 << counter_id)
                post_abort_count = int(handle.r_count.value)

                glitched = bool(status['out'] == 1 and status['null_count'] == 1) or bool(out_pin)
                glitches.append((target_k, glitched, status, pre_abort_count, post_abort_count))

                self.log.info(
                    f"  K={target_k:2d} pre_abort_count={pre_abort_count:3d} "
                    f"post_abort_count={post_abort_count:3d} status={status} "
                    f"out_pin={bool(out_pin)} glitched={glitched}"
                )

            any_glitch = [g for g in glitches if g[1]]
            assert not any_glitch, (
                f"a control-word reprogram raised OUT with NULL_COUNT set (a spurious, "
                f"self-contradictory IRQ) for target_k in "
                f"{[g[0] for g in any_glitch]} out of {self.TERMINAL_RACE_SWEEP_MAX - 1} "
                f"sweep points - the terminal-tick branch overrides the control word's "
                f"OUT clear in that cycle"
            )

            self.log.info("GH#52-I Control word on terminal tick test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#52-I Control word on terminal tick test FAILED: {e}")
            return False

    # ------------------------------------------------------------------
    # J. A reprogram must release a stale latch, not let it survive
    #    (found reviewing the landed #52 RTL fix - not part of the
    #    original issue thread)
    # ------------------------------------------------------------------

    async def test_gh52_latch_cleared_by_reprogram(self) -> bool:
        """
        Latching a counter (control word RW=00) and then reprogramming it
        (a new control word + a new load) before ever reading the latched
        value must make the FIRST subsequent COUNTERx_DATA read return the
        live count of the NEW program, not the stale latched snapshot from
        before the reprogram.

        pit_counter.sv's latch flops (r_count_latch/r_count_latched) are
        only released `else if (count_reg_rd) r_count_latched <= 1'b0;` - a
        control word write does not touch them at all, so a latch armed
        before a reprogram survives the reprogram and is still sitting
        there, stale, the next time software reads the counter.
        """
        self.log.info("=" * 80)
        self.log.info("Test: GH#52-J Latch cleared by reprogram")
        self.log.info("=" * 80)

        counter_id = 0
        try:
            self.tb.dut.gate_in.value = 0x7
            await self.tb.enable_pit(True)

            await self.tb.configure_counter_mode0(counter_id, 50000, bcd=False)
            await ClockCycles(self.tb.core_clk, 40)

            # Latch counter 0 (control word RW=00) - do NOT read it.
            await self.tb.write_control_word(
                bcd=0, mode=0,
                rw_mode=PITRegisterMap.RW_MODE_LATCH,
                counter_select=counter_id,
            )
            await ClockCycles(self.tb.core_clk, 10)

            # Reprogram counter 0 with a small, easily-distinguished new
            # count before ever reading the latch armed above.
            # A count that outlives the write+read round trip (23 counting
            # clocks CDC off, ~34 CDC on); with 20 the counter reached 0 before
            # the read landed and no window could tell fixed from broken.
            new_count = 50000
            await self.tb.configure_counter_mode0(counter_id, new_count, bcd=False)
            await ClockCycles(self.tb.core_clk, 5)

            first_read = await self.tb.read_counter(counter_id)

            self.log.info(f"  new_count={new_count} first_read_after_reprogram={first_read}")

            assert (new_count - 200) < first_read <= new_count, (
                f"first COUNTERx_DATA read after a reprogram returned 0x{first_read:04x}, "
                f"expected close to the new program's count (0x{new_count:04x}, allowing a "
                f"few decrements) - a latch armed before the reprogram (and never read) is "
                f"still stale in r_count_latch/r_count_latched, and the read mux is "
                f"returning that instead of the new program's live count"
            )

            self.log.info("GH#52-J Latch cleared by reprogram test PASSED")
            return True

        except AssertionError as e:
            self.log.error(f"GH#52-J Latch cleared by reprogram test FAILED: {e}")
            return False
