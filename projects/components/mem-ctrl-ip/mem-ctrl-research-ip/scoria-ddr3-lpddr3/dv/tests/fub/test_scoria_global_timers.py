# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `scoria_global_timers` -- the controller-wide JEDEC windows.

This is where pumice ISSUE-018 lived: the readiness outputs and the counters are
both registered, and they used to be derived TWICE -- the counter flop sampling
the next state while the readiness flop sampled `r_*_cnt == 0`, the state it was
about to replace. Every gate therefore stayed open for exactly one cycle after
the command that should have closed it, and a board ILA capture caught a tRTW of
20 honoured as 1. scoria inherited the fixed code (one next-state function, two
flops), so the job here is PROVING the fix came across rather than assuming it.

Two things make that proof delicate, and both are baked into the helpers:

1.  SAMPLING. Every output of this module is a flop. Reading one in the same
    delta as the clock edge measures whichever side of the NBA the simulator
    happened to be on. `tick()` steps an edge and then settles 1 ns into the
    cycle, so `cycles_until()` index i is read mid-cycle (i+1) where cycle 0 is
    the cycle the event was asserted in. A window whose enforced spacing is
    N+1 cycles therefore first reads ready at index N -- see the table in
    `cycles_until`.

2.  DIRECTION. `>=` is the wrong comparison. A gate that opens one cycle EARLY
    violates the part; one that opens late only costs bandwidth. So the
    spacing cases assert exact equality, and `*_never_early` separately walks
    every cycle inside the window and requires the gate shut in all of them --
    that second case is what an ISSUE-018 regression trips, because the
    off-by-one lands inside the window rather than at its edge.

Convention under test, from scoria_csr.rdl: "MC cycles to block; spacing
enforced is N+1". Program the JEDEC number; do not pre-subtract.
"""

import os
import random

import cocotb
import pytest
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path


class GtTB(TBBase):
    async def setup(self, *, faw=0, rrd=0, wtr=0, rtw=0, ccd=0):
        await self.start_clock('mc_clk', 10, 'ns')
        d = self.dut
        d.t_faw_i.value = faw
        d.t_rrd_i.value = rrd
        d.t_wtr_global_i.value = wtr
        d.t_rtw_i.value = rtw
        d.t_ccd_i.value = ccd
        for s in ('evt_act_i', 'evt_rd_i', 'evt_wr_i'):
            getattr(d, s).value = 0
        d.evt_act_rank_i.value = 0
        await self.assert_reset()
        await self.wait_clocks('mc_clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('mc_clk', 3)
        await Timer(1, 'ns')

    async def assert_reset(self):
        self.dut.mc_rst_n.value = 0

    async def deassert_reset(self):
        self.dut.mc_rst_n.value = 1

    async def setup_clocks_and_reset(self):
        await self.setup()

    async def tick(self):
        """One clock, then settle inside the following cycle."""
        await RisingEdge(self.dut.mc_clk)
        await Timer(1, 'ns')

    def bit(self, sig, idx=0):
        return (int(getattr(self.dut, sig).value) >> idx) & 1

    async def event(self, name, rank=0):
        """Assert one event for exactly one cycle; return mid-NEXT-cycle.

        Call it back to back to issue events in consecutive cycles -- it leaves
        the clock mid-cycle, which is where the next assignment must happen.
        """
        d = self.dut
        if name == 'evt_act_i':
            d.evt_act_rank_i.value = rank
        getattr(d, name).value = 1
        await self.tick()
        getattr(d, name).value = 0

    async def cycles_until(self, sig, idx=0, limit=400):
        """Index of the first mid-cycle sample where `sig[idx]` reads high.

        Called immediately after `event()`, index 0 is mid-cycle 1 (cycle 0
        being the event's own cycle), so for a window programmed to N:

            spacing enforced   first legal command   returns
            N+1 cycles         cycle N+1             N
            0 (disabled)       cycle 1               0
        """
        for i in range(limit):
            if self.bit(sig, idx):
                return i
            await self.tick()
        return None


# (case name, window kwarg, event signal, readiness output)
_WINDOWS = {
    "trrd":  ("rrd", 'evt_act_i', 'trrd_window_ok_o'),
    "twtr":  ("wtr", 'evt_wr_i',  'twtr_global_ok_o'),
    "trtw":  ("rtw", 'evt_rd_i',  'trtw_window_ok_o'),
    "tccd":  ("ccd", 'evt_rd_i',  'tccd_window_ok_o'),
}


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_scoria_global_timers(dut):
    tt = os.environ.get("TEST_TYPE", "spacing_exact")
    tb = GtTB(dut)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    if tt == "spacing_exact":
        # Each global window in turn, measured rather than bounded.
        for name, (kw, evt, ok) in _WINDOWS.items():
            for n in (1, 4, 9):
                await tb.setup(**{kw: n})
                chk(tb.bit(ok) == 1, f"{name}: gate shut at rest, before any "
                                     f"event -- reset must publish ready")
                await tb.event(evt)
                g = await tb.cycles_until(ok)
                chk(g == n, f"{name}={n}: ready at index {g}, expected {n} "
                            f"(= {n + 1} cycles of command spacing; the RDL "
                            f"says a window programmed to N enforces N+1). "
                            f"An index of {n + 1} here is the ISSUE-018 "
                            f"one-cycle blind spot back again.")

    elif tt == "never_early":
        # The ISSUE-018 signature. The off-by-one is INSIDE the window, so only
        # walking every cycle catches it -- the spacing case above sees the
        # edge, this sees the whole span.
        for name, (kw, evt, ok) in _WINDOWS.items():
            for n in (3, 7):
                await tb.setup(**{kw: n})
                await tb.event(evt)
                for i in range(n):
                    chk(tb.bit(ok) == 0,
                        f"{name}={n}: {ok} high at index {i} -- the window is "
                        f"still closed for {n} more samples. A command issues "
                        f"here and the part sees {i + 1} cycles of spacing "
                        f"instead of {n + 1}.")
                    await tb.tick()
                chk(tb.bit(ok) == 1,
                    f"{name}={n}: {ok} still low at index {n}; the window "
                    f"closed for longer than programmed")

    elif tt == "tfaw_four_acts_then_block":
        # JESD79-3F: at most four ACTs inside tFAW. Four slots, so the fifth
        # must be refused -- and the first four must NOT be.
        n = 20
        await tb.setup(faw=n, rrd=0)
        for k in range(4):
            chk(tb.bit('tfaw_window_ok_o') == 1,
                f"tFAW blocked ACT #{k + 1} of 4 -- four activates per window "
                f"are legal and refusing one costs the rank's whole burst")
            await tb.event('evt_act_i')
        chk(tb.bit('tfaw_window_ok_o') == 0,
            "tFAW still open after 4 ACTs -- a fifth activate inside the "
            "window exceeds the device's four-activate power limit")
        # Reopens when the OLDEST slot expires: ACT #1 was in cycle 0, so the
        # fifth ACT is legal in cycle n+1, and we are sitting mid-cycle 4.
        g = await tb.cycles_until('tfaw_window_ok_o')
        chk(g == n - 3,
            f"tFAW reopened at index {g}, expected {n - 3} -- the window is "
            f"measured from the FIRST of the four activates (cycle 0), so the "
            f"fifth is legal in cycle {n + 1} and we start mid-cycle 4")

    elif tt == "tfaw_slots_are_a_sliding_window":
        # Not a burst-of-four counter: the slots roll. Space four ACTs out, and
        # the fifth must be legal as soon as the first slot expires, not after
        # a fresh window from the fourth.
        n = 12
        await tb.setup(faw=n, rrd=0)
        await tb.event('evt_act_i')                 # cycle 0
        for _ in range(3):
            await tb.tick()
        for _ in range(3):                          # cycles 4, 5, 6
            chk(tb.bit('tfaw_window_ok_o') == 1, "tFAW blocked one of ACTs 2-4")
            await tb.event('evt_act_i')
        chk(tb.bit('tfaw_window_ok_o') == 0, "tFAW open after the 4th ACT")
        g = await tb.cycles_until('tfaw_window_ok_o')
        # ACT#1 in cycle 0 -> slot free for cycle n+1; we sit mid-cycle 7.
        chk(g == n - 6,
            f"tFAW reopened at index {g}, expected {n - 6}. A fixed window "
            f"restarted from the fourth ACT would give {n - 3}; the slots are "
            f"a sliding window and the oldest one governs.")

    elif tt == "turnaround_is_direction_specific":
        # tWTR is closed by a WRITE and tRTW by a READ. Crossing them wires a
        # controller that stalls the wrong direction -- and, worse, leaves the
        # real turnaround unenforced on the shared DQ bus.
        await tb.setup(wtr=6, rtw=6, ccd=0)
        await tb.event('evt_wr_i')
        chk(tb.bit('twtr_global_ok_o') == 0, "a WR did not close tWTR")
        chk(tb.bit('trtw_window_ok_o') == 1,
            "a WR closed tRTW -- tRTW is read-to-write and a write must not "
            "arm it, or every write pays a read turnaround it never owed")
        await tb.setup(wtr=6, rtw=6, ccd=0)
        await tb.event('evt_rd_i')
        chk(tb.bit('trtw_window_ok_o') == 0, "a RD did not close tRTW")
        chk(tb.bit('twtr_global_ok_o') == 1, "a RD closed tWTR")

    elif tt == "tccd_takes_either_column":
        # tCCD paces columns regardless of direction: both RD and WR reload it.
        for evt in ('evt_rd_i', 'evt_wr_i'):
            await tb.setup(ccd=5)
            await tb.event(evt)
            g = await tb.cycles_until('tccd_window_ok_o')
            chk(g == 5, f"{evt}: tCCD ready at index {g}, expected 5 -- tCCD "
                        f"is CAS-to-CAS and both column commands occupy the "
                        f"same DQ bus")

    elif tt == "zero_disables_every_window":
        # The OFF state needs its own case: a window programmed to 0 must not
        # block at all, including on the very cycle its event fires. Software
        # uses 0 to retire a constraint the part does not have.
        await tb.setup(faw=0, rrd=0, wtr=0, rtw=0, ccd=0)
        for _ in range(6):
            dut.evt_act_i.value = 1
            dut.evt_rd_i.value = 1
            dut.evt_wr_i.value = 1
            await tb.tick()
            for ok in ('tfaw_window_ok_o', 'trrd_window_ok_o',
                       'twtr_global_ok_o', 'trtw_window_ok_o',
                       'tccd_window_ok_o'):
                chk(tb.bit(ok) == 1,
                    f"{ok} low with its window programmed to 0 -- a disabled "
                    f"constraint that still stalls cannot be retired by "
                    f"software")
        dut.evt_act_i.value = 0
        dut.evt_rd_i.value = 0
        dut.evt_wr_i.value = 0

    elif tt == "per_rank_independence":
        # REQUIRES NUM_RANKS=2. tFAW and tRRD are device-local limits, so an
        # ACT on rank 0 must leave rank 1 free; sharing them would halve
        # multi-rank activate bandwidth for no JEDEC reason.
        await tb.setup(faw=20, rrd=8)
        await tb.event('evt_act_i', rank=0)
        chk(tb.bit('trrd_window_ok_o', 0) == 0, "rank 0 tRRD open after its ACT")
        chk(tb.bit('trrd_window_ok_o', 1) == 1,
            "an ACT on rank 0 closed rank 1's tRRD -- tRRD is a per-device "
            "window and ranks are separate devices")
        for _ in range(4):
            await tb.event('evt_act_i', rank=1)
            await tb.tick()
        chk(tb.bit('tfaw_window_ok_o', 1) == 0,
            "rank 1 tFAW open after 4 ACTs on rank 1")
        chk(tb.bit('tfaw_window_ok_o', 0) == 1,
            "rank 1's four activates closed rank 0's tFAW -- the windows are "
            "per rank")
        # And the global DQ windows are NOT per rank: one shared bus.
        await tb.setup(faw=20, rrd=8, ccd=4)
        await tb.event('evt_rd_i')
        chk(tb.bit('tccd_window_ok_o') == 0,
            "tCCD open after a read -- the DQ bus is shared across ranks and "
            "tCCD must be global")

    elif tt == "obs_tracks_the_counters":
        # The obs_* flags are the board's only view of these timers (ILA and
        # the STALL_* CSRs). A flag that does not follow its counter turns a
        # capture into fiction -- which is how ISSUE-018 stayed hidden.
        await tb.setup(rrd=6, wtr=6, rtw=6, ccd=6, faw=6)
        for o in ('obs_trrd_nz_o', 'obs_twtr_nz_o', 'obs_trtw_nz_o',
                  'obs_tccd_nz_o', 'obs_faw_nz_o'):
            chk(tb.bit(o) == 0, f"{o} set at rest with every counter at 0")
        await tb.event('evt_act_i')
        chk(tb.bit('obs_trrd_nz_o') == 1, "obs_trrd_nz clear inside tRRD")
        # obs_faw_nz_o is NOT a counter-non-zero flag despite the name and the
        # module header: it is `!w_tfaw_ok`, i.e. NO SLOT FREE. One ACT loads
        # one of four slots and the rank is still three activates from its
        # limit, so the flag must stay clear -- asserting it here reads the
        # header rather than the RTL, and it is the RTL that drives STALL_TFAW.
        chk(tb.bit('obs_faw_nz_o') == 0,
            "obs_faw_nz set after ONE activate -- it reports the window FULL "
            "(no free slot), so a single ACT of the four legal ones must not "
            "raise it or STALL_TFAW attributes stalls that never happened")
        for _ in range(3):
            await tb.event('evt_act_i')
        chk(tb.bit('obs_faw_nz_o') == 1,
            "obs_faw_nz clear after four activates -- every slot is loaded "
            "and the next ACT really is tFAW-blocked")
        await tb.event('evt_wr_i')
        chk(tb.bit('obs_twtr_nz_o') == 1, "obs_twtr_nz clear inside tWTR")
        chk(tb.bit('obs_tccd_nz_o') == 1, "obs_tccd_nz clear inside tCCD")
        await tb.event('evt_rd_i')
        chk(tb.bit('obs_trtw_nz_o') == 1, "obs_trtw_nz clear inside tRTW")
        # All drain.
        for _ in range(12):
            await tb.tick()
        for o in ('obs_trrd_nz_o', 'obs_twtr_nz_o', 'obs_trtw_nz_o',
                  'obs_tccd_nz_o', 'obs_faw_nz_o'):
            chk(tb.bit(o) == 0, f"{o} still set long after every window closed")

    elif tt == "random_soak":
        # Follow the timers' own advice and check JEDEC in Python: issuing only
        # what the outputs permit must never produce an illegal spacing.
        rng = random.Random(int(os.environ.get('SEED', '17')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 200, "FUNC": 800, "FULL": 3000}.get(lvl, 800)
        RRD, FAW, WTR, RTW, CCD = 4, 16, 5, 6, 3
        await tb.setup(rrd=RRD, faw=FAW, wtr=WTR, rtw=RTW, ccd=CCD)
        acts, last_wr, last_rd, last_col = [], None, None, None
        for cyc in range(n):
            do_act = tb.bit('trrd_window_ok_o') and tb.bit('tfaw_window_ok_o') \
                and rng.random() < 0.35
            col_ok = tb.bit('tccd_window_ok_o')
            do_rd = (not do_act) and col_ok and tb.bit('twtr_global_ok_o') \
                and rng.random() < 0.35
            do_wr = (not do_act) and (not do_rd) and col_ok \
                and tb.bit('trtw_window_ok_o') and rng.random() < 0.35
            if do_act:
                if acts:
                    chk(cyc - acts[-1] >= RRD + 1,
                        f"ACT at {cyc} is {cyc - acts[-1]} cycles after the "
                        f"previous one; tRRD={RRD} requires {RRD + 1}")
                recent = [a for a in acts if cyc - a <= FAW]
                chk(len(recent) < 4,
                    f"ACT at {cyc} is the {len(recent) + 1}th inside a "
                    f"tFAW={FAW} window (prior: {recent}) -- JESD79-3F allows "
                    f"four")
                acts.append(cyc)
            if do_rd and last_wr is not None:
                chk(cyc - last_wr >= WTR + 1,
                    f"RD at {cyc} is {cyc - last_wr} cycles after a WR; "
                    f"tWTR={WTR} requires {WTR + 1}")
            if do_wr and last_rd is not None:
                chk(cyc - last_rd >= RTW + 1,
                    f"WR at {cyc} is {cyc - last_rd} cycles after a RD; "
                    f"tRTW={RTW} requires {RTW + 1}")
            if (do_rd or do_wr) and last_col is not None:
                chk(cyc - last_col >= CCD + 1,
                    f"column at {cyc} is {cyc - last_col} cycles after the "
                    f"previous one; tCCD={CCD} requires {CCD + 1}")
            dut.evt_act_i.value = 1 if do_act else 0
            dut.evt_rd_i.value = 1 if do_rd else 0
            dut.evt_wr_i.value = 1 if do_wr else 0
            if do_rd:
                last_rd = cyc
            if do_wr:
                last_wr = cyc
            if do_rd or do_wr:
                last_col = cyc
            await tb.tick()
        dut.evt_act_i.value = 0
        dut.evt_rd_i.value = 0
        dut.evt_wr_i.value = 0
        chk(len(acts) > n // 20,
            f"only {len(acts)} activates in {n} cycles -- the soak never got "
            f"going, so it proved nothing about the windows")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('mc_clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["spacing_exact", "never_early", "tfaw_four_acts_then_block"]
_FUNC = _GATE + ["tfaw_slots_are_a_sliding_window",
                 "turnaround_is_direction_specific",
                 "tccd_takes_either_column", "zero_disables_every_window",
                 "per_rank_independence", "obs_tracks_the_counters",
                 "random_soak"]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_scoria_global_timers(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "scoria_global_timers"
    test_name = f"test_scoria_global_timers_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/"
                       "rtl/filelists/fub/scoria_global_timers.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_scoria_global_timers",
        sim_build=sim_build, simulator="verilator",
        parameters={"NUM_RANKS": "2"} if test_type == "per_rank_independence"
                   else {},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
