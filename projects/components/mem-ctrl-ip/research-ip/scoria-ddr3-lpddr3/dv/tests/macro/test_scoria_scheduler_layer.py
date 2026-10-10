# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""First COMPOSED scoria test: the real scheduler, not a FUB with mocks.

Seventeen FUB suites pass. Every one of them mocked its module's neighbours,
and a mocked neighbour cannot disagree with the test author -- it answers
exactly as they believed it would. This file instantiates the real wiring:
arbiter + bank_timers + global_timers + refresh_ctrl + page_policy + zq_ctrl +
init_sequencer + wrlvl_ifc + mode_register + the command FIFO.

That matters because this session's FUB findings were all about boundaries the
unit tests had to model by hand -- the arbiter keeping its own in-flight
precharge record against a stale `bank_row_active`, a readiness flop sampling
current state instead of next, a grant gated on a registered decision rather
than an accepted fire. Each needed the testbench to be right about a
neighbour. Here nobody models them.

Two things make every case in this file carry more than its own assertions:

  * `CMD_HISTORY_EN=1` with the DDR3 windows, so
    `scoria_cmd_history_checker` audits the real issued stream and `$fatal`s on
    any same-bank or cross-bank JEDEC violation. That checker was proved ARMED
    in dv/tests/fub/test_scoria_cmd_history_checker.py -- nine mutations, each
    required to kill the simulation -- so a clean run here is evidence rather
    than silence. `--assert` is in the compile args for the same reason: without
    it verilator discards every immediate assertion and the checker is inert.
  * `tb.unsafe_pushes`, the pumice BUG-003 invariant: no command may be pushed
    to the FIFO while the arbiter's own final safety gate says no. Checked at
    the end of every case, because it holds for every config and traffic
    pattern.

The timing set is derived from the HAS design point by `scoria_dram_configs`
and logged by the TB, so a passing result can say which config produced it.
The HIST_T_* parameters take `spacing` (the required separation), while the
CSR ports take `prog` (spacing - 1, the N+1 convention) -- keeping those apart
is why the config module returns both.
"""

import os
import random

import cocotb
import pytest
import sys
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.scoria_scheduler_layer_tb import (  # noqa: E402
    ScoriaMemCmdSchedulerTB, OP_ACT, OP_RD, OP_WR, OP_PRE, OP_PREA, OP_REF,
    OP_MRS, OP_ZQCS, OP_ZQCL,
)
from tbclasses.scoria_dram_configs import dram_config  # noqa: E402

NUM_BANKS, ROW_WIDTH, COL_WIDTH = 8, 15, 10
_SPACING, _PROG, _META = dram_config()


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_scoria_scheduler_layer(dut):
    tt = os.environ.get("TEST_TYPE", "init_sequence_in_jedec_order")
    tb = ScoriaMemCmdSchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    if tt == "init_sequence_in_jedec_order":
        # HAS verification item 1 asks for the ORDER, "because order is what
        # pumice got wrong on its equivalent": MR2, MR3, MR1, MR0, then ZQCL.
        # The FUB test checks the sequencer alone; this checks it driving the
        # real arbiter, which has to forward init commands verbatim ahead of
        # every other class.
        chk(int(dut.dram_reset_n_o.value) == 0,
            "RESET# is not asserted at the start of init -- JESD79-3F needs it "
            "held low through the power-up wait, and a scoria FUB fix this "
            "session changed it from a 10 ns pulse to a latched level")
        ok = await tb.complete_init()
        chk(ok, f"init never completed. stream: {tb.stream()}")
        mrs = tb.ops_of(OP_MRS)
        chk(len(mrs) >= 4,
            f"{len(mrs)} MRS commands issued during init, expected at least 4 "
            f"(MR2, MR3, MR1, MR0). stream: {tb.stream()}")
        zqcl = tb.ops_of(OP_ZQCL)
        chk(len(zqcl) >= 1,
            f"no ZQCL during init -- DDR3 calibrates its output drivers once "
            f"at power-up and the BIOS cannot do it later. stream: "
            f"{tb.stream()}")
        if mrs and zqcl:
            chk(mrs[-1]['cycle'] < zqcl[0]['cycle'],
                f"ZQCL at cycle {zqcl[0]['cycle']} precedes the last MRS at "
                f"{mrs[-1]['cycle']}; the mode registers must be written "
                f"before calibration")
        chk(int(dut.dram_reset_n_o.value) == 1,
            "RESET# still asserted after init completed")
        tb.log.info(f"init stream: {tb.stream()}")

    elif tt == "act_then_read_with_real_timers":
        # The headline composition check: a pending read, gated by the REAL
        # per-bank timer rather than a vector the test drove itself.
        chk(await tb.complete_init(), "init never completed")
        before = len(tb.cmds)
        tb.rd_entry = dict(slot=0, bank=3, row=0x1234, col=0x40)
        # Wait on the captured STREAM, not on rd_issue_valid_o: the issue
        # strobe leads the command at the sink by CMD_DELAY plus the FIFO, so
        # breaking on it and then reading tb.cmds finds nothing.
        await tb.wait_for_ops(OP_RD, since=before, limit=120)
        await tb.drain()
        new = list(tb.cmds)[before:]
        acts = [c for c in new if c['op'] == OP_ACT]
        rds = [c for c in new if c['op'] == OP_RD]
        chk(acts and rds,
            f"a pending read did not produce ACT then RD. new stream: "
            f"{' '.join(c['name'] + '@' + str(c['cycle']) for c in new)}")
        if acts and rds:
            chk(acts[0]['bank'] == 3 and acts[0]['row'] == 0x1234,
                f"ACT addressed bank {acts[0]['bank']} row "
                f"0x{acts[0]['row']:X}, expected bank 3 row 0x1234")
            chk(rds[0]['bank'] == 3 and rds[0]['col'] == 0x40,
                f"RD addressed bank {rds[0]['bank']} col 0x{rds[0]['col']:X}, "
                f"expected bank 3 col 0x40")
            gap = rds[0]['cycle'] - acts[0]['cycle']
            chk(gap >= _SPACING['tRCD'],
                f"ACT->RD gap {gap} cycles, tRCD needs "
                f"{_SPACING['tRCD']} at this operating point. The bank timer "
                f"is real here, so this is the composed spacing, not a "
                f"mocked one.")
            tb.log.info(f"composed ACT->RD gap {gap} cycles "
                        f"(tRCD spacing {_SPACING['tRCD']})")
        chk(tb.rd_issued == [0],
            f"rd_issue fired {tb.rd_issued}, expected slot 0 exactly once")

    elif tt == "refresh_closes_banks_then_refreshes":
        # Refresh has to precharge an open bank before it can refresh. With the
        # real refresh_ctrl and real timers, that is a sequence rather than a
        # single decision.
        chk(await tb.complete_init(), "init never completed")
        tb.rd_entry = dict(slot=0, bank=2, row=0x55, col=8)
        await tb.wait_for_ops(OP_RD, limit=120)
        await tb.drain()
        before = len(tb.cmds)
        # tREFI is 781 cycles at this point; reload a short interval instead of
        # simulating 7.8 us of nothing, and say so.
        dut.t_refi_i.value = 8
        dut.refi_reload_i.value = 1
        await RisingEdge(dut.aclk)
        dut.refi_reload_i.value = 0
        for _ in range(400):
            await RisingEdge(dut.aclk)
            if [c for c in list(tb.cmds)[before:] if c['op'] == OP_REF]:
                break
        new = list(tb.cmds)[before:]
        refs = [c for c in new if c['op'] == OP_REF]
        pres = [c for c in new if c['op'] in (OP_PRE, OP_PREA)]
        chk(refs, f"no REF issued in 400 cycles with tREFI=8. new stream: "
                  f"{' '.join(c['name'] + '@' + str(c['cycle']) for c in new)}")
        if refs:
            chk(pres and pres[0]['cycle'] < refs[0]['cycle'],
                f"REF at cycle {refs[0]['cycle']} with no preceding precharge "
                f"-- bank 2 was left open, and REFab into an open row is the "
                f"defect the bound history checker exists to catch")
            chk(tb.stat('stat_ref_o') >= 1,
                f"stat_ref is {tb.stat('stat_ref_o')} after a refresh issued")

    elif tt == "zqcs_maintenance_in_traffic":
        # The ZQ arm, composed. The FUB test drove zq_req by hand; here the
        # real zq_ctrl raises it on its interval, against real bank state.
        chk(await tb.complete_init(), "init never completed")
        before = len(tb.cmds)
        dut.zq_enable_i.value = 1
        dut.zq_interval_i.value = 20
        tb.rd_entry = dict(slot=0, bank=5, row=0x77, col=0x10)
        for _ in range(500):
            await RisingEdge(dut.aclk)
            if [c for c in list(tb.cmds)[before:] if c['op'] == OP_ZQCS]:
                break
            if tb.rd_issued and tb.rd_entry is None:
                # keep a little traffic alive so ZQ has to contend with it
                tb.rd_entry = dict(slot=0, bank=5, row=0x77, col=0x10)
        new = list(tb.cmds)[before:]
        zq = [c for c in new if c['op'] == OP_ZQCS]
        chk(zq, f"no ZQCS in 500 cycles with zq_enable and interval 20 -- "
                f"periodic calibration never fired. new stream: "
                f"{' '.join(c['name'] + '@' + str(c['cycle']) for c in new)}")
        if zq:
            # JESD79-3F 3.10: all banks idle at the ZQCS, and no command for
            # tZQCS after it. Both are the arbiter's structure; here they are
            # checked against the real bank state rather than a driven vector.
            after = [c for c in new if c['cycle'] > zq[0]['cycle']]
            quiet = [c for c in after if c['cycle'] - zq[0]['cycle'] <= 16]
            chk(quiet == [],
                f"commands issued inside the tZQCS window after ZQCS@"
                f"{zq[0]['cycle']}: "
                f"{' '.join(c['name'] + '@' + str(c['cycle']) for c in quiet)}")
            chk(tb.stat('zq_total_o') >= 1,
                f"zq_total is {tb.stat('zq_total_o')} after a ZQCS issued")
            tb.log.info(f"ZQCS@{zq[0]['cycle']}, zq_total="
                        f"{tb.stat('zq_total_o')}")

    elif tt == "probe_act_spacing":
        # DISCRIMINATOR. The bound checker watches the SCHEDULER OUTPUT
        # (cmd_valid_o && cmd_ready_i), which is downstream of CMD_DELAY and the
        # command FIFO -- not the arbiter's issue stream. So a tRRD violation
        # there has two possible causes and they need different fixes:
        #   (a) the arbiter issued two ACTs too close  -> pumice BUG-021
        #   (b) the arbiter spaced them and the FIFO/delay path COMPRESSED them
        #       -> the TASK-007 class ("preserves ORDER but not SPACING")
        # tb.pushes carries the arbiter-side cycle of every push, so both
        # spacings can be measured from one run.
        rng = random.Random(int(os.environ.get('SEED', '734')))
        chk(await tb.complete_init(), "init never completed")
        for _ in range(400):
            if tb.rd_entry is None and rng.random() < 0.5:
                tb.rd_entry = dict(slot=0, bank=rng.randrange(NUM_BANKS),
                                   row=rng.randrange(1 << 8),
                                   col=rng.randrange(1 << COL_WIDTH))
            if tb.wr_entry is None and rng.random() < 0.5:
                tb.wr_entry = dict(slot=1, bank=rng.randrange(NUM_BANKS),
                                   row=rng.randrange(1 << 8),
                                   col=rng.randrange(1 << COL_WIDTH))
            await RisingEdge(dut.aclk)
        arb_acts = [p['cycle'] for p in tb.pushes if p['op'] == OP_ACT]
        out_acts = [c['cycle'] for c in tb.cmds if c['op'] == OP_ACT]
        def tight(cs):
            return [(a, b, b - a) for a, b in zip(cs, cs[1:]) if b - a < 2]
        tb.log.info(f"PROBE arbiter ACTs={len(arb_acts)} tight={tight(arb_acts)[:6]}")
        tb.log.info(f"PROBE output  ACTs={len(out_acts)} tight={tight(out_acts)[:6]}")
        tb.log.info(f"PROBE unsafe_pushes={len(tb.unsafe_pushes)}")

    elif tt == "mixed_traffic_audited_by_the_checker":
        # The point of this case is the BOUND CHECKER, not its own assertions:
        # mixed read/write traffic across banks, with the DDR3 windows live, so
        # scoria_cmd_history_checker re-derives JEDEC spacing from what is
        # actually issued. It $fatal's on a violation, so survival is the
        # result -- and it is only meaningful because the checker is proved
        # armed by its own FUB suite.
        rng = random.Random(int(os.environ.get('SEED', '61')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 150, "FUNC": 800, "FULL": 3000}.get(lvl, 800)
        chk(await tb.complete_init(), "init never completed")
        before = len(tb.cmds)
        for _ in range(n):
            if tb.rd_entry is None and rng.random() < 0.5:
                tb.rd_entry = dict(slot=0, bank=rng.randrange(NUM_BANKS),
                                   row=rng.randrange(1 << 8),
                                   col=rng.randrange(1 << COL_WIDTH))
            if tb.wr_entry is None and rng.random() < 0.5:
                tb.wr_entry = dict(slot=1, bank=rng.randrange(NUM_BANKS),
                                   row=rng.randrange(1 << 8),
                                   col=rng.randrange(1 << COL_WIDTH))
            await RisingEdge(dut.aclk)
        new = list(tb.cmds)[before:]
        cols = [c for c in new if c['op'] in (OP_RD, OP_WR)]
        chk(len(cols) > n // 40,
            f"only {len(cols)} column commands in {n} cycles -- the traffic "
            f"never got going, so the checker audited almost nothing and this "
            f"case proves little")
        chk(len(tb.rd_issued) + len(tb.wr_committed) > 0,
            "no CAM entry was ever retired")
        tb.log.info(f"audited {len(new)} commands, {len(cols)} columns, "
                    f"{len(tb.ops_of(OP_ACT))} ACTs, "
                    f"{len(tb.ops_of(OP_REF))} REFs")

    elif tt == "elastic_refresh_in_traffic":
        # Mode A: demand-aware elastic refresh. The threshold is 16 consecutive
        # demand cycles; before that the FUB keeps strict tREFI timing. Use a
        # tREFI shorter than 16 so a tick lands inside the initial window. The
        # request must assert during that sporadic window (strict timing), and
        # the actual REF command must wait until demand has been sustained for
        # 16 cycles. A mis-wired streak=1 would defer the request instead.
        chk(await tb.complete_init(), "init never completed")
        before_cycle = tb.cmds[-1]['cycle'] if tb.cmds else 0
        dut.t_refi_i.value = 12
        dut.refi_reload_i.value = 1
        await RisingEdge(dut.aclk)
        dut.refi_reload_i.value = 0
        dut.ref_elastic_en_i.value = 1
        dut.ref_postpone_i.value = 7
        dut.ref_postpone_demand_streak_i.value = 16
        # Keep both read and write entries alive so demand_i stays high even
        # when one side commits/issues and the CAM model clears it for a cycle.
        tb.rd_entry = dict(slot=0, bank=1, row=0x100, col=0)
        tb.wr_entry = dict(slot=1, bank=2, row=0x101, col=0)
        demand_cycles = 0
        first_req_cycle = None
        for cyc in range(16):
            await RisingEdge(dut.aclk)
            if int(dut.u_refresh.demand_i.value):
                demand_cycles += 1
            if first_req_cycle is None and int(dut.u_refresh.refresh_req_o.value):
                first_req_cycle = cyc + 1
            if tb.rd_entry is None:
                tb.rd_entry = dict(slot=0, bank=1, row=0x100, col=0)
            if tb.wr_entry is None:
                tb.wr_entry = dict(slot=1, bank=2, row=0x101, col=0)
        early_refs = [r for r in tb.ops_of(OP_REF)
                      if before_cycle < r['cycle'] <= before_cycle + 16]
        chk(not early_refs,
            f"REF issued during the first 16 demand cycles (sporadic window): "
            f"{' '.join(f'{r['name']}@{r['cycle']}' for r in early_refs)}")
        # The first tREFI tick lands around cycle 12; strict/sporadic mode must
        # assert the request inside the 16-cycle window. Mis-wired streak=1
        # defers the request until the backlog exceeds the postpone limit.
        chk(first_req_cycle is not None,
            "refresh request never asserted during the 16-cycle sporadic window "
            "-- ref_postpone_demand_streak_i may be mis-wired to 1")
        chk(first_req_cycle <= 18,
            f"refresh request first asserted at cycle {first_req_cycle} of the "
            f"sporadic window, expected <= 18 (tREFI tick + pipeline margin)")
        # Continue sustained demand; the postponed REF command must only appear
        # after the cumulative demand streak has reached 16 cycles.
        req_seen = False
        for _ in range(400):
            await RisingEdge(dut.aclk)
            if int(dut.u_refresh.demand_i.value):
                demand_cycles += 1
            if tb.rd_entry is None:
                tb.rd_entry = dict(slot=0, bank=1, row=0x100, col=0)
            if tb.wr_entry is None:
                tb.wr_entry = dict(slot=1, bank=2, row=0x101, col=0)
            if int(dut.u_refresh.refresh_req_o.value):
                req_seen = True
                break
        chk(req_seen, "refresh request never appeared under elastic traffic")
        chk(demand_cycles >= 16,
            f"refresh request appeared after only {demand_cycles} demand cycles, "
            f"expected >= 16 (sustained-demand threshold)")

    elif tt == "tcr_doubles_rate":
        # Mode B: temperature-compensated refresh. Derate=1 halves tREFI, so
        # the REF count in a fixed window must be at least 1.8x derate=0.
        chk(await tb.complete_init(), "init never completed")

        async def count_refs(derate):
            before = len(tb.ops_of(OP_REF))
            dut.ref_tcr_en_i.value = 1
            dut.ref_trefi_derate_i.value = derate
            dut.t_refi_i.value = 40
            dut.refi_reload_i.value = 1
            await RisingEdge(dut.aclk)
            dut.refi_reload_i.value = 0
            # Light traffic to keep demand present but not block REFs.
            for c in range(2000):
                await RisingEdge(dut.aclk)
                if tb.rd_entry is None and (c % 8) == 0:
                    tb.rd_entry = dict(slot=0, bank=2, row=0x200, col=0)
            return len(tb.ops_of(OP_REF)) - before

        refs_0 = await count_refs(0)
        # Disable TCR and let the counter settle before the second run.
        dut.ref_tcr_en_i.value = 0
        dut.ref_trefi_derate_i.value = 0
        await tb.drain(40)
        refs_1 = await count_refs(1)
        chk(refs_1 * 10 >= refs_0 * 18,
            f"TCR derate=1 produced {refs_1} REFs vs {refs_0} for derate=0, "
            f"expected >= 1.8x")

    elif tt == "zqcs_defer_under_demand":
        # Mode C: ZQCS placement policy. With placement=1 and overdue_max=0,
        # ZQCS must defer while traffic persists, then fire once CAMs drain.
        chk(await tb.complete_init(), "init never completed")
        before = len(tb.cmds)
        before_cycle = tb.cmds[-1]['cycle'] if tb.cmds else 0
        dut.zq_enable_i.value = 1
        dut.zq_interval_i.value = 20
        dut.zq_placement_i.value = 1
        dut.zq_overdue_max_i.value = 0
        # Use both read and write entries so demand_i never drops when one side
        # issues/commits and the CAM model clears it for a cycle.
        tb.rd_entry = dict(slot=0, bank=3, row=0x300, col=0)
        tb.wr_entry = dict(slot=1, bank=4, row=0x301, col=0)
        zq_req_seen = False
        for _ in range(100):
            await RisingEdge(dut.aclk)
            if int(dut.u_zq.zq_req_o.value):
                zq_req_seen = True
                break
            if tb.rd_entry is None:
                tb.rd_entry = dict(slot=0, bank=3, row=0x300, col=0)
            if tb.wr_entry is None:
                tb.wr_entry = dict(slot=1, bank=4, row=0x301, col=0)
        chk(not zq_req_seen,
            "ZQ request asserted during the first 100 cycles of continuous "
            "demand with placement=1, overdue_max=0 -- deferral is not wired")
        early_zq = [z for z in tb.ops_of(OP_ZQCS)
                    if before_cycle < z['cycle'] <= before_cycle + 100]
        chk(not early_zq,
            f"ZQCS issued within first 100 cycles despite continuous demand: "
            f"{' '.join(f'{z['name']}@{z['cycle']}' for z in early_zq)}")
        # Drain CAMs: stop issuing and let the arbiter go idle. The interval
        # already expired during the demand window, so ZQCS should arrive within
        # the bank-idle/precharge grant margin once demand drops.
        tb.rd_entry = None
        tb.wr_entry = None
        post_drain = 0
        zq = None
        for _ in range(80):
            await RisingEdge(dut.aclk)
            post_drain += 1
            hits = [c for c in list(tb.cmds)[before:] if c['op'] == OP_ZQCS]
            if hits:
                zq = hits
                break
        chk(zq, "no ZQCS within 80 cycles after draining CAMs")
        if zq:
            chk(post_drain <= 60,
                f"ZQCS after drain appeared {post_drain} cycles after traffic "
                f"stopped, expected <= 60 (bank-idle/precharge margin = 60)")
        # Rerun with overdue_max=8: the request must cap deferral under load.
        # Let the interval reload naturally after the first ZQCS, then restart
        # traffic and verify the ZQ request asserts within the overdue window.
        before2 = len(tb.cmds)
        dut.zq_overdue_max_i.value = 8
        tb.rd_entry = dict(slot=0, bank=3, row=0x300, col=0)
        tb.wr_entry = dict(slot=1, bank=4, row=0x301, col=0)
        # Wait for the ZQ request to assert (this is the composed Mode C path;
        # the actual ZQCS grant still needs an idle bank window).
        req_seen2 = False
        for cyc2 in range(120):
            await RisingEdge(dut.aclk)
            if int(dut.u_zq.zq_req_o.value):
                req_seen2 = True
                break
            if tb.rd_entry is None:
                tb.rd_entry = dict(slot=0, bank=3, row=0x300, col=0)
            if tb.wr_entry is None:
                tb.wr_entry = dict(slot=1, bank=4, row=0x301, col=0)
        chk(req_seen2,
            "ZQ request never asserted with overdue_max=8 despite demand")
        chk(cyc2 <= 100,
            f"ZQ request with overdue_max=8 asserted at cycle {cyc2}, "
            f"expected <= ~100 (interval + overdue cap + margin)")
        # The actual ZQCS may wait for an idle bank, but it must arrive.
        zq2 = await tb.wait_for_ops(OP_ZQCS, since=before2, limit=200)
        chk(zq2, "no ZQCS within 200 cycles with overdue_max=8 despite demand")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    # ---- invariants that hold for EVERY case -------------------------------
    chk(tb.unsafe_pushes == [],
        f"{len(tb.unsafe_pushes)} command(s) pushed to the FIFO while the "
        f"arbiter's own final safety gate said no (pumice BUG-003): "
        f"{tb.unsafe_pushes[:4]}. The FIFO takes the command, the DRAM "
        f"executes it, and evt_* never strobes -- so the timers and the CAM "
        f"retire never learn it happened.")

    await tb.wait_clocks('aclk', 4)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["init_sequence_in_jedec_order", "act_then_read_with_real_timers"]
_FUNC = _GATE + ["probe_act_spacing", "refresh_closes_banks_then_refreshes",
                 "zqcs_maintenance_in_traffic",
                 "mixed_traffic_audited_by_the_checker",
                 "elastic_refresh_in_traffic",
                 "tcr_doubles_rate",
                 "zqcs_defer_under_demand"]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_scoria_scheduler_layer(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "scoria_scheduler_layer"
    test_name = f"test_scoria_scheduler_layer_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/"
                       "rtl/filelists/macro/scoria_scheduler_layer.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_scoria_scheduler_layer",
        sim_build=sim_build, simulator="verilator",
        # HIST_T_* take the required SPACING, not the programmed value: the
        # checker's rule is "at least T cycles apart", while the CSR ports take
        # spacing - 1. Mixing the two under-spaces every window by one and the
        # audit then passes a design it should have failed.
        parameters={"NUM_BANKS": str(NUM_BANKS), "ROW_WIDTH": str(ROW_WIDTH),
                    "COL_WIDTH": str(COL_WIDTH),
                    # The probe MEASURES the two spacings; the checker would
                    # $fatal before it can print them.
                    "CMD_HISTORY_EN": "0" if test_type.startswith("probe") else "1",
                    "HIST_T_RCD": str(_SPACING['tRCD']),
                    "HIST_T_RP":  str(_SPACING['tRP']),
                    "HIST_T_RAS": str(_SPACING['tRAS']),
                    "HIST_T_RFC": str(_SPACING['tRFC']),
                    "HIST_T_WTR": str(_SPACING['tWTR']),
                    "HIST_T_RTW": str(_SPACING['tWTR']),
                    "HIST_T_RRD": str(_SPACING['tRRD']),
                    "HIST_T_FAW": str(_SPACING['tFAW'])},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "NUM_BANKS": str(NUM_BANKS), "ROW_WIDTH": str(ROW_WIDTH),
                   "COL_WIDTH": str(COL_WIDTH),
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        # --assert is NOT a verilator default; without it the bound history
        # checker's immediate assertions are discarded at compile time and
        # every case above runs with the audit silently switched off.
        compile_args=["+define+USE_ASYNC_RESET", "--assert"],
        keep_files=True, timescale="1ns/1ps")
