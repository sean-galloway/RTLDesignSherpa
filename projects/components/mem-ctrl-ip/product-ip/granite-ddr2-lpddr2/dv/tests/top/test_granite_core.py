# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
End-to-end smoke for `granite_core` (the storage-lite product controller).

Cloned from research-ip/pumice-ddr2-lpddr2/dv/tests/top/test_pumice_core.py —
same DFI-domain memory model, same AXI BFM, same board clock parity. The
ONLY differences are the DUT, its filelist, and its parameter set (no
N_SRAM_PORTS knob; NUM_ENTRIES defaults to GRANITE_SEAM_N=1).

Why this test exists: the A7 bring-up (FINDINGS_granite_bringup_2026-10-11.md)
showed init_done=1 then a silent read hang. Lint and every fub sim were green
because none of them closes the read-return contract through the entry store.
This test is the missing reproduction: one AXI write burst + one read burst
against a DFI model, with signal probes dumped on either phase's timeout so
the stall boundary is visible in the log.
"""

import os
import sys
import random
from collections import deque

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, SimTimeoutError, with_timeout
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

_FILELIST = ("projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/"
             "rtl/filelists/top/granite.f")

# dv/ on sys.path so `tbclasses.*` resolves; import AFTER the insert.
# granite has no tbclasses of its own yet -- the BFM is the pumice one, shared
# verbatim (it binds generic s_axi_* ports, nothing pumice-specific).
_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)
_PUMICE_DV = os.path.abspath(os.path.join(
    os.path.dirname(__file__), "..", "..", "..", "..", "..",
    "research-ip", "pumice-ddr2-lpddr2", "dv"))
if _PUMICE_DV not in sys.path:
    sys.path.insert(0, _PUMICE_DV)

from tbclasses.pumice_axi_bfm import PumiceAxiBfm      # noqa: E402
from tbclasses.pumice_levels import depth as _profile_depth  # noqa: E402

from tbclasses.pumice_top_csr_tb import board_clock_periods  # noqa: E402
_ACLK_NS, _DFI_NS = board_clock_periods()   # BOARD parity, not literals

DFI_RATE, DRAM_BEAT = 2, 64
DW = DRAM_BEAT * DFI_RATE          # 128 (host AXI = DFI word)
SW = DW // 8
BL = 8
BL_WORDS = BL // DFI_RATE          # 4  (host AXI burst beats)
BURST_INCR = 1

_PHASE_TIMEOUT_US = 200


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_granite_core(dut):
    cocotb.start_soon(Clock(dut.aclk, _ACLK_NS, units='ns').start())
    cocotb.start_soon(Clock(dut.dfi_clk, _DFI_NS, units='ns').start())
    _idle(dut)
    dut.aresetn.value = 0
    dut.dfi_rstn.value = 0
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    dut.dfi_rstn.value = 1
    for _ in range(6):
        await RisingEdge(dut.aclk)

    bfm = _init_masters(dut)

    captured = []
    cocotb.start_soon(_dfi_model(dut, captured))

    # wait for init to complete
    for _ in range(400):
        await RisingEdge(dut.aclk)
        if int(dut.init_done_o.value):
            break
    assert int(dut.init_done_o.value) == 1, "init never completed"

    rng = random.Random(int(os.environ.get("SEED", "1")))
    roundtrips = _profile_depth('core_roundtrips')
    dut._log.info("depth: TEST_LEVEL=%s core_roundtrips=%d",
                  os.environ.get("TEST_LEVEL", "gate"), roundtrips)
    for rnd in range(roundtrips):
        data = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
        addr = 0x2000 + rnd * 0x1000
        captured.clear()

        # ---- AXI write burst, then read the same address back ----
        mon = cocotb.start_soon(_cmd_monitor(dut))
        try:
            await with_timeout(bfm.write(addr, data, wid=1), _PHASE_TIMEOUT_US, "us")
        except SimTimeoutError:
            mon.kill()
            await _dump_probes(dut, "WRITE")
            raise AssertionError(f"round {rnd}: AXI write never returned B")
        mon.kill()

        if len(captured) < BL_WORDS:
            # B fires when the entry store's staging FIFO drains into the DFI
            # plane's wd FIFO -- the WR command itself lands CMD_DELAY cycles
            # later, behind whatever maintenance the scheduler is draining.
            # Poll the DFI bus for the burst instead of sampling the same
            # delta cycle (which fails on a healthy design).
            async def _wait_wrdma():
                while len(captured) < BL_WORDS:
                    await RisingEdge(dut.dfi_clk)
            try:
                await with_timeout(_wait_wrdma(), _PHASE_TIMEOUT_US, "us")
            except SimTimeoutError:
                await _dump_probes(dut, "WRITE-NODATA")
                raise AssertionError(
                    f"round {rnd}: only {len(captured)} words hit the DFI write bus")

        assert len(captured) >= BL_WORDS, \
            (f"round {rnd}: only {len(captured)} words hit the DFI write bus; "
             f"entry wr state / cmd activity dumped above")
        assert captured[:BL_WORDS] == data, \
            f"round {rnd}: DFI write burst {[hex(x) for x in captured[:BL_WORDS]]} != {[hex(x) for x in data]}"

        trace = []
        dut._rd_trace = trace
        tracer = cocotb.start_soon(_rd_pin_tracer(dut, trace))
        try:
            rd = await with_timeout(bfm.read(addr, rid=1), _PHASE_TIMEOUT_US, "us")
        except SimTimeoutError:
            tracer.kill()
            for rec in trace[:80]:
                dut._log.info("RDTRACE %s", rec)
            await _dump_probes(dut, "READ")
            raise AssertionError(f"round {rnd}: AXI read never returned R data")
        tracer.kill()

        if rd[:BL_WORDS] != data:
            # replay the captured DFI return window
            for rec in getattr(dut, "_rd_trace", [])[:80]:
                dut._log.info("RDTRACE %s", rec)
            await _dump_probes(dut, "READ-BADDATA")
        assert rd[:BL_WORDS] == data, \
            f"round {rnd}: AXI read-back {[hex(x) for x in rd[:BL_WORDS]]} != {[hex(x) for x in data]}"
    dut._log.info("PASS: init done; AXI write burst -> DFI -> read burst back == written data, x%d",
                  roundtrips)


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_granite_core_narrow(dut):
    """Narrow AXI beats (granite TASK-007), one AxSIZE per cell. One DRAM burst
    (BL_WORDS words) is written as (BL_WORDS * SW) >> AxSIZE narrow INCR beats,
    back to back: the DFI write bus must carry the packed words, exactly
    BL_WORDS of them (one burst, not one per beat). The burst is then read back
    as the same narrow beats: every beat must carry its bytes in the lanes its
    address selects. Before mc_axi4_narrow_pack the chopper stepped each
    narrow beat by a full word, so beat 1 onwards wrote and read the wrong
    words."""
    size = int(os.environ.get("NARROW_SIZE", "3"))
    nb = 1 << size
    cocotb.start_soon(Clock(dut.aclk, _ACLK_NS, units='ns').start())
    cocotb.start_soon(Clock(dut.dfi_clk, _DFI_NS, units='ns').start())
    _idle(dut)
    dut.aresetn.value = 0
    dut.dfi_rstn.value = 0
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    dut.dfi_rstn.value = 1
    for _ in range(6):
        await RisingEdge(dut.aclk)
    bfm = _init_masters(dut)
    captured = []
    cocotb.start_soon(_dfi_model(dut, captured))
    for _ in range(400):
        await RisingEdge(dut.aclk)
        if int(dut.init_done_o.value):
            break
    assert int(dut.init_done_o.value) == 1, "init never completed"

    rng = random.Random(int(os.environ.get("SEED", "1")))
    addr = 0x3000
    nbeats = (BL_WORDS * SW) // nb
    data = [rng.getrandbits(8 * nb) for _ in range(nbeats)]
    line = b"".join(d.to_bytes(nb, "little") for d in data)
    words = [int.from_bytes(line[k * SW:(k + 1) * SW], "little") for k in range(BL_WORDS)]

    await with_timeout(bfm.wr.write_transaction(addr, data, burst_len=nbeats, id=1, size=size),
                       _PHASE_TIMEOUT_US, "us")

    async def _wait_wrdata():
        while len(captured) < BL_WORDS:
            await RisingEdge(dut.dfi_clk)
    await with_timeout(_wait_wrdata(), _PHASE_TIMEOUT_US, "us")
    for _ in range(40):
        await RisingEdge(dut.dfi_clk)
    assert len(captured) == BL_WORDS, \
        f"AxSIZE {size}: {len(captured)} words on the DFI write bus for one burst, expected {BL_WORDS}"
    assert captured == words, \
        (f"AxSIZE {size}: DFI write words {[hex(x) for x in captured]} != packed "
         f"{[hex(x) for x in words]}")

    rd = await with_timeout(bfm.rd.read_transaction(addr, burst_len=nbeats, id=1, size=size),
                            _PHASE_TIMEOUT_US, "us")
    assert len(rd) == nbeats, f"AxSIZE {size}: {len(rd)} R beats, expected {nbeats}"
    bad = [i for i in range(nbeats)
           if ((rd[i] >> (8 * ((i * nb) % SW))) & ((1 << (8 * nb)) - 1)) != data[i]]
    assert not bad, (f"AxSIZE {size}: {len(bad)} of {nbeats} narrow read beats wrong, "
                     f"first at beat {bad[0]}")
    dut._log.info("PASS narrow: AxSIZE %d, %d beats -> %d DFI words -> %d beats read back",
                  size, nbeats, len(captured), nbeats)


async def _cmd_monitor(dut):
    """Count command-stream fires by op while a phase runs. Killed by the caller
    when the phase ends; results are read by _dump_probes via dut._cmd_log."""
    log = {"fires": {}, "schv_cycles": 0, "cycles": 0}
    dut._cmd_log = log
    prev_v = 0
    while True:
        await RisingEdge(dut.aclk)
        log["cycles"] += 1
        try:
            v = int(dut.w_cmd_v.value) and int(dut.w_cmd_rdy.value)
            if v and not prev_v:
                op = int(dut.w_cmd_op.value)
                log["fires"][op] = log["fires"].get(op, 0) + 1
            prev_v = v
            if int(dut.w_wr_sch_v.value) & 1:
                log["schv_cycles"] += 1
        except Exception:
            pass


async def _rd_pin_tracer(dut, trace, max_cyc=400):
    """Record the DFI read-return window, one row per dfi_clk edge."""
    for _ in range(max_cyc):
        await RisingEdge(dut.dfi_clk)
        try:
            trace.append({
                "en":   int(dut.dfi_rddata_en_o.value),
                "vld":  int(dut.dfi_rddata_valid_i.value),
                "data": int(dut.dfi_rddata_i.value) & 0xffffffff,
                "ret_v": int(dut.w_ret_v.value),
                "ret_r": int(dut.w_ret_rdy.value),
            })
        except Exception:
            pass


async def _dump_probes(dut, phase):
    """Sample the write/read-path seams for a few cycles so the log shows WHERE the
    stall lives. Every probe is guarded -- Verilator may optimize an internal
    net; a missing probe must not hide the ones that survive."""
    cmd_log = getattr(dut, "_cmd_log", None)
    if cmd_log is not None:
        dut._log.info("HANG[%s] cmd_log: %s", phase, cmd_log)
    for _ in range(8):
        await RisingEdge(dut.aclk)
        snap = {}
        for s in ("ar_push_valid", "ar_push_ready", "rt_alloc_ready",
                  "rd_iss_valid", "rd_iss_ready",
                  "w_rd_issue_v", "w_rd_issue_rdy",
                  "w_wr_commit_v", "w_wr_commit_rdy",
                  "aw_push_valid", "aw_push_ready",
                  "w_ret_v", "w_ret_rdy", "w_cmd_v", "w_cmd_rdy"):
            try:
                snap[s] = int(getattr(dut, s).value)
            except Exception:
                snap[s] = None
        for s in ("r_wr_valid", "r_wr_fdone", "r_wr_sched",
                  "r_rd_valid", "r_rd_issued"):
            try:
                snap[f"entry.{s}"] = int(getattr(dut.u_entry_store, s).value)
            except Exception:
                snap[f"entry.{s}"] = None
        # DFI pin + return-path activity: how many rddata windows, how many
        # valid words actually reached the ring, what drained.
        pins = {"en": 0, "valid": 0}
        for _ in range(64):
            await RisingEdge(dut.dfi_clk)
            try:
                if int(dut.dfi_rddata_en_o.value) != 0:
                    pins["en"] += 1
                if int(dut.dfi_rddata_valid_i.value) != 0:
                    pins["valid"] += 1
            except Exception:
                pass
        snap["dfi_pins_64cyc"] = pins
        for s in ("stall_noreq_o", "stall_banktimer_o", "stall_refresh_o",
                  "stall_bp_o", "stall_turnaround_o"):
            try:
                snap[f"sched.{s}"] = int(getattr(dut.u_sched_plane, s).value)
            except Exception:
                snap[f"sched.{s}"] = None
        try:
            snap["ring.occ"] = int(dut.u_axi_plane.u_rd_ring.r_occ.value)
        except Exception:
            snap["ring.occ"] = None
        dut._log.info("HANG[%s] %s", phase, snap)


def _idle(dut):
    dut.memtype_i.value = 0
    dut.page_policy_i.value = 0          # OPEN
    dut.bank_lsb_i.value  = 10   # ROW_MAJOR
    dut.hash_en_i.value   = 0
    dut.hash_seed_i.value = 0
    for t, v in [("t_rcd_i", 2), ("t_rp_i", 2), ("t_ras_i", 3), ("t_rc_i", 4),
                 ("t_wr_i", 2), ("t_rtp_i", 2), ("t_faw_i", 4), ("t_rrd_i", 1),
                 ("t_wtr_i", 1), ("t_rtw_i", 1), ("t_ccd_i", 1)]:
        getattr(dut, t).value = v
    dut.t_refi_i.value = 0x7FFF
    dut.t_rfc_i.value = 8
    dut.refresh_burst_i.value = 1
    for t in ("t_init_wait_i", "t_dll_wait_i"):
        getattr(dut, t).value = 0
    for t in ("t_mrd_wait_i", "t_rp_wait_i", "t_rfc_wait_i"):
        getattr(dut, t).value = 0
    dut.rd_phase_i.value = 0
    dut.wr_phase_i.value = 0
    dut.t_phy_wrlat_i.value = 1
    dut.t_rddata_en_i.value = 1
    dut.dfi_rddata_i.value = 0
    dut.dfi_rddata_valid_i.value = 0
    dut.dfi_init_complete_i.value = 0


async def _dfi_model(dut, cap):
    """DFI-domain model: finish init, capture writes, serve reads.

    One rddata_en window == one DRAM burst == BL_WORDS words, served in write
    order after a 3-cycle gap. Strict per-edge signal discipline: each signal
    is assigned exactly once per dfi_clk edge, so valid never glitches mid-
    burst (the previous coroutine form raced the clock and corrupted a beat)."""
    chunks = 0
    in_window = False
    rd_q = deque()
    state = "idle"
    gap_left = 0
    beat_left = 0
    while True:
        await RisingEdge(dut.dfi_clk)
        if int(dut.dfi_init_start_o.value):
            dut.dfi_init_complete_i.value = 1
        if int(dut.dfi_wrdata_en_o.value) != 0:
            cap.append(int(dut.dfi_wrdata_o.value))
        # A read's rddata_en window spans several dfi cycles (BL8 over rate 2
        # = 4); the whole window is ONE request. Count only the rising edge.
        if int(dut.dfi_rddata_en_o.value) != 0:
            if not in_window:
                chunks += 1
                in_window = True
        else:
            in_window = False
        if state == "idle":
            if chunks > 0 and not rd_q and cap:
                # Refill once at the FIRST window after the write (cap is
                # complete by then); later windows of the same read set drain
                # rd_q in order. Re-snapshotting per window would replay word
                # 0 for every read.
                rd_q = deque(cap)
            if chunks > 0 and rd_q:
                chunks -= 1
                state = "gap"
                gap_left = 2
            dut.dfi_rddata_valid_i.value = 0
        elif state == "gap":
            gap_left -= 1
            if gap_left == 0:
                state = "data"
                beat_left = min(BL_WORDS, len(rd_q))
            dut.dfi_rddata_valid_i.value = 0
        else:
            dut.dfi_rddata_i.value = rd_q.popleft()
            dut.dfi_rddata_valid_i.value = (1 << DFI_RATE) - 1
            beat_left -= 1
            if beat_left == 0:
                state = "idle"


def _init_masters(dut):
    """AXI4 master BFMs on s_axi -- the ONLY thing that drives that port."""
    return PumiceAxiBfm(dut, data_width=DW, bl_words=BL_WORDS)


@cocotb.test(timeout_time=20000, timeout_unit="us")
async def cocotb_test_granite_core_merge(dut):
    """Store combining (TASK-006). Two writes to one burst address from one id
    arrive back-to-back: with STORE_MERGE_EN=1 the second merges into the
    first's entry (ONE burst reaches the DFI write bus, carrying the second
    write's bytes) and both get a B; two back-to-back reads of that address
    take ONE DRAM read (the second is a shadow ticket) and both return it.
    The same pairs from two DIFFERENT ids never combine (owner's rule,
    2026-11-03): two bursts and two DRAM reads, both states, counters unmoved.
    One id (a stream): a pair merges while an OLDER same-id write is still in
    flight, and does not when a same-id write arrived between its halves (the
    merged B would overtake it).
    With STORE_MERGE_EN=0 (the parameter's OFF state) the same traffic takes
    two bursts each way and the counters stay 0: the test asserts the exact
    count for whichever state it was built with, so it fails if the knob is
    inert either way."""
    merge_en = int(os.environ.get("STORE_MERGE_EN", "0"))
    cocotb.start_soon(Clock(dut.aclk, _ACLK_NS, units='ns').start())
    cocotb.start_soon(Clock(dut.dfi_clk, _DFI_NS, units='ns').start())
    _idle(dut)
    dut.aresetn.value = 0
    dut.dfi_rstn.value = 0
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    dut.dfi_rstn.value = 1
    for _ in range(6):
        await RisingEdge(dut.aclk)
    bfm = _init_masters(dut)
    captured = []
    cocotb.start_soon(_dfi_model(dut, captured))
    for _ in range(400):
        await RisingEdge(dut.aclk)
        if int(dut.init_done_o.value):
            break
    assert int(dut.init_done_o.value) == 1, "init never completed"

    rng = random.Random(int(os.environ.get("SEED", "1")))
    addr = 0x4000
    d1 = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
    d2 = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
    captured.clear()

    # ---- two writes, same burst, same id, back-to-back (engine runner) ----
    await with_timeout(bfm.write_many([(addr, d1), (addr, d2)], axid_fn=lambda k: 1),
                       _PHASE_TIMEOUT_US, "us")
    for _ in range(200):          # let the merged burst drain to the DFI bus
        await RisingEdge(dut.dfi_clk)
        if len(captured) >= (BL_WORDS if merge_en else 2 * BL_WORDS):
            break
    wr_merges = int(dut.stat_wr_merge_o.value)
    dut._log.info("merge test: STORE_MERGE_EN=%d write merges=%d dfi words=%d",
                  merge_en, wr_merges, len(captured))
    if merge_en:
        assert wr_merges == 1, f"expected one write merge, counted {wr_merges}"
        assert len(captured) == BL_WORDS, \
            f"a merged pair must reach the DFI bus as ONE burst, saw {len(captured)} words"
        assert captured[:BL_WORDS] == d2, "the merged burst must carry the second write's bytes"
    else:
        assert wr_merges == 0, f"STORE_MERGE_EN=0 must not merge, counted {wr_merges}"
        assert len(captured) == 2 * BL_WORDS, \
            f"without combining both writes reach the DFI bus, saw {len(captured)} words"
        assert captured[:BL_WORDS] == d1 and captured[BL_WORDS:2 * BL_WORDS] == d2

    # ---- two reads, same burst, same id, back-to-back ----
    # The model serves reads from its captured write bursts in order; the
    # expected data is whichever burst(s) reached the bus above.
    rds = await with_timeout(bfm.read_many([addr, addr], axid_fn=lambda k: 1),
                             _PHASE_TIMEOUT_US, "us")
    rd_merges = int(dut.stat_rd_merge_o.value)
    dut._log.info("merge test: read merges=%d returns=%s", rd_merges,
                  [[hex(x) for x in beats[:2]] for _, beats in rds])
    assert len(rds) == 2, f"both reads must return, got {len(rds)}"
    if merge_en:
        assert rd_merges == 1, f"expected one read merge, counted {rd_merges}"
        assert rds[0][1][:BL_WORDS] == d2 and rds[1][1][:BL_WORDS] == d2, \
            "both reads must return the one merged burst"
    else:
        assert rd_merges == 0, f"STORE_MERGE_EN=0 must not merge reads, counted {rd_merges}"
        assert rds[0][1][:BL_WORDS] == d1 and rds[1][1][:BL_WORDS] == d2, \
            "without combining the two reads serve the two bursts in write order"
    # ---- the same pairs from two different ids: never combined ----------
    # rd_q drained above, so the model's next reads serve these two bursts.
    d3 = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
    d4 = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
    captured.clear()
    await with_timeout(bfm.write_many([(addr, d3), (addr, d4)], axid_fn=lambda k: 1 + k),
                       _PHASE_TIMEOUT_US, "us")
    for _ in range(200):
        await RisingEdge(dut.dfi_clk)
        if len(captured) >= 2 * BL_WORDS:
            break
    assert int(dut.stat_wr_merge_o.value) == wr_merges, \
        f"writes from two ids merged (count {wr_merges} -> {int(dut.stat_wr_merge_o.value)})"
    assert len(captured) == 2 * BL_WORDS and captured[:BL_WORDS] == d3 \
        and captured[BL_WORDS:2 * BL_WORDS] == d4, \
        f"two ids must reach the DFI bus as two bursts in order, saw {len(captured)} words"
    rds = await with_timeout(bfm.read_many([addr, addr], axid_fn=lambda k: 1 + k),
                             _PHASE_TIMEOUT_US, "us")
    assert int(dut.stat_rd_merge_o.value) == rd_merges, \
        f"reads from two ids merged (count {rd_merges} -> {int(dut.stat_rd_merge_o.value)})"
    # two ids may complete in either order; each must see its own DRAM read
    assert len(rds) == 2 and sorted(tuple(b[:BL_WORDS]) for _, b in rds) == sorted([tuple(d3), tuple(d4)]), \
        "two ids must take two DRAM reads"

    # ---- one id, an older same-id write in flight: the pair still merges ---
    burst_bytes = BL_WORDS * (DW // 8)
    ax, ay = addr + 2 * burst_bytes, addr + 3 * burst_bytes
    e0, ea, eb = ([rng.randrange(1 << DW) for _ in range(BL_WORDS)] for _ in range(3))
    async def one_id_writes(reqs, want_bursts):
        captured.clear()
        await with_timeout(bfm.write_many(reqs, axid_fn=lambda k: 3), _PHASE_TIMEOUT_US, "us")
        for _ in range(400):
            await RisingEdge(dut.dfi_clk)
            if len(captured) >= len(want_bursts) * BL_WORDS:
                break
        for _ in range(50):
            await RisingEdge(dut.dfi_clk)
        got = sorted(tuple(captured[i:i + BL_WORDS]) for i in range(0, len(captured), BL_WORDS))
        assert got == sorted(tuple(b) for b in want_bursts), \
            f"one-id writes: expected {len(want_bursts)} bursts, saw {len(captured) // BL_WORDS}"
    m0 = int(dut.stat_wr_merge_o.value)
    await one_id_writes([(ax, e0), (ay, ea), (ay, eb)],
                        [e0, eb] if merge_en else [e0, ea, eb])
    m1 = int(dut.stat_wr_merge_o.value)
    assert m1 - m0 == (1 if merge_en else 0), \
        f"one id, older write in flight: expected {1 if merge_en else 0} merge, counted {m1 - m0}"
    # ---- one id, a younger same-id write between the halves: no merge ------
    ax2, ay2 = addr + 4 * burst_bytes, addr + 5 * burst_bytes
    f1, fc, fd = ([rng.randrange(1 << DW) for _ in range(BL_WORDS)] for _ in range(3))
    await one_id_writes([(ay2, fc), (ax2, f1), (ay2, fd)], [fc, f1, fd])
    m2 = int(dut.stat_wr_merge_o.value)
    assert m2 == m1, f"a same-id write between the halves must block the merge (count {m1} -> {m2})"
    _assert_no_held_write(dut)
    dut._log.info("PASS: store combining %s; different ids never combine",
                  "merges a same-burst same-id pair" if merge_en else "off: no merges, two bursts")


@cocotb.test(timeout_time=20000, timeout_unit="us")
async def cocotb_test_granite_core_merge_fill_lag(dut):
    """Store combining with the write DATA lagging the addresses (TASK-006,
    2026-10-29): eight same-burst pairs, one id per pair, arrive with the W
    channel on the slow_producer profile, so every entry in the pool is
    allocated and merged before its own fill lands -- up to two pending
    fills per entry, sixteen in all. The fill-order FIFO must hold them:
    sized to one per entry it overflowed, fills landed in the wrong slots
    and the board read back ~83% of the pair walk wrong at 32 outstanding
    (open page, counter ids). With STORE_MERGE_EN=1 the DFI bus sees eight
    bursts carrying each pair's second write; with 0 it sees all sixteen
    in order. Either way every burst that reaches the bus must be one the
    host wrote."""
    merge_en = int(os.environ.get("STORE_MERGE_EN", "0"))
    cocotb.start_soon(Clock(dut.aclk, _ACLK_NS, units='ns').start())
    cocotb.start_soon(Clock(dut.dfi_clk, _DFI_NS, units='ns').start())
    _idle(dut)
    dut.aresetn.value = 0
    dut.dfi_rstn.value = 0
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    dut.dfi_rstn.value = 1
    for _ in range(6):
        await RisingEdge(dut.aclk)
    bfm = _init_masters(dut)
    bfm.set_profile("backtoback", channels=["aw", "b"])
    bfm.set_profile("slow_producer", channels=["w"])    # W beats 8..20 cycles apart
    captured = []
    cocotb.start_soon(_dfi_model(dut, captured))
    for _ in range(400):
        await RisingEdge(dut.aclk)
        if int(dut.init_done_o.value):
            break
    assert int(dut.init_done_o.value) == 1, "init never completed"

    rng = random.Random(int(os.environ.get("SEED", "1")))
    n_pairs = 8                                   # == NUM_ENTRIES: every slot a merge target
    burst_bytes = BL_WORDS * (DW // 8)
    addrs = [0x4000 + k * burst_bytes for k in range(n_pairs)]   # one row, one bank
    first = [[rng.randrange(1 << DW) for _ in range(BL_WORDS)] for _ in range(n_pairs)]
    second = [[rng.randrange(1 << DW) for _ in range(BL_WORDS)] for _ in range(n_pairs)]
    reqs = []
    for k in range(n_pairs):
        reqs.append((addrs[k], first[k]))
        reqs.append((addrs[k], second[k]))
    captured.clear()
    # one id per PAIR: only a same-id pair combines (different ids never do)
    await with_timeout(bfm.write_many(reqs, axid_fn=lambda k: (k // 2) & 0xF), _PHASE_TIMEOUT_US, "us")
    want_words = (n_pairs if merge_en else 2 * n_pairs) * BL_WORDS
    for _ in range(2000):
        await RisingEdge(dut.dfi_clk)
        if len(captured) >= want_words:
            break
    for _ in range(50):                           # nothing more may trickle out
        await RisingEdge(dut.dfi_clk)
    wr_merges = int(dut.stat_wr_merge_o.value)
    bursts = [tuple(captured[i:i + BL_WORDS]) for i in range(0, len(captured), BL_WORDS)]
    dut._log.info("fill-lag: STORE_MERGE_EN=%d write merges=%d dfi bursts=%d",
                  merge_en, wr_merges, len(bursts))
    assert len(captured) == want_words, \
        f"expected {want_words} DFI words on the bus, saw {len(captured)}"
    if merge_en:
        assert wr_merges == n_pairs, f"expected {n_pairs} write merges, counted {wr_merges}"
        want = sorted(tuple(d) for d in second)
    else:
        assert wr_merges == 0, f"STORE_MERGE_EN=0 must not merge, counted {wr_merges}"
        want = sorted(tuple(d) for d in first + second)
    got = sorted(bursts)
    bad = [i for i, (g, w) in enumerate(zip(got, want)) if g != w]
    assert got == want, \
        f"{len(bad)} of {len(want)} DFI bursts are not what the host wrote (a fill landed in the wrong slot)"
    _assert_no_held_write(dut)
    dut._log.info("PASS: %d pending fills kept their slots", 2 * n_pairs if merge_en else n_pairs)


def _assert_no_held_write(dut):
    """Contract (granite TASK-006): a committed write's data is staged by the
    time its WRITE reaches the DFI command head. The DFI command path counts
    the cycles a WRITE sat at the head waiting (simulation-only); the
    scheduler's tWR / auto-precharge / ACT timers run from the commit, so a
    held WRITE is a JEDEC violation at the DRAM that no model here sees."""
    cmd = dut.u_dfi_plane.u_cmd
    held = int(cmd.r_wr_held_cnt.value)
    assert held == 0, f"{held} cycles with a WRITE held at the DFI head for its data (max run {int(cmd.r_wr_held_max.value)})"


def _core_params():
    """The granite_core parameter set every runner in this file builds with."""
    return {"AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32", "NUM_RANKS": "1",
            "STORE_BACKEND": os.environ.get("GRANITE_STORE_BACKEND", "1"),
            "BANK_FIFO_DEPTH": os.environ.get("GRANITE_BANK_FIFO_DEPTH", "0"),
            "HEAD2_EN": os.environ.get("GRANITE_HEAD2_EN", "1"),
            "DFI_CDC_EN": os.environ.get("GRANITE_DFI_CDC_EN", "1"),
            "HAS_SNARF": os.environ.get("GRANITE_HAS_SNARF", "0"),
            "INTAKE_FIFO_DEPTH": os.environ.get("GRANITE_INTAKE_FIFO_DEPTH", "0"),
            "AXI_SKID_DEPTH": os.environ.get("GRANITE_AXI_SKID_DEPTH", "2"),
            "SHARED_ADDR_MAP": os.environ.get("GRANITE_SHARED_ADDR_MAP", "0"),
            "HAS_PAGE_POLICY": os.environ.get("GRANITE_HAS_PAGE_POLICY", "1"),
            "BANK_TW": os.environ.get("GRANITE_BANK_TW", "5"),
            "BANK_EVT_REG": os.environ.get("GRANITE_BANK_EVT_REG", "1"),
            "BANK_CAP_MIXED": os.environ.get("GRANITE_BANK_CAP_MIXED", "6"),
            "HAS_AGE": os.environ.get("GRANITE_HAS_AGE", "0"),
            "STORE_MERGE_EN": os.environ.get("GRANITE_STORE_MERGE_EN", "1"),
            "PP_TIMEOUT_CLOSE": os.environ.get("GRANITE_PP_TIMEOUT_CLOSE", "1"),
            "DFI_CMD_FIFO_DEPTH": os.environ.get("GRANITE_DFI_CMD_FIFO_DEPTH", "4"),
            "DFI_WD_FIFO_DEPTH": os.environ.get("GRANITE_DFI_WD_FIFO_DEPTH", "16"),
            "DFI_RD_FIFO_DEPTH": os.environ.get("GRANITE_DFI_RD_FIFO_DEPTH", "4"),
            # GRANITE_FIXED_TIMINGS=1: the core compares against the T_*
            # constants, so they are set to the values this test drives on
            # the t_*_i ports (cocotb_test_* below) and the DFI model sees
            # the same spacing either way.
            "FIXED_TIMINGS": os.environ.get("GRANITE_FIXED_TIMINGS", "0"),
            "T_RCD": "2", "T_RP": "2", "T_RAS": "3", "T_RC": "4", "T_WR": "2",
            "T_RTP": "2", "T_FAW": "4", "T_RRD": "1", "T_WTR": "1", "T_RTW": "1",
            "T_CCD": "1", "T_REFI": str(0x7FFF), "T_RFC": "8",
            "NUM_BANKS": "8", "ROW_WIDTH": "14", "COL_WIDTH": "10",
            "DFI_RATE": str(DFI_RATE), "DRAM_BEAT_WIDTH": str(DRAM_BEAT), "DRAM_BL": str(BL)}


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_granite_core(request, test_level):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "granite_core"
    test_name = f"cocotb_test_granite_core_{test_level}"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = dict(_core_params())
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                 **level_env(test_level)}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_granite_core",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")


@pytest.mark.parametrize("size", [0, 1, 2, 3, 4])
def test_granite_core_narrow(request, size):
    """granite TASK-007: narrow INCR beats at every legal AxSIZE on the 128-bit host."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "granite_core"
    test_name = f"cocotb_test_granite_core_narrow_{size}"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = dict(_core_params())
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                 "NARROW_SIZE": str(size),
                 **level_env("func")}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_granite_core_narrow",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")


@pytest.mark.parametrize("merge_en", [0, 1])
def test_granite_core_merge(request, merge_en):
    """TASK-006 store combining, both parameter states (FUNC level)."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "granite_core"
    test_name = f"cocotb_test_granite_core_merge_{merge_en}"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = dict(_core_params())
    params["STORE_MERGE_EN"] = str(merge_en)
    # The product default return FIFO (DFI_RD_FIFO_DEPTH 4). This TB runs the
    # crossing (DFI_CDC_EN 1, dfi_clk = 2 x aclk), where granite_core sizes it
    # to the whole window; the OFF state's two back-to-back reads of one burst
    # are what lost a beat when 4 applied here too (pumice ISSUE-026).
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                 **level_env("func")}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_granite_core_merge",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")


@pytest.mark.parametrize("merge_en", [0, 1])
def test_granite_core_merge_fill_lag(request, merge_en):
    """TASK-006 store combining with the write data lagging the addresses, both parameter states (FUNC level)."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "granite_core"
    test_name = f"cocotb_test_granite_core_merge_fill_lag_{merge_en}"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = dict(_core_params())
    params["STORE_MERGE_EN"] = str(merge_en)
    # The product default return FIFO (DFI_RD_FIFO_DEPTH 4). This TB runs the
    # crossing (DFI_CDC_EN 1, dfi_clk = 2 x aclk), where granite_core sizes it
    # to the whole window; the OFF state's two back-to-back reads of one burst
    # are what lost a beat when 4 applied here too (pumice ISSUE-026).
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                 **level_env("func")}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_granite_core_merge_fill_lag",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")


async def _dfi_cmd_monitor(dut, counts):
    """Count the DRAM commands on the DFI pins, per phase: ACT, PRE, columns,
    and columns with auto-precharge (address bit 10). Decoded on dfi_clk."""
    row_w = 14                                     # _core_params ROW_WIDTH
    while True:
        await RisingEdge(dut.dfi_clk)
        cs = int(dut.dfi_cs_n_o.value); ras = int(dut.dfi_ras_n_o.value)
        cas = int(dut.dfi_cas_n_o.value); we = int(dut.dfi_we_n_o.value)
        addr = int(dut.dfi_address_o.value)
        for p in range(DFI_RATE):
            if (cs >> p) & 1:
                continue
            code = ((ras >> p) & 1, (cas >> p) & 1, (we >> p) & 1)
            if code == (0, 1, 1):
                counts["act"] += 1
                bank = (int(dut.dfi_bank_o.value) >> (p * 3)) & 0x7
                counts.setdefault("act_at", []).append(
                    (bank, (addr >> (p * row_w)) & ((1 << row_w) - 1)))
            elif code == (0, 1, 0):
                counts["pre"] += 1
            elif code in ((1, 0, 0), (1, 0, 1)):
                counts["col"] += 1
                if (addr >> (p * row_w + 10)) & 1:
                    counts["ap"] += 1


@cocotb.test(timeout_time=20000, timeout_unit="us")
async def cocotb_test_granite_core_page_mode(dut):
    """The four page modes told apart on two stimuli (2026-10-30).

    STIM=samerow: two writes to one row of one bank, different columns, with the W data on
    the slow_producer profile so the second write's fill lands long after
    the first write has fired. At the first write's fire the second is
    behind it in the bank (same row), so a close-on-drain column carries no
    AP; the bank then sits idle with the row open for far longer than
    tr_init (2) until the second fill lands.

      mode 0 build default   : drain AP only      -> ACT 1, PRE 0, AP 1 (the 2nd write)
      mode 1 static_open     : neither             -> ACT 1, PRE 0, AP 0
      mode 3 fixed_open      : timeout only        -> ACT 2, PRE 1, AP 0 (the row was
                                                      closed in the idle; the 2nd re-activates)
      mode 4 hybrid          : as fixed_open here  -> ACT 2, PRE 1, AP 0 (the 2nd
                                                      write's queue is EMPTY behind it:
                                                      no AP, and the reopen marks the
                                                      row keep-open, so no timeout PRE)

    STIM=conflict: two writes to two rows of one bank, W back to back, so the
    second is queued behind the first (a different row) when the first fires:
      mode 0 drain AP        : AP on both          -> ACT 2, PRE 0, AP 2
      mode 1 static_open     : demand PRE only     -> ACT 2, PRE 1, AP 0
      mode 3 fixed_open      : demand PRE, then the idle timeout closes
                               the 2nd row         -> ACT 2, PRE 2, AP 0
      mode 4 hybrid          : AP on the 1st (known conflict); the 2nd
                               (queue empty) does NOT: its ACT arms the
                               bank's drained-close history, but granite's
                               page policy sees the issued stream one cycle
                               late (PRED_CMD_REG), so the arm lands at ACT+3
                               and the column fired at ACT+2 (tRCD 2). The
                               idle timeout closes that row instead. Only a
                               bank's FIRST switch pays this; the arm then
                               persists (measured 2026-10-30)
                                                   -> ACT 2, PRE 1, AP 1
    Every count is exact, so an inert mode fails rather than passes."""
    mode = int(os.environ.get("PAGE_MODE", "0"))
    stim = os.environ.get("STIM", "samerow")
    want = {"samerow": {0: (1, 0, 1), 1: (1, 0, 0), 3: (2, 1, 0), 4: (2, 1, 0)},
            "conflict": {0: (2, 0, 2), 1: (2, 1, 0), 3: (2, 2, 0), 4: (2, 1, 1)}}[stim][mode]
    cocotb.start_soon(Clock(dut.aclk, _ACLK_NS, units='ns').start())
    cocotb.start_soon(Clock(dut.dfi_clk, _DFI_NS, units='ns').start())
    _idle(dut)
    dut.page_mode_i.value = mode
    dut.page_tr_init_i.value = 2
    dut.aresetn.value = 0
    dut.dfi_rstn.value = 0
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    dut.dfi_rstn.value = 1
    for _ in range(6):
        await RisingEdge(dut.aclk)
    bfm = _init_masters(dut)
    bfm.set_profile("backtoback", channels=["aw", "b"])
    bfm.set_profile("slow_producer" if stim == "samerow" else "backtoback",
                    channels=["w"])                     # samerow: W beats 8..20 cycles apart
    captured = []
    cocotb.start_soon(_dfi_model(dut, captured))
    for _ in range(400):
        await RisingEdge(dut.aclk)
        if int(dut.init_done_o.value):
            break
    assert int(dut.init_done_o.value) == 1, "init never completed"
    for _ in range(20):                           # let the init's own commands drain
        await RisingEdge(dut.dfi_clk)
    counts = {"act": 0, "pre": 0, "col": 0, "ap": 0}
    cocotb.start_soon(_dfi_cmd_monitor(dut, counts))
    rng = random.Random(int(os.environ.get("SEED", "1")))
    burst_bytes = BL_WORDS * (DW // 8)
    # bank_lsb 10 counts 8-byte DRAM words (row major): bank = addr[15:13],
    # row = addr >> 16, so +0x10000 is the same bank one row up (+0x2000 is
    # the NEXT BANK -- measured). The ACT check below proves the geometry.
    second = 0x4000 + (burst_bytes if stim == "samerow" else 0x10000)
    reqs = [(0x4000, [rng.randrange(1 << DW) for _ in range(BL_WORDS)]),
            (second, [rng.randrange(1 << DW) for _ in range(BL_WORDS)])]
    await with_timeout(bfm.write_many(reqs, axid_fn=lambda k: k & 0xF), _PHASE_TIMEOUT_US, "us")
    for _ in range(2000):
        await RisingEdge(dut.dfi_clk)
        if len(captured) >= 2 * BL_WORDS:
            break
    for _ in range(60):                           # the timeout PRE, if any, lands here
        await RisingEdge(dut.dfi_clk)
    dut._log.info("page mode %d %s: ACT=%d PRE=%d COL=%d AP=%d  ACT (bank,row)=%s", mode,
                  stim, counts["act"], counts["pre"], counts["col"], counts["ap"],
                  counts.get("act_at"))
    acts = counts.get("act_at", [])
    if stim == "conflict":
        assert len({b for b, _ in acts}) == 1 and len({r for _, r in acts}) == 2, \
            f"conflict stimulus must open two rows of one bank, saw {acts}"
    assert counts["col"] == 2, f"expected 2 column commands, saw {counts['col']}"
    got = (counts["act"], counts["pre"], counts["ap"])
    assert got == want, f"page mode {mode}: (ACT, PRE, AP) = {got}, expected {want}"


@pytest.mark.parametrize("stim", ["samerow", "conflict"])
@pytest.mark.parametrize("page_mode", [0, 1, 3, 4])
def test_granite_core_page_mode(request, page_mode, stim):
    """Page modes 0 / 1 / 3 / 4 told apart on the DFI command stream (FUNC level)."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "granite_core"
    test_name = f"cocotb_test_granite_core_page_mode_{page_mode}_{stim}"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = dict(_core_params())
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO", "PAGE_MODE": str(page_mode), "STIM": stim,
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                 **level_env("func")}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_granite_core_page_mode",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")


# ----------------------------------------------------------------------------
# granite ISSUE-001: same-id write B responses in AW order
# ----------------------------------------------------------------------------
_BANK_A_BASE = 0x4000      # bank 2 (bank_lsb 10: bank = addr[15:13], row = addr >> 16)
_BANK_B_BASE = 0x6000      # bank 3
_ROW_STRIDE = 0x10000      # +1 row, same bank (measured: see cocotb_test_granite_core_page_mode)


def _board_sched_csrs(dut):
    """The granite CSR resets the board runs with (regs/granite_csr.rdl):
    PAGE_POLICY_CFG.policy_mode 4 (hybrid), PAGE_TIMEOUT_CFG.tr_init 2,
    SCHED_POLICY all 0 (build default order, no QoS, age inert),
    SCHED_WR_WM high 2 / low 1, wr_batch_max = GRANITE_DIR_BATCH_MAX 255."""
    dut.page_mode_i.value = 4
    dut.page_tr_init_i.value = 2
    dut.sched_order_mode_i.value = 0
    dut.sched_row_sel_i.value = 0
    dut.sched_col_sel_i.value = 0
    dut.sched_access_pref_i.value = 0
    dut.sched_wr_high_wm_i.value = 2
    dut.sched_wr_batch_max_i.value = 255
    dut.sched_wr_low_wm_i.value = 1
    dut.sched_prio_sub_i.value = 0
    dut.sched_qos_en_i.value = 0
    dut.sched_age_thresh_i.value = 0


async def _dfi_wr_burst_monitor(dut, cyc, bursts):
    """Passive: every BL_WORDS-word write burst on the DFI write bus, with
    the dfi_clk cycle its first word appeared. Drain order == this order."""
    cur, t0 = [], 0
    while True:
        await RisingEdge(dut.dfi_clk)
        if int(dut.dfi_wrdata_en_o.value) != 0:
            if not cur:
                t0 = cyc[0]
            cur.append(int(dut.dfi_wrdata_o.value))
            if len(cur) == BL_WORDS:
                bursts.append((t0, tuple(cur)))
                cur = []


@cocotb.test(timeout_time=40000, timeout_unit="us")
async def cocotb_test_granite_core_b_order(dut):
    """granite BUG-001 (was ISSUE-001): AXI requires B responses of ONE id in AW order.

    granite produces a write's B when its slot DRAINS (mc_bank_fifo_store
    wr_done_*), slots drain in commit order (u_wr_drain_q fed by wr_commit_*),
    and the pick commits FR-FCFS across banks with no id compare. So:

        blockers (id 7): N writes to bank A, alternating rows (each a row miss)
        [opener  (id 6): one write to bank B row R  -- the W2_HIT variant]
        W1       (id X): bank A, another row, queued behind the blockers
        W2       (id X or Y): bank B (row R: a page hit behind the opener)

    Each trial runs twice:
      * DIFFERENT ids (X=3, Y=4) -- the vacuity guard: the DFI write-burst
        monitor must see W2 DRAIN before W1 in at least one trial, or the
        scenario never inverts commit order and a same-id pass proves nothing.
        Since the fix (granite BUG-001) the store releases EVERY B in AW order,
        so B(3) must precede B(4) here even when the drain inverted.
      * SAME id (X=Y=3) -- the AXI rule. A B carries no address, but AXI says
        the FIRST id-3 B acknowledges W1. A B leaves when its write DRAINS the
        store, which is a fixed lead ahead of the write's burst on the DFI bus
        (command delay + CDC + write latency); the different-id phase measures
        that lead for W1 and W2 (their ids are unique there). The first id-3 B
        may therefore lead W1's DFI burst by at most that lead: before the fix
        B left in drain order, so W2 draining first put the first id-3 B a
        whole blocker-run ahead of W1's data.

    The sweep: N in {1, 2, 4} x W2 page hit/miss x 2 reps, CSRs at the board
    resets; the pytest cells pace the AW channel backtoback / constrained. Fails if ANY same-id trial drains (=Bs) out of AW order, or if NO
    different-id trial inverts (the scenario would then prove nothing)."""
    cocotb.start_soon(Clock(dut.aclk, _ACLK_NS, units='ns').start())
    cocotb.start_soon(Clock(dut.dfi_clk, _DFI_NS, units='ns').start())
    _idle(dut)
    _board_sched_csrs(dut)
    dut.aresetn.value = 0
    dut.dfi_rstn.value = 0
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    dut.dfi_rstn.value = 1
    for _ in range(6):
        await RisingEdge(dut.aclk)
    bfm = _init_masters(dut)
    # W stays back to back: a write commits only once its data is in, so a
    # paced W channel fills W1 long before W2 and the bank-A queue drains
    # first -- measured: W on `constrained` inverted 0/12 different-id
    # trials (vacuous). The AW channel carries the gap setting instead.
    aw_profile = os.environ.get("AW_PROFILE", "backtoback")
    bfm.set_profile("backtoback", channels=["w", "b"])
    bfm.set_profile(aw_profile, channels=["aw"])
    captured = []
    cocotb.start_soon(_dfi_model(dut, captured))

    cyc = [0]

    async def _count():
        while True:
            await RisingEdge(dut.dfi_clk)
            cyc[0] += 1
    cocotb.start_soon(_count())
    b_log = []                       # (dfi cycle, bid) in B-handshake order
    bfm.wr.b_channel.add_callback(lambda pkt: b_log.append((cyc[0], int(getattr(pkt, 'id', 0)))))
    bursts = []
    cocotb.start_soon(_dfi_wr_burst_monitor(dut, cyc, bursts))

    for _ in range(400):
        await RisingEdge(dut.aclk)
        if int(dut.init_done_o.value):
            break
    assert int(dut.init_done_o.value) == 1, "init never completed"
    for _ in range(20):
        await RisingEdge(dut.dfi_clk)

    rng = random.Random(int(os.environ.get("SEED", "1")))
    burst_bytes = BL_WORDS * (DW // 8)
    trial_cfgs = [(n, hit, rep) for rep in range(2) for n in (1, 2, 4) for hit in (0, 1)]
    vac_inv, vac_total = 0, 0
    same_inv = []
    lead_max = 0                     # max (DFI burst cycle - B cycle) seen for W1/W2, diff phase
    row_base = 1
    for t, (n_blk, w2_hit, rep) in enumerate(trial_cfgs):
        for phase in ("diff", "same"):
            id1, id2 = (3, 4) if phase == "diff" else (3, 3)
            rb = row_base
            row_base += n_blk + 3
            reqs, ids, names = [], [], []

            def add(addr, axid, name):
                reqs.append((addr, [rng.randrange(1 << DW) for _ in range(BL_WORDS)]))
                ids.append(axid)
                names.append(name)
            if w2_hit:
                add(_BANK_B_BASE + rb * _ROW_STRIDE, 6, "open_B")
            for k in range(n_blk):
                add(_BANK_A_BASE + (rb + 1 + (k % 2)) * _ROW_STRIDE, 7, f"blk{k}_A")
            add(_BANK_A_BASE + rb * _ROW_STRIDE, id1, "W1_A")
            add(_BANK_B_BASE + rb * _ROW_STRIDE + (burst_bytes if w2_hit else 0), id2, "W2_B")
            i_w1, i_w2 = len(reqs) - 2, len(reqs) - 1

            b_log.clear()
            bursts.clear()
            captured.clear()
            await with_timeout(bfm.write_many(reqs, axid_fn=lambda k: ids[k]),
                               _PHASE_TIMEOUT_US, "us")
            for _ in range(2000):
                await RisingEdge(dut.dfi_clk)
                if len(bursts) >= len(reqs):
                    break
            for _ in range(60):
                await RisingEdge(dut.dfi_clk)
            assert len(bursts) == len(reqs), \
                f"trial {t} {phase}: {len(bursts)} DFI write bursts for {len(reqs)} writes"
            by_data = {tuple(d): i for i, (_, d) in enumerate(reqs)}
            drain = [by_data[d] for _, d in bursts]
            t_dfi = {by_data[d]: tc for tc, d in bursts}
            assert sorted(drain) == list(range(len(reqs))), \
                f"trial {t} {phase}: DFI bursts are not the host's writes"
            w2_first = drain.index(i_w2) < drain.index(i_w1)
            dut._log.info(
                "BORDER trial %d N=%d w2_hit=%d rep=%d %s: AW %s | ids %s | drain %s | "
                "B (cyc,id) %s | DFI cyc W1=%d W2=%d", t, n_blk, w2_hit, rep, phase,
                names, ids, [names[i] for i in drain], b_log, t_dfi[i_w1], t_dfi[i_w2])
            if phase == "diff":
                vac_total += 1
                vac_inv += int(w2_first)          # the DRAIN inverted: the scenario bites
                b_ids = [b for _, b in b_log]
                b_w2_first = b_ids.index(id2) < b_ids.index(id1)
                # Bs leave in AW order whatever the drain did (granite BUG-001 fix)
                assert not b_w2_first, \
                    (f"trial {t}: B(id {id2}, W2) left before B(id {id1}, W1) although W1's AW "
                     f"came first (drain W2 first={w2_first})")
                t_b = {b: tc for tc, b in b_log}
                lead_max = max(lead_max, t_dfi[i_w1] - t_b[id1], t_dfi[i_w2] - t_b[id2])
            else:
                b3 = [tc for tc, b in b_log if b == 3]
                # the first id-3 B acknowledges W1 (AXI); it may lead W1's DFI burst
                # by the measured drain-to-DFI lead and no more
                if b3 and b3[0] < t_dfi[i_w1] - lead_max - 2:
                    same_inv.append(
                        f"trial {t} (N={n_blk}, w2_hit={w2_hit}): AW W1(bank 2 row {rb}) then "
                        f"W2(bank 3 row {rb}), both id 3; drain W2 first={w2_first}; first id-3 B "
                        f"at dfi cyc {b3[0]}, W1 data on DFI at {t_dfi[i_w1]} (W2 at {t_dfi[i_w2]}), "
                        f"lead bound {lead_max}")
    _assert_no_held_write(dut)
    dut._log.info("BORDER summary: drain inverted in %d/%d different-id trials; same-id B "
                  "ahead of its write in %d/%d trials (B-to-DFI lead bound %d)",
                  vac_inv, vac_total, len(same_inv), len(trial_cfgs), lead_max)
    assert vac_inv > 0, \
        (f"vacuity: no different-id trial of {vac_total} drained W2 before W1 -- the "
         f"scenario never inverts commit order, so a same-id pass would prove nothing")
    assert not same_inv, \
        ("granite BUG-001: a same-id B left ahead of its own write in "
         f"{len(same_inv)}/{len(trial_cfgs)} trials:\n  " + "\n  ".join(same_inv))
    dut._log.info("PASS: Bs in AW order on every trial; the drain inverted in %d/%d",
                  vac_inv, vac_total)


async def _axi_b_pending_tracker(dut, stat):
    """Passive: AW and B handshakes on the host port, the peak of their
    difference, and the cycles the intake's B FIFO was FULL -- the condition
    under which, before the fix, a store done was dropped on the floor."""
    aw, b, full = 0, 0, 0
    fifo_ready = dut.u_axi_plane.u_wr_intake.w_b_wr_ready
    while True:
        await RisingEdge(dut.aclk)
        if int(dut.s_axi_awvalid.value) and int(dut.s_axi_awready.value):
            aw += 1
        if int(dut.s_axi_bvalid.value) and int(dut.s_axi_bready.value):
            b += 1
        if int(fifo_ready.value) == 0:
            full += 1
        stat["aw"], stat["b"], stat["fifo_full_cycles"] = aw, b, full
        stat["max_pending"] = max(stat.get("max_pending", 0), aw - b)


@cocotb.test(timeout_time=40000, timeout_unit="us")
async def cocotb_test_granite_core_b_stall(dut):
    """memory-controllers BUG-001: a host that stalls BREADY must lose no B.

    The intake's B FIFO is 4 deep and, before the fix, the store's wr_done had
    no ready: the fifth completion into a full FIFO was dropped and the master
    waited forever. Here the master accepts each B only after a long ready
    delay while N writes stream in, so completions pile up well past four;
    every AW must still get its B (the engine runner returns only when they
    all have). The peak of outstanding Bs is the vacuity guard: it must exceed
    the FIFO depth, or the test never reached the hole."""
    cocotb.start_soon(Clock(dut.aclk, _ACLK_NS, units='ns').start())
    cocotb.start_soon(Clock(dut.dfi_clk, _DFI_NS, units='ns').start())
    _idle(dut)
    _board_sched_csrs(dut)
    dut.aresetn.value = 0
    dut.dfi_rstn.value = 0
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    dut.dfi_rstn.value = 1
    for _ in range(6):
        await RisingEdge(dut.aclk)
    bfm = _init_masters(dut)
    bfm.set_profile("backtoback", channels=["aw", "w"])
    # one B accepted every B_STALL cycles: with 24 writes in flight the
    # controller must hold far more than the intake FIFO's 4
    b_stall = int(os.environ.get("B_STALL", "40"))
    bfm.wr.b_channel.randomizer = FlexRandomizer({'ready_delay': ([(b_stall, b_stall)], [1])})
    captured = []
    cocotb.start_soon(_dfi_model(dut, captured))
    stat = {}
    cocotb.start_soon(_axi_b_pending_tracker(dut, stat))
    b_ids = []
    bfm.wr.b_channel.add_callback(lambda pkt: b_ids.append(int(getattr(pkt, 'id', 0))))

    for _ in range(400):
        await RisingEdge(dut.aclk)
        if int(dut.init_done_o.value):
            break
    assert int(dut.init_done_o.value) == 1, "init never completed"
    for _ in range(20):
        await RisingEdge(dut.dfi_clk)

    rng = random.Random(int(os.environ.get("SEED", "1")))
    n = 24
    # bank k % 8 (addr[15:13]), row k // 8: every bank busy, each write its own row
    reqs = [(((k % 8) << 13) | ((k // 8) * _ROW_STRIDE),
             [rng.randrange(1 << DW) for _ in range(BL_WORDS)]) for k in range(n)]
    ids = [k % 16 for k in range(n)]
    try:
        await with_timeout(bfm.write_many(reqs, axid_fn=lambda k: ids[k]),
                           4 * _PHASE_TIMEOUT_US, "us")
    except SimTimeoutError:
        raise AssertionError(
            f"BUG-001: only {stat.get('b', 0)} of {n} B responses arrived with BREADY stalled "
            f"{b_stall} cycles per B (AW accepted {stat.get('aw', 0)}, peak pending "
            f"{stat.get('max_pending', 0)}): the controller dropped B responses")
    for _ in range(50):
        await RisingEdge(dut.aclk)
    held = int(dut.u_dfi_plane.u_cmd.r_wr_held_cnt.value)
    dut._log.info("BSTALL: %d AW, %d B, peak outstanding Bs %d, intake B FIFO full %d cycles, "
                  "WRITE held at the DFI head %d cycles, ids %s", stat["aw"], stat["b"],
                  stat["max_pending"], stat["fifo_full_cycles"], held, b_ids)
    assert stat["aw"] == n and stat["b"] == n, \
        f"{stat['b']} B responses for {stat['aw']} accepted AWs ({n} issued)"
    assert sorted(b_ids) == sorted(ids), f"B ids {sorted(b_ids)} != AW ids {sorted(ids)}"
    assert stat["fifo_full_cycles"] > 0, \
        ("vacuity: the intake's 4-deep B FIFO never filled, so the dropped-done hole was "
         f"never reached (peak outstanding {stat['max_pending']}; raise B_STALL)")
    # the dense 24-write stream is also what showed the CDC write-data FIFO at its
    # full-depth equilibrium (granite_core DFI_WD_FIFO_EFF): the contract holds here
    _assert_no_held_write(dut)
    dut._log.info("PASS: %d/%d Bs with up to %d outstanding", stat["b"], n, stat["max_pending"])


@pytest.mark.parametrize("aw_profile", ["backtoback", "constrained"])
def test_granite_core_b_order(request, aw_profile):
    """granite ISSUE-001: same-id write Bs in AW order across banks (FUNC level)."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "granite_core"
    test_name = f"cocotb_test_granite_core_b_order_{aw_profile}"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = dict(_core_params())
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO", "AW_PROFILE": aw_profile,
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                 **level_env("func")}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_granite_core_b_order",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")


def test_granite_core_b_stall(request):
    """memory-controllers BUG-001: no B is lost when the host stalls BREADY (FUNC level)."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "granite_core"
    test_name = "cocotb_test_granite_core_b_stall"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = dict(_core_params())
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                 **level_env("func")}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_granite_core_b_stall",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
