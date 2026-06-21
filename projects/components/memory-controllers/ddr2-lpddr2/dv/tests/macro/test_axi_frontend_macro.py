# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Author: sean galloway
# Created: 2026-06-18

"""
Test runner for axi_frontend_macro using CocoTBFramework AXI4 BFMs.

Methodology mirrors stream's macro-level test runners:
  - pytest parametrize over (TEST_LEVEL, NUM_RANKS, TIMING_PROFILE, ...)
  - cocotb_test.simulator.run invokes Verilator
  - TB class (axi_frontend_macro_tb) encapsulates BFM + stub setup
  - FlexRandomizer profiles drive directed-random valid/ready timing on
    every AXI channel (AXI_RANDOMIZER_CONFIGS: backtoback / fast /
    constrained / slow_producer / burst_pause / high_throughput)

Test scenarios:
  forward_smoke   : write A, read A while in-flight  -> forward hit
  miss_smoke      : write A, read B (no match)       -> miss path
  random_directed : N random write/read pairs with shuffled order,
                    seed-driven addresses and data, verifying snarf
                    when addresses overlap and rd-inject otherwise
"""

import os
import sys
import random
import logging
import pytest

import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Make the component dv dir importable as `tbclasses.*`
_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.axi_frontend_macro_tb import AxiFrontendMacroTB  # noqa: E402


# ---------------------------------------------------------------------------
# CocoTB top-level (dispatches by TEST_TYPE)
# ---------------------------------------------------------------------------

@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_axi_frontend(dut):
    test_type      = os.environ.get("TEST_TYPE", "forward_smoke")
    timing_profile = os.environ.get("TIMING_PROFILE", "backtoback")
    seed           = int(os.environ.get("SEED", "12345"))

    log = logging.getLogger("axi_frontend_test")
    log.info(f"TEST_TYPE='{test_type}' TIMING_PROFILE='{timing_profile}' SEED={seed}")

    tb = AxiFrontendMacroTB(
        dut=dut,
        axi_data_width=int(os.environ.get("AXI_DATA_WIDTH", "64")),
        axi_id_width=int(os.environ.get("AXI_ID_WIDTH",     "4")),
        axi_addr_width=int(os.environ.get("AXI_ADDR_WIDTH", "32")),
        axi_user_width=int(os.environ.get("AXI_USER_WIDTH", "1")),
    )
    await tb.setup(timing_profile=timing_profile)

    scenarios = {
        "forward_smoke":        _run_forward_smoke,
        "miss_smoke":           _run_miss_smoke,
        "random_directed":      _run_random_directed,
        "snarf_timing_schmoo":  _run_snarf_timing_schmoo,
        "addr_space_sweep":     _run_addr_space_sweep,
        "scheme_sweep":         _run_scheme_sweep,
        "partial_strb":         _run_partial_strb,
        "burst_len_sweep":      _run_burst_len_sweep,
        "perfect_streaming":    _run_perfect_streaming,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)

    # Drain a few cycles so background tasks finish printing
    for _ in range(20):
        await RisingEdge(tb.dut.mc_clk)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------

async def _run_forward_smoke(tb):
    """Issue write to A, then read from A — expect forward hit and matching
    data. The write will complete in the background via the scheduler stub.
    """
    addr  = 0x0000_4080
    beats = [0xCAFE_BABE_DEAD_BEEF, 0x1234_5678_9ABC_DEF0,
             0x1111_2222_3333_4444, 0x5555_6666_7777_8888]

    # Start the write but don't await it (B comes back when scheduler stub
    # drives b_complete). Run it as a background task.
    wr_task = cocotb.start_soon(tb.axi_write(addr, beats, axi_id=3))

    # Give the AW + W beats time to land in the macro before the AR.
    for _ in range(20):
        await RisingEdge(tb.dut.mc_clk)

    data = await tb.axi_read(addr, beats=len(beats), axi_id=3)
    assert data == beats, f"data mismatch: got {data} want {beats}"
    assert tb.fwd_hits_seen >= 1, \
        f"expected at least one fwd hit; got hits={tb.fwd_hits_seen} misses={tb.fwd_misses_seen}"
    tb.log.info(f"forward_smoke PASS — fwd_hits={tb.fwd_hits_seen} fwd_misses={tb.fwd_misses_seen}")

    # Let the write transaction complete (scheduler stub will drive b_complete)
    await wr_task


async def _run_miss_smoke(tb):
    """Issue write to A, then read from B (different address). The read
    should NOT snarf — rd_scheduler_stub injects expected zeros (since B
    has never been written) and the read completes via the miss path.
    """
    wr_addr = 0x0000_4080
    wr_data = [0x1111_2222_3333_4444, 0x5555_6666_7777_8888]
    wr_task = cocotb.start_soon(tb.axi_write(wr_addr, wr_data, axi_id=3))

    for _ in range(20):
        await RisingEdge(tb.dut.mc_clk)

    rd_addr = 0x0000_8080
    data = await tb.axi_read(rd_addr, beats=2, axi_id=5)
    # B was never written → expected zeros from memory model
    assert data == [0, 0], f"data mismatch: got {data} want [0, 0]"
    assert tb.fwd_misses_seen >= 1, \
        f"expected at least one fwd miss; got hits={tb.fwd_hits_seen} misses={tb.fwd_misses_seen}"
    tb.log.info(f"miss_smoke PASS — fwd_hits={tb.fwd_hits_seen} fwd_misses={tb.fwd_misses_seen}")
    await wr_task


async def _run_random_directed(tb):
    """Run a sequence of random write/read pairs. Half target the same
    address (forward path), half target distinct addresses (miss path).
    Verifies data integrity at the AXI boundary across both paths.
    """
    random.seed(tb.SEED)
    num_pairs = int(os.environ.get("NUM_PAIRS", "8"))
    burst_len = 4

    for i in range(num_pairs):
        addr  = (random.randint(0x1000, 0xF000) >> 5) << 5   # 32-byte aligned
        beats = [random.getrandbits(tb.AXI_DATA_WIDTH) & tb.AXI_DATA_MASK
                 for _ in range(burst_len)]
        wr_id = random.randint(0, (1 << tb.AXI_ID_WIDTH) - 1)
        rd_id = random.randint(0, (1 << tb.AXI_ID_WIDTH) - 1)

        # 50/50 split: same address (forward) vs different (miss)
        rd_addr = addr if (i & 1) == 0 else (addr ^ 0x1_0000)

        wr_task = cocotb.start_soon(tb.axi_write(addr, beats, axi_id=wr_id))
        for _ in range(15):
            await RisingEdge(tb.dut.mc_clk)
        data = await tb.axi_read(rd_addr, beats=burst_len, axi_id=rd_id)

        if rd_addr == addr:
            assert data == beats, (
                f"pair {i} fwd path mismatch at addr 0x{addr:x}:"
                f" got {data} want {beats}"
            )
        else:
            # rd-stub injected expected zeros for unwritten address
            assert data == [0] * burst_len, (
                f"pair {i} miss path mismatch at addr 0x{rd_addr:x}:"
                f" got {data} want zeros"
            )

        await wr_task

    tb.log.info(
        f"random_directed PASS — {num_pairs} pairs "
        f"(fwd_hits={tb.fwd_hits_seen}, fwd_misses={tb.fwd_misses_seen})"
    )


# ---------------------------------------------------------------------------
# Schmoo: snarf timing — vary the read's arrival relative to the write,
# from 8 cycles before to 8 cycles after, with the wr-stub paused so the
# write stays in the CAM until we let it complete.
# ---------------------------------------------------------------------------

async def _run_snarf_timing_schmoo(tb):
    """Sweep read-to-write delta across [-8 .. +8] with the wr_stub paused.

    Negative delta = read issued first, then write at |delta| cycles later.
    Positive delta = write issued first, then read at delta cycles later.

    For positive delta with the write still in the CAM, the read snarfs.
    For negative delta the write hasn't reached the CAM yet so the read
    takes the miss path (the rd_stub injects whatever the mem model holds
    at the time, which is the pre-populated expected value).

    We don't strictly assert hit-vs-miss per delta (the boundary is
    timing-dependent) — instead we assert that across the sweep we see
    BOTH paths exercised and data integrity holds in every iteration.
    """
    deltas = [-8, -6, -4, -2, 0, 2, 4, 6, 8]
    burst_len = 2
    base_addr = 0x0000_4080
    # Vary address per iteration to make sure no inter-iteration state leaks
    # into the next; the snarf is keyed on (rank, bank, row, col).

    total_hits = 0
    total_misses = 0
    for i, delta in enumerate(deltas):
        addr = base_addr + (i * 0x80)
        beats = [(0xCAFE_0000_0000_0000 | (i << 24) | b) & tb.AXI_DATA_MASK
                 for b in range(burst_len)]

        # Pre-populate mem so that rd_inject (miss path) has the right
        # data; snarf path will source from w_buf instead.
        tb.mem.write(addr, beats)

        hits_before, misses_before = tb.stat_snapshot()

        # Pause wr_stub so the write stays in the CAM during the test.
        tb.wr_stub_paused = True

        if delta >= 0:
            wr_task = cocotb.start_soon(tb.axi_write(addr, beats, axi_id=1))
            for _ in range(delta + 6):   # +6 lets AW+W actually land
                await RisingEdge(tb.dut.mc_clk)
            rdata = await tb.axi_read(addr, beats=burst_len, axi_id=2)
        else:
            rd_task = cocotb.start_soon(tb.axi_read(addr, beats=burst_len, axi_id=2))
            for _ in range(-delta):
                await RisingEdge(tb.dut.mc_clk)
            wr_task = cocotb.start_soon(tb.axi_write(addr, beats, axi_id=1))
            rdata = await rd_task

        # Resume the stub so the queued write can drain.
        tb.wr_stub_paused = False
        await wr_task

        # Data integrity check — every iteration must return the right beats.
        assert rdata == beats, (
            f"delta={delta}: data mismatch at addr 0x{addr:x}: "
            f"got {rdata} want {beats}"
        )

        hits_after, misses_after = tb.stat_snapshot()
        h = hits_after - hits_before
        m = misses_after - misses_before
        total_hits += h
        total_misses += m
        tb.log.info(f"schmoo delta={delta:+d} hits={h} misses={m} addr=0x{addr:x}")

        # Settle between iterations
        for _ in range(10):
            await RisingEdge(tb.dut.mc_clk)

    # We should have seen BOTH paths across the sweep
    assert total_hits   > 0, f"no forward hits across schmoo (total_hits={total_hits})"
    assert total_misses > 0, f"no forward misses across schmoo (total_misses={total_misses})"
    tb.log.info(
        f"snarf_timing_schmoo PASS — total hits={total_hits} misses={total_misses}"
    )


# ---------------------------------------------------------------------------
# Address-space sweep — vary (bank, row, col) tuples and verify snarf
# correctness across each. Rank is fixed at 0 (only NR=1 builds here).
# ---------------------------------------------------------------------------

async def _run_addr_space_sweep(tb):
    """For each (bank, row, col) point in a small grid, do a write+read
    pair and verify forward hit + data integrity.

    Address bit layout under ROW_MAJOR (default), with
    BYTE_OFFSET_WIDTH=3, COL_WIDTH=10, BANK_WIDTH=3, ROW_WIDTH=14:

      [2:0]    byte offset (stripped)
      [12:3]   col[9:0]
      [15:13]  bank[2:0]
      [29:16]  row[13:0]

    So we can sweep (bank, row, col_low) by constructing addresses
    directly from those fields.
    """
    BYTE_OFF = 3
    COL_W    = 10
    BANK_W   = 3

    def make_addr(bank, row, col):
        return (row << (BYTE_OFF + COL_W + BANK_W)) \
             | (bank << (BYTE_OFF + COL_W)) \
             | (col << BYTE_OFF)

    # Coverage points — not exhaustive but spans the field
    banks = [0, 1, 4, 7]                     # boundaries + middle
    rows  = [0, 1, 0x100, 0x3FF, 0x3FFF]     # zero, small, mid, large, max-ish
    cols  = [0, 1, 0x100]

    burst_len = 2
    for bank in banks:
        for row in rows:
            for col in cols:
                addr  = make_addr(bank, row, col)
                beats = [(0xBA5E_0000_0000_0000
                          | (bank << 32) | (row << 16) | (col << 4) | i)
                         & tb.AXI_DATA_MASK
                         for i in range(burst_len)]
                tb.mem.write(addr, beats)

                hits_before, _ = tb.stat_snapshot()
                tb.wr_stub_paused = True
                wr_task = cocotb.start_soon(tb.axi_write(addr, beats, axi_id=3))
                # Wait deterministically for the wr CAM to hold the push.
                await tb.wait_for_wr_cam_push(prev_occ=0)
                rdata = await tb.axi_read(addr, beats=burst_len, axi_id=4)
                tb.wr_stub_paused = False
                await wr_task

                assert rdata == beats, (
                    f"addr 0x{addr:x} (bank={bank} row={row:#x} col={col:#x}): "
                    f"got {rdata} want {beats}"
                )
                hits_after, _ = tb.stat_snapshot()
                assert hits_after > hits_before, (
                    f"expected fwd hit at addr 0x{addr:x}"
                )

                for _ in range(4):
                    await RisingEdge(tb.dut.mc_clk)

    tb.log.info(
        f"addr_space_sweep PASS — {len(banks)*len(rows)*len(cols)} points "
        f"fwd_hits={tb.fwd_hits_seen}"
    )


# ---------------------------------------------------------------------------
# Scheme sweep — same workload under ROW_MAJOR and BANK_INTERLEAVE
# (XOR_HASH currently requires a separate verilator build with
# SYNTH_XOR_HASH=1, deferred to a future test variant).
# ---------------------------------------------------------------------------

async def _run_scheme_sweep(tb):
    """Run a snarf check under each runtime-selectable scheme."""
    schemes = [
        (tb.SCHEME_ROW_MAJOR,       "ROW_MAJOR"),
        (tb.SCHEME_BANK_INTERLEAVE, "BANK_INTERLEAVE"),
    ]
    addr_base = 0x0001_4080
    burst_len = 2

    for scheme_val, scheme_name in schemes:
        tb.set_scheme(scheme_val)
        # Pump a few cycles so the new scheme is sampled
        for _ in range(4):
            await RisingEdge(tb.dut.mc_clk)

        addr  = addr_base + (scheme_val << 10)
        beats = [(0x5CAE_0000_0000_0000 | (scheme_val << 32) | i)
                 & tb.AXI_DATA_MASK for i in range(burst_len)]
        tb.mem.write(addr, beats)

        hits_before, _ = tb.stat_snapshot()
        tb.wr_stub_paused = True
        wr_task = cocotb.start_soon(tb.axi_write(addr, beats, axi_id=3))
        await tb.wait_for_wr_cam_push(prev_occ=0)
        rdata = await tb.axi_read(addr, beats=burst_len, axi_id=4)
        tb.wr_stub_paused = False
        await wr_task

        assert rdata == beats, f"{scheme_name}: data mismatch"
        hits_after, _ = tb.stat_snapshot()
        assert hits_after > hits_before, f"{scheme_name}: no fwd hit"
        tb.log.info(f"scheme_sweep[{scheme_name}] PASS")

    tb.log.info("scheme_sweep PASS")


# ---------------------------------------------------------------------------
# Partial-strobe writes must NOT forward — wr2rd_forward gates on
# cam_full_strb_i, which axi_intake computes by AND-reducing wstrb
# across the burst.
# ---------------------------------------------------------------------------

async def _run_partial_strb(tb):
    """Write a burst with partial wstrb (not 0xFF). The full_strb AND-reduce
    in axi_intake should yield 0 → wr2rd_forward marks the entry
    ineligible → the next matching read must take the miss path
    (rd_stub injects from the memory model, which models the post-write
    DRAM state)."""
    addr  = 0x0000_4080
    beats = [0xAAAA_AAAA_AAAA_AAAA, 0xBBBB_BBBB_BBBB_BBBB]

    hits_before, misses_before = tb.stat_snapshot()
    tb.wr_stub_paused = True
    wr_task = cocotb.start_soon(
        tb.axi_write(addr, beats, axi_id=5, strb=0x0F)   # only low nibble enabled
    )
    await tb.wait_for_wr_cam_push(prev_occ=0)
    rdata = await tb.axi_read(addr, beats=len(beats), axi_id=6)
    tb.wr_stub_paused = False
    await wr_task

    hits_after, misses_after = tb.stat_snapshot()
    assert hits_after == hits_before, (
        f"partial-strb write must NOT forward — saw {hits_after - hits_before} hits"
    )
    assert misses_after > misses_before, \
        "partial-strb read should take the miss path (no hit, miss observed)"
    tb.log.info(
        f"partial_strb PASS — fwd_miss observed, rdata via rd_inject = {[hex(x) for x in rdata]}"
    )


# ---------------------------------------------------------------------------
# Burst-length sweep — varies burst_len across {1, 2, 4, 8, 16}. For each
# length, do a snarf check and verify data integrity.
# ---------------------------------------------------------------------------

async def _run_burst_len_sweep(tb):
    """Vary the burst length and verify snarf + data integrity for each."""
    for burst_len in [1, 2, 4, 8, 16]:
        addr  = 0x0000_4000 + (burst_len * 0x100)
        beats = [(0xB527_0000_0000_0000 | (burst_len << 24) | i)
                 & tb.AXI_DATA_MASK for i in range(burst_len)]
        tb.mem.write(addr, beats)

        hits_before, _ = tb.stat_snapshot()
        tb.wr_stub_paused = True
        wr_task = cocotb.start_soon(tb.axi_write(addr, beats, axi_id=1))
        await tb.wait_for_wr_cam_push(prev_occ=0)
        rdata = await tb.axi_read(addr, beats=burst_len, axi_id=2)
        tb.wr_stub_paused = False
        await wr_task

        assert rdata == beats, f"len={burst_len}: {rdata} != {beats}"
        hits_after, _ = tb.stat_snapshot()
        assert hits_after > hits_before, f"len={burst_len}: no fwd hit"
        tb.log.info(f"burst_len_sweep[len={burst_len}] PASS")

        for _ in range(6):
            await RisingEdge(tb.dut.mc_clk)

    tb.log.info("burst_len_sweep PASS")


# ---------------------------------------------------------------------------
# Perfect-streaming — prove host AXI never throttles under ideal drain.
#
# This scenario isolates the axi_intake's intrinsic handshake budget.
# Under `backtoback` master timing + un-paused scheduler stubs:
#   * AW / AR / B / R skid buffers are never full → 0 DUT stall cycles
#   * W has a SINGLE design-mandated stall cycle per burst boundary —
#     the cycle where `r_burst_done` is high awaiting the AW push to
#     downstream. For N back-to-back bursts that's ≤ (N-1) stall cycles
#     total AND no contiguous stall run can exceed 1 cycle.
#
# Anything outside that budget = real bug.
# ---------------------------------------------------------------------------

async def _run_perfect_streaming(tb):
    """Prove ≥2us contiguous (wvalid && wready) and (rvalid && rready)
    under ideal drain. Method:

      * Pause the single-issue scheduler stubs; enable the pipelined
        drains (multi-outstanding, no per-slot deadtime).
      * Drive a SINGLE long burst (256 beats AXI4-max) per side, with
        all W beats bulk-queued into the BFM's pipeline so it stays in
        zero-bubble mode.
      * 256 beats @ 10ns clock = 2.56us contiguous active per burst,
        clearing the 2us bar with margin.

    Build override required: W_BUF_DEPTH=256 (default is 128) so the
    256-beat W burst fits in w_buf — the wr CAM only accepts the entry
    after wlast, so the drain can't start consuming until then.
    """
    import cocotb
    from cocotb.triggers import RisingEdge

    BEATS_PER_BURST   = 256
    NUM_BURSTS        = 3
    TARGET_RUN_CYCLES = 200   # 2us @ 100MHz
    base_addr         = 0x0001_0000

    # Hand off from slow stubs to fast drains
    tb.wr_stub_paused      = True
    tb.rd_stub_paused      = True
    tb.fast_drain_enabled  = True

    aw      = tb.axi_master_wr.aw_channel
    w_ch    = tb.axi_master_wr.w_channel
    ar      = tb.axi_master_rd.ar_channel
    full_strb = (1 << (tb.AXI_DATA_WIDTH // 8)) - 1
    id_mask = (1 << tb.AXI_ID_WIDTH) - 1

    # Warmup write so the BFM's first-call cold start is past us
    await tb.axi_write(base_addr - 0x10000,
                       [0xDEAD_0000 | i for i in range(8)],
                       axi_id=0xF)

    # Pre-populate mem so the rd drain has data to inject for each read
    for i in range(NUM_BURSTS):
        addr  = base_addr + i * (BEATS_PER_BURST * (tb.AXI_DATA_WIDTH // 8))
        beats = [((0x5A5A_0000_0000 | (i << 16) | b) & tb.AXI_DATA_MASK)
                 for b in range(BEATS_PER_BURST)]
        tb.mem.write(addr, beats)

    tb.reset_stall_counters()

    # ---------------- write stream: bulk-queue AW + W ----------------
    for i in range(NUM_BURSTS):
        addr  = base_addr + i * (BEATS_PER_BURST * (tb.AXI_DATA_WIDTH // 8))
        beats = [((0x5A5A_0000_0000 | (i << 16) | b) & tb.AXI_DATA_MASK)
                 for b in range(BEATS_PER_BURST)]

        # AW: single packet, awlen = beats-1
        aw_pkt = aw.create_packet(
            addr=addr, len=BEATS_PER_BURST - 1,
            id=i & id_mask, size=3, burst=1,
        )
        # Touch private state — `await aw.send(pkt)` would await the
        # handshake AND deassert valid; we want it to stay high through
        # the whole burst chain so we queue directly.
        aw.transmit_queue.append(aw_pkt)
        if aw.transmit_coroutine is None:
            aw.transmit_coroutine = cocotb.start_soon(aw._transmit_pipeline())

        # W: bulk-queue every beat of this burst
        for b in range(BEATS_PER_BURST):
            w_pkt = w_ch.create_packet(
                data=beats[b],
                last=1 if b == BEATS_PER_BURST - 1 else 0,
                strb=full_strb,
            )
            w_ch.transmit_queue.append(w_pkt)
        if w_ch.transmit_coroutine is None:
            w_ch.transmit_coroutine = cocotb.start_soon(w_ch._transmit_pipeline())

    # Drain AW + W pipelines
    while aw.transmit_coroutine is not None:
        await RisingEdge(tb.dut.mc_clk)
    while w_ch.transmit_coroutine is not None:
        await RisingEdge(tb.dut.mc_clk)

    # Let B responses settle
    for _ in range(100):
        await RisingEdge(tb.dut.mc_clk)

    # Capture write metrics before reads start
    w_run_max = tb.w_active_run_max
    w_total   = tb.w_active_cycles

    # ---------------- read stream: bulk-queue AR + inject ----------------
    # Use READ addresses disjoint from the WRITE range so reads take the
    # miss path through `rd_inject` (driven by our pipelined drain) instead
    # of the snarf path (driven by the intake's r_r_fwd_active FSM). This
    # is the channel that measures the rd_inject streaming path, which is
    # what we want to assert.
    read_base = base_addr + 0x10_0000   # 1 MiB above writes
    for i in range(NUM_BURSTS):
        addr  = read_base + i * (BEATS_PER_BURST * (tb.AXI_DATA_WIDTH // 8))
        beats = [((0xA5A5_0000_0000 | (i << 16) | b) & tb.AXI_DATA_MASK)
                 for b in range(BEATS_PER_BURST)]
        # Queue inject data ahead of AR so the rd drain has data ready.
        tb.mem.queue_inject(i & id_mask, beats)

        ar_pkt = ar.create_packet(
            addr=addr, len=BEATS_PER_BURST - 1,
            id=i & id_mask, size=3, burst=1,
        )
        ar.transmit_queue.append(ar_pkt)
        if ar.transmit_coroutine is None:
            ar.transmit_coroutine = cocotb.start_soon(ar._transmit_pipeline())

    while ar.transmit_coroutine is not None:
        await RisingEdge(tb.dut.mc_clk)

    # Drain R beats
    for _ in range(BEATS_PER_BURST * NUM_BURSTS + 200):
        await RisingEdge(tb.dut.mc_clk)

    # Restore default stubs (be polite to subsequent tests in the matrix)
    tb.fast_drain_enabled = False
    tb.wr_stub_paused     = False
    tb.rd_stub_paused     = False

    tb.log.info(
        f"perfect_streaming results: "
        f"W active={tb.w_active_cycles}, run_max={tb.w_active_run_max} (write phase ran {w_total}/{w_run_max}); "
        f"R active={tb.r_active_cycles}, run_max={tb.r_active_run_max} "
        f"(rd_inject internal run_max={tb.rd_inject_active_run_max}); "
        f"stalls: AW={tb.aw_stall_cycles} AR={tb.ar_stall_cycles} "
        f"W={tb.w_stall_cycles}(run≤{tb.w_stall_run_max})"
    )

    # --- assertions ----------------------------------------------------
    # AW / AR — skid buffers absorb everything under ideal drain.
    assert tb.aw_stall_cycles == 0, (
        f"AW stalled {tb.aw_stall_cycles} cycles under ideal drain "
        f"(longest run {tb.aw_stall_run_max})."
    )
    assert tb.ar_stall_cycles == 0, (
        f"AR stalled {tb.ar_stall_cycles} cycles under ideal drain "
        f"(longest run {tb.ar_stall_run_max})."
    )
    # W — only the burst_done window allows wready low, never multi-cycle.
    assert tb.w_stall_run_max <= 1, (
        f"W stalled contiguously {tb.w_stall_run_max} cycles "
        "(expected ≤1 — intake burst_done window)."
    )

    # --- the headline assertions: >= 2us contiguous streaming ----------
    # W: (wvalid && wready) must remain 1 for at least TARGET_RUN_CYCLES.
    assert w_run_max >= TARGET_RUN_CYCLES, (
        f"W did not sustain (wvalid & wready)=1 for 2us. "
        f"Longest run in the write phase was {w_run_max} cycles "
        f"({w_run_max * 10}ns), needed ≥ {TARGET_RUN_CYCLES} cycles "
        f"({TARGET_RUN_CYCLES * 10}ns)."
    )
    # R: (rvalid && rready) must remain 1 for at least TARGET_RUN_CYCLES.
    assert tb.r_active_run_max >= TARGET_RUN_CYCLES, (
        f"R did not sustain (rvalid & rready)=1 for 2us. "
        f"Longest run was {tb.r_active_run_max} cycles "
        f"({tb.r_active_run_max * 10}ns), needed ≥ {TARGET_RUN_CYCLES} cycles "
        f"({TARGET_RUN_CYCLES * 10}ns)."
    )

    tb.log.info(
        f"perfect_streaming PASS — W run_max={w_run_max} "
        f"({w_run_max * 10}ns), R run_max={tb.r_active_run_max} "
        f"({tb.r_active_run_max * 10}ns), both ≥ 2us target."
    )


# ---------------------------------------------------------------------------
# Pytest wrapper — TEST_LEVEL controls matrix density
# ---------------------------------------------------------------------------

# (test_type, num_ranks, timing_profile)
# Note: perfect_streaming is `backtoback`-only on purpose — it measures
# the intake's intrinsic handshake budget under ideal drain. Other
# profiles would inject master-side stalls that the test isn't about.
_GATE = [
    ("forward_smoke",       1, "backtoback"),
    ("miss_smoke",          1, "backtoback"),
    ("snarf_timing_schmoo", 1, "backtoback"),
    ("perfect_streaming",   1, "backtoback"),
]

_FUNC = _GATE + [
    ("random_directed",     1, "backtoback"),
    ("addr_space_sweep",    1, "backtoback"),
    ("scheme_sweep",        1, "backtoback"),
    ("partial_strb",        1, "backtoback"),
    ("burst_len_sweep",     1, "backtoback"),
    # one timing-profile variation for sensitivity
    ("forward_smoke",       1, "fast"),
    ("random_directed",     1, "constrained"),
]

_FULL = _FUNC + [
    # broader timing profile coverage
    ("snarf_timing_schmoo", 1, "fast"),
    ("snarf_timing_schmoo", 1, "constrained"),
    ("addr_space_sweep",    1, "fast"),
    ("burst_len_sweep",     1, "constrained"),
    ("random_directed",     1, "burst_pause"),
]

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type,num_ranks,timing_profile", _PARAMS,
                         ids=[f"{t[0]}-nr{t[1]}-{t[2]}" for t in _PARAMS])
def test_axi_frontend_macro(request, test_type, num_ranks, timing_profile):
    """Pytest wrapper. SV NUM_RANKS controls the macro build; TIMING_PROFILE
    selects an AXI_RANDOMIZER_CONFIGS profile."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "axi_frontend_macro"
    test_name = (
        f"test_axi_frontend_macro_{test_type}_nr{num_ranks}_{timing_profile}"
    )

    filelist_path = (
        "projects/components/memory-controllers/ddr2-lpddr2/"
        "rtl/filelists/macro/axi_frontend_macro.f"
    )
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path
    )

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)

    log_path     = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")

    extra_env = {
        "DUT":               dut_name,
        "LOG_PATH":          log_path,
        "COCOTB_LOG_LEVEL":  "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        "SEED":              str(random.randint(0, 100000)),
        "TEST_TYPE":         test_type,
        "TIMING_PROFILE":    timing_profile,
        "AXI_DATA_WIDTH":    "64",
        "AXI_ID_WIDTH":      "4",
        "AXI_ADDR_WIDTH":    "32",
        "AXI_USER_WIDTH":    "1",
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET"]
    sim_args = []
    plus_args = []
    if enable_waves:
        # FST is faster + ~10× more compact than VCD on Verilator.
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args   += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args  += ["--trace"]
        extra_env["VERILATOR_TRACE"] = "1"
        extra_env["VERILATOR_TRACE_FST"] = "1"

    parameters = {"NUM_RANKS": str(num_ranks)}
    # perfect_streaming uses one 256-beat burst per side; w_buf default
    # of 128 would overflow before wlast lands and the wr CAM accepts
    # the entry. Widen for this scenario only.
    if test_type == "perfect_streaming":
        parameters["W_BUF_DEPTH"] = "512"

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_axi_frontend",
        sim_build=sim_build,
        simulator="verilator",
        extra_env=extra_env,
        parameters=parameters,
        compile_args=compile_args,
        sim_args=sim_args,
        plus_args=plus_args,
        waves=enable_waves,
        keep_files=True,
        timescale="1ns/1ps",
    )
