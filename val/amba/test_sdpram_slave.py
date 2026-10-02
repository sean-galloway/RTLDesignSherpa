#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# FUB-level test for rtl/amba/shared/sdpram_slave.sv — exercises the
# unified BRAM slave at both AXI4 and AXIL protocol selections, and
# (in AXI4 mode) verifies the new burst support (INCR + FIXED) added
# on top of the predecessor's single-beat behaviour.
#
# Phases:
#   1. single_beat        — 1-beat AW/W/B + AR/R round-trip
#   2. axi4_incr_burst    — INCR burst write + read (AXI4 only)
#   3. axi4_fixed_burst   — FIXED burst write (last beat wins) + read
#                           (AXI4 only)
#   4. random_fill_check  — fill memory single-beat, read back
#
# AXIL configurations exercise phases 1 and 4 only — the burst phases
# are skipped at runtime because the AXIL skid ties awlen/arlen to 0.

import os
import random
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ReadOnly
import pytest

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from cocotb_test.simulator import run


_repo_root = os.environ.get("REPO_ROOT")
if not _repo_root:
    cand = Path(__file__).resolve().parent
    while cand != Path("/") and not (cand / ".git").is_dir():
        cand = cand.parent
    if (cand / ".git").is_dir():
        _repo_root = str(cand)
if not _repo_root:
    raise RuntimeError("REPO_ROOT not set. Source env_python first.")


CLK_PERIOD_NS = 10


# ============================================================================
# Driver helpers — drive the full AXI4-shape s_axi_* ports. In AXIL mode the
# AXI4-only fields (id/len/size/burst/lock/cache/qos/region/user) are
# ignored by the wrapper, so always driving 0 is safe.
# ============================================================================

async def _reset(dut, cycles: int = 10) -> None:
    dut.aresetn.value = 0
    for sig in (
        "s_axi_awid", "s_axi_awaddr", "s_axi_awlen", "s_axi_awsize",
        "s_axi_awburst", "s_axi_awlock", "s_axi_awcache", "s_axi_awprot",
        "s_axi_awqos", "s_axi_awregion", "s_axi_awuser", "s_axi_awvalid",
        "s_axi_wdata", "s_axi_wstrb", "s_axi_wlast", "s_axi_wuser",
        "s_axi_wvalid", "s_axi_bready",
        "s_axi_arid", "s_axi_araddr", "s_axi_arlen", "s_axi_arsize",
        "s_axi_arburst", "s_axi_arlock", "s_axi_arcache", "s_axi_arprot",
        "s_axi_arqos", "s_axi_arregion", "s_axi_aruser", "s_axi_arvalid",
        "s_axi_rready",
        "i_cfg_start_clear",
    ):
        try:
            getattr(dut, sig).value = 0
        except Exception:
            pass
    for _ in range(cycles):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    await RisingEdge(dut.aclk)


async def _axi_write_burst(dut, addr, beats, size_log2, burst_type, awid=0,
                           strb=None) -> int:
    """
    Drive a write burst. `beats` is a list of data words; `size_log2` is the
    AXI awsize (log2 of bytes-per-beat); `burst_type` is 0=FIXED, 1=INCR,
    2=WRAP. Returns BRESP.
    """
    n = len(beats)
    full_strb = (1 << (len(dut.s_axi_wdata.value) // 8)) - 1
    if strb is None:
        strb = full_strb

    dut.s_axi_awid.value     = awid
    dut.s_axi_awaddr.value   = addr
    dut.s_axi_awlen.value    = n - 1
    dut.s_axi_awsize.value   = size_log2
    dut.s_axi_awburst.value  = burst_type
    dut.s_axi_awvalid.value  = 1
    dut.s_axi_bready.value   = 1

    # AW handshake
    while True:
        await ReadOnly()
        if int(dut.s_axi_awvalid.value) and int(dut.s_axi_awready.value):
            await RisingEdge(dut.aclk)
            dut.s_axi_awvalid.value = 0
            break
        await RisingEdge(dut.aclk)

    # Walk W beats
    for i, data in enumerate(beats):
        dut.s_axi_wdata.value  = data
        dut.s_axi_wstrb.value  = strb
        dut.s_axi_wlast.value  = 1 if i == n - 1 else 0
        dut.s_axi_wvalid.value = 1
        while True:
            await ReadOnly()
            if int(dut.s_axi_wvalid.value) and int(dut.s_axi_wready.value):
                await RisingEdge(dut.aclk)
                dut.s_axi_wvalid.value = 0
                dut.s_axi_wlast.value  = 0
                break
            await RisingEdge(dut.aclk)

    # B handshake
    while True:
        await ReadOnly()
        if int(dut.s_axi_bvalid.value) and int(dut.s_axi_bready.value):
            bresp = int(dut.s_axi_bresp.value)
            await RisingEdge(dut.aclk)
            dut.s_axi_bready.value = 0
            return bresp
        await RisingEdge(dut.aclk)


async def _axi_read_burst(dut, addr, n_beats, size_log2, burst_type, arid=0):
    """
    Drive a read burst. Returns list of (rdata, rresp, rlast) tuples.
    """
    dut.s_axi_arid.value     = arid
    dut.s_axi_araddr.value   = addr
    dut.s_axi_arlen.value    = n_beats - 1
    dut.s_axi_arsize.value   = size_log2
    dut.s_axi_arburst.value  = burst_type
    dut.s_axi_arvalid.value  = 1
    dut.s_axi_rready.value   = 1

    while True:
        await ReadOnly()
        if int(dut.s_axi_arvalid.value) and int(dut.s_axi_arready.value):
            await RisingEdge(dut.aclk)
            dut.s_axi_arvalid.value = 0
            break
        await RisingEdge(dut.aclk)

    beats = []
    while len(beats) < n_beats:
        await ReadOnly()
        if int(dut.s_axi_rvalid.value) and int(dut.s_axi_rready.value):
            beats.append((
                int(dut.s_axi_rdata.value),
                int(dut.s_axi_rresp.value),
                int(dut.s_axi_rlast.value),
            ))
        await RisingEdge(dut.aclk)
    dut.s_axi_rready.value = 0
    return beats


# ============================================================================
# CocoTB test
# ============================================================================

@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_sdpram_slave(dut):
    cocotb.start_soon(Clock(dut.aclk, CLK_PERIOD_NS, units="ns").start())

    dw = int(os.environ.get("DUT_DATA_WIDTH", "64"))
    depth = int(os.environ.get("DUT_MEM_DEPTH", "64"))
    wr_proto = os.environ.get("DUT_WR_PROTOCOL", "AXI4")
    rd_proto = os.environ.get("DUT_RD_PROTOCOL", "AXI4")
    word_bytes = dw // 8
    size_log2 = (word_bytes - 1).bit_length()  # log2(bytes-per-beat)
    mask = (1 << dw) - 1

    await _reset(dut)
    log = dut._log
    log.info(
        f"sdpram_slave FUB: WR={wr_proto} RD={rd_proto} "
        f"DATA_WIDTH={dw} MEM_DEPTH={depth} word_bytes={word_bytes}"
    )

    # ------------------------------------------------------------------
    # Phase 1 — single-beat write then read (both AXI4 + AXIL paths)
    # ------------------------------------------------------------------
    log.info("Phase 1: single_beat")
    addr1 = 0x0
    data1 = 0xCAFEBABEDEADBEEF & mask
    bresp = await _axi_write_burst(dut, addr1, [data1], size_log2, burst_type=1)
    assert bresp == 0, f"single-beat BRESP={bresp:#b}"
    beats = await _axi_read_burst(dut, addr1, 1, size_log2, burst_type=1)
    assert beats[0][0] == data1, f"single-beat read 0x{beats[0][0]:x} != 0x{data1:x}"
    assert beats[0][1] == 0, f"single-beat RRESP={beats[0][1]:#b}"
    assert beats[0][2] == 1, "single-beat RLAST should be 1"
    log.info(f"  OK: data=0x{data1:x}")

    # ------------------------------------------------------------------
    # Phase 2 — AXI4 INCR burst (4 beats)
    # ------------------------------------------------------------------
    if wr_proto == "AXI4" and rd_proto == "AXI4":
        log.info("Phase 2: axi4_incr_burst (4 beats)")
        base = 4 * word_bytes
        burst_data = [
            (0x1111111100000000 | i) & mask for i in range(4)
        ]
        bresp = await _axi_write_burst(dut, base, burst_data, size_log2, burst_type=1)
        assert bresp == 0, f"INCR burst BRESP={bresp:#b}"
        beats = await _axi_read_burst(dut, base, 4, size_log2, burst_type=1)
        for i, (rdata, rresp, rlast) in enumerate(beats):
            expected = burst_data[i]
            assert rresp == 0, f"INCR beat {i} RRESP={rresp:#b}"
            assert rdata == expected, (
                f"INCR beat {i} addr=0x{base + i*word_bytes:x} "
                f"read 0x{rdata:x} != expected 0x{expected:x}"
            )
            expected_last = 1 if i == 3 else 0
            assert rlast == expected_last, (
                f"INCR beat {i}: rlast={rlast} expected {expected_last}"
            )
        log.info(f"  OK: 4-beat INCR round-trip at base=0x{base:x}")

    # ------------------------------------------------------------------
    # Phase 3 — AXI4 FIXED burst (4 beats to same address)
    # Last beat's value should be what stays in the BRAM.
    # ------------------------------------------------------------------
    if wr_proto == "AXI4" and rd_proto == "AXI4":
        log.info("Phase 3: axi4_fixed_burst")
        fixed_addr = 32 * word_bytes
        fixed_beats = [
            (0xAAAA000000000000 | (i * 0x10)) & mask for i in range(4)
        ]
        bresp = await _axi_write_burst(dut, fixed_addr, fixed_beats, size_log2,
                                       burst_type=0)
        assert bresp == 0, f"FIXED burst BRESP={bresp:#b}"
        # All 4 beats wrote to the same row — last beat wins.
        beats = await _axi_read_burst(dut, fixed_addr, 1, size_log2, burst_type=1)
        last_written = fixed_beats[-1]
        assert beats[0][0] == last_written, (
            f"FIXED last beat: read 0x{beats[0][0]:x} != expected 0x{last_written:x}"
        )
        log.info(f"  OK: FIXED burst, last beat 0x{last_written:x} retained")

    # ------------------------------------------------------------------
    # Phase 4 — stream stability stress: ready signals don't glitch
    # within a burst.
    #
    # Drives sustained back-to-back INCR bursts of length 8, holding
    # s_axi_wvalid / s_axi_rready stable through each burst. Samples
    # s_axi_wready and s_axi_rvalid every cycle from AW/AR accept to
    # the last beat and counts 1→0 transitions. The contract: once
    # wready (resp. rvalid) goes high inside a burst window, it stays
    # high until the burst's last beat is consumed.
    #
    # The clear FSM was gated on no-active-bursts as part of this
    # contract; this phase is the regression for that fix. AXI4-only.
    # ------------------------------------------------------------------
    if wr_proto == "AXI4" and rd_proto == "AXI4":
        log.info("Phase 4b: stream_stability_stress")

        STRESS_BURSTS = 16
        BEATS_PER_BURST = 8

        # ----- write side -----
        wready_dips_in_burst = 0
        wr_base = 16 * word_bytes

        for b in range(STRESS_BURSTS):
            base = (wr_base + b * BEATS_PER_BURST * word_bytes) % (depth * word_bytes)
            beats_data = [(0xC0DE000000000000 | ((b << 8) | i)) & mask
                          for i in range(BEATS_PER_BURST)]
            # AW phase
            dut.s_axi_awid.value     = 0
            dut.s_axi_awaddr.value   = base
            dut.s_axi_awlen.value    = BEATS_PER_BURST - 1
            dut.s_axi_awsize.value   = size_log2
            dut.s_axi_awburst.value  = 1
            dut.s_axi_awvalid.value  = 1
            dut.s_axi_bready.value   = 1
            while True:
                await ReadOnly()
                if int(dut.s_axi_awvalid.value) and int(dut.s_axi_awready.value):
                    await RisingEdge(dut.aclk)
                    dut.s_axi_awvalid.value = 0
                    break
                await RisingEdge(dut.aclk)

            # W phase — hold wvalid stable throughout. Sample wready
            # every cycle once it first rises.
            wready_was_high = False
            beat_idx = 0
            full_strb = (1 << (dw // 8)) - 1
            dut.s_axi_wdata.value  = beats_data[0]
            dut.s_axi_wstrb.value  = full_strb
            dut.s_axi_wlast.value  = 1 if BEATS_PER_BURST == 1 else 0
            dut.s_axi_wvalid.value = 1
            while beat_idx < BEATS_PER_BURST:
                await ReadOnly()
                wr = int(dut.s_axi_wready.value)
                if wr == 1:
                    if not wready_was_high:
                        wready_was_high = True
                elif wready_was_high:
                    wready_dips_in_burst += 1
                    wready_was_high = False  # only count one dip per re-rise
                handshake = int(dut.s_axi_wvalid.value) and wr
                await RisingEdge(dut.aclk)
                if handshake:
                    beat_idx += 1
                    if beat_idx < BEATS_PER_BURST:
                        dut.s_axi_wdata.value = beats_data[beat_idx]
                        dut.s_axi_wlast.value = 1 if beat_idx == BEATS_PER_BURST - 1 else 0
            dut.s_axi_wvalid.value = 0
            dut.s_axi_wlast.value  = 0

            # Drain B
            while True:
                await ReadOnly()
                if int(dut.s_axi_bvalid.value) and int(dut.s_axi_bready.value):
                    await RisingEdge(dut.aclk)
                    break
                await RisingEdge(dut.aclk)
            dut.s_axi_bready.value = 0

        assert wready_dips_in_burst == 0, (
            f"wready de-asserted mid-burst {wready_dips_in_burst} times "
            f"across {STRESS_BURSTS} bursts × {BEATS_PER_BURST} beats — "
            "slave isn't streaming"
        )
        log.info(
            f"  OK: wready stayed high through every burst across "
            f"{STRESS_BURSTS}×{BEATS_PER_BURST}={STRESS_BURSTS*BEATS_PER_BURST} beats"
        )

        # ----- read side -----
        rvalid_dips_in_burst = 0
        rd_base = wr_base
        for b in range(STRESS_BURSTS):
            base = (rd_base + b * BEATS_PER_BURST * word_bytes) % (depth * word_bytes)
            dut.s_axi_arid.value    = 0
            dut.s_axi_araddr.value  = base
            dut.s_axi_arlen.value   = BEATS_PER_BURST - 1
            dut.s_axi_arsize.value  = size_log2
            dut.s_axi_arburst.value = 1
            dut.s_axi_arvalid.value = 1
            dut.s_axi_rready.value  = 1
            while True:
                await ReadOnly()
                if int(dut.s_axi_arvalid.value) and int(dut.s_axi_arready.value):
                    await RisingEdge(dut.aclk)
                    dut.s_axi_arvalid.value = 0
                    break
                await RisingEdge(dut.aclk)

            rvalid_was_high = False
            beats_seen = 0
            while beats_seen < BEATS_PER_BURST:
                await ReadOnly()
                rv = int(dut.s_axi_rvalid.value)
                rr = int(dut.s_axi_rready.value)
                if rv == 1:
                    if not rvalid_was_high:
                        rvalid_was_high = True
                elif rvalid_was_high:
                    rvalid_dips_in_burst += 1
                    rvalid_was_high = False
                if rv and rr:
                    beats_seen += 1
                await RisingEdge(dut.aclk)
            dut.s_axi_rready.value = 0

        assert rvalid_dips_in_burst == 0, (
            f"rvalid de-asserted mid-burst {rvalid_dips_in_burst} times "
            f"across {STRESS_BURSTS} bursts — slave isn't streaming"
        )
        log.info(
            f"  OK: rvalid stayed high through every burst across "
            f"{STRESS_BURSTS}×{BEATS_PER_BURST}={STRESS_BURSTS*BEATS_PER_BURST} beats"
        )

    # ------------------------------------------------------------------
    # Phase 4c — burst pipelining: ZERO dead cycles at burst boundaries.
    #
    # Streams PIPE_BURSTS back-to-back INCR bursts on each channel with
    # the command for burst n+1 offered while burst n is in flight
    # (AW/AR driver coroutines), wvalid / rready held continuously, and
    # B consumed immediately (bready tied high). Asserts from the beat
    # handshake timestamps that every burst boundary is EXACTLY one
    # clock: burst n+1's first beat lands the cycle after burst n's
    # last. (The one stall this phase deliberately does not count is the
    # stream-start pipeline fill: the wrapper's registered leaf takes
    # two W beats into its skid while AW1 is still propagating to the
    # core, so a master streaming W from cycle 0 sees a single stall
    # inside the first burst window. That is pipeline latency, not a
    # boundary cost, and every board measurement includes it.)
    #
    # The contract after the sdpram_core burst-queue fix (2026-10-02,
    # Sean: the serialised-burst behaviour documented against amba
    # ISSUE-004 IS a bug): a burst boundary costs NOTHING. The old
    # single-tracker core fails this phase with >= 2 dead cycles per
    # write boundary and >= 1 per read boundary. AXI4-only.
    # ------------------------------------------------------------------
    if wr_proto == "AXI4" and rd_proto == "AXI4":
        log.info("Phase 4c: burst_pipelining")

        PIPE_BURSTS = 4
        PIPE_BEATS = 8
        total = PIPE_BURSTS * PIPE_BEATS
        full_strb = (1 << (dw // 8)) - 1
        pipe_data = [(0xB000000000000000 | i) & mask for i in range(total)]
        pipe_addrs = [((b * PIPE_BEATS) * word_bytes) % (depth * word_bytes)
                      for b in range(PIPE_BURSTS)]

        async def _drive_cmds(dut, is_write, addrs):
            for a in addrs:
                if is_write:
                    dut.s_axi_awaddr.value  = a
                    dut.s_axi_awlen.value   = PIPE_BEATS - 1
                    dut.s_axi_awsize.value  = size_log2
                    dut.s_axi_awburst.value = 1
                    dut.s_axi_awvalid.value = 1
                else:
                    dut.s_axi_araddr.value  = a
                    dut.s_axi_arlen.value   = PIPE_BEATS - 1
                    dut.s_axi_arsize.value  = size_log2
                    dut.s_axi_arburst.value = 1
                    dut.s_axi_arvalid.value = 1
                vld = dut.s_axi_awvalid if is_write else dut.s_axi_arvalid
                rdy = dut.s_axi_awready if is_write else dut.s_axi_arready
                while True:
                    await ReadOnly()
                    if int(vld.value) and int(rdy.value):
                        await RisingEdge(dut.aclk)
                        vld.value = 0
                        break
                    await RisingEdge(dut.aclk)

        async def _count_bs(dut, result):
            while True:
                await ReadOnly()
                if int(dut.s_axi_bvalid.value) and int(dut.s_axi_bready.value):
                    result[0] += 1
                await RisingEdge(dut.aclk)

        # ----- write side -----
        b_count = [0]
        aw_task = cocotb.start_soon(_drive_cmds(dut, True, pipe_addrs))
        b_task = cocotb.start_soon(_count_bs(dut, b_count))
        dut.s_axi_bready.value = 1

        # The contract under test is the BURST BOUNDARY: burst n+1's first
        # beat must land the cycle after burst n's last. The one dead cycle
        # this phase does NOT count is the stream-start pipeline fill: the
        # wrapper's registered leaf accepts two W beats into its skid while
        # AW1 is still propagating to the core, so a master streaming W from
        # cycle 0 sees a single stall cycle inside the first burst window
        # (present in the old core too, and in every board measurement).
        # Bubbles are therefore counted from beat PIPE_BEATS onward, and the
        # boundary gaps are checked exactly from the handshake timestamps.
        w_bubbles = 0
        w_hs_times = []
        for i in range(total):
            dut.s_axi_wdata.value  = pipe_data[i]
            dut.s_axi_wstrb.value  = full_strb
            dut.s_axi_wlast.value  = 1 if (i % PIPE_BEATS) == PIPE_BEATS - 1 else 0
            dut.s_axi_wvalid.value = 1
            while True:
                await ReadOnly()
                wr = int(dut.s_axi_wready.value)
                if len(w_hs_times) >= PIPE_BEATS and not wr:
                    w_bubbles += 1
                if int(dut.s_axi_wvalid.value) and wr:
                    w_hs_times.append(cocotb.utils.get_sim_time('ns'))
                    await RisingEdge(dut.aclk)
                    break
                await RisingEdge(dut.aclk)
        dut.s_axi_wvalid.value = 0
        dut.s_axi_wlast.value  = 0

        await aw_task
        while b_count[0] < PIPE_BURSTS:
            await RisingEdge(dut.aclk)
        b_task.kill()
        dut.s_axi_bready.value = 0

        assert len(w_hs_times) == total
        clk_ns = w_hs_times[1] - w_hs_times[0]
        for k in range(1, PIPE_BURSTS):
            gap = w_hs_times[k * PIPE_BEATS] - w_hs_times[k * PIPE_BEATS - 1]
            assert gap == clk_ns, (
                f"burst boundary {k - 1}->{k} cost "
                f"{gap / clk_ns - 1:.0f} dead cycles -- the burst boundary "
                "must be free (sdpram_core burst-queue fix)"
            )
        assert w_bubbles == 0, (
            f"write channel saw {w_bubbles} dead cycles after stream start "
            f"across {PIPE_BURSTS - 1} burst boundaries -- the burst "
            "boundary must be free (sdpram_core burst-queue fix)"
        )
        log.info(
            f"  OK: {total} write beats in {total} cycles across "
            f"{PIPE_BURSTS} bursts, zero dead cycles, {b_count[0]} B responses"
        )

        # ----- read side -----
        ar_task = cocotb.start_soon(_drive_cmds(dut, False, pipe_addrs))
        dut.s_axi_rready.value = 1

        r_bubbles = 0
        r_started = False
        r_seen = 0
        r_last_count = 0
        r_mismatch = 0
        r_hs_times = []
        while r_seen < total:
            await ReadOnly()
            rv = int(dut.s_axi_rvalid.value)
            if r_started and not rv:
                r_bubbles += 1
            if rv:
                r_started = True
                if int(dut.s_axi_rdata.value) != pipe_data[r_seen]:
                    r_mismatch += 1
                if int(dut.s_axi_rlast.value):
                    r_last_count += 1
                r_hs_times.append(cocotb.utils.get_sim_time('ns'))
                r_seen += 1
            await RisingEdge(dut.aclk)
        dut.s_axi_rready.value = 0
        await ar_task

        assert r_bubbles == 0, (
            f"read channel saw {r_bubbles} dead cycles across "
            f"{PIPE_BURSTS - 1} burst boundaries -- the burst boundary "
            "must be free (sdpram_core burst-queue fix)"
        )
        for k in range(1, PIPE_BURSTS):
            gap = r_hs_times[k * PIPE_BEATS] - r_hs_times[k * PIPE_BEATS - 1]
            assert gap == clk_ns, (
                f"read burst boundary {k - 1}->{k} cost "
                f"{gap / clk_ns - 1:.0f} dead cycles -- the burst boundary "
                "must be free (sdpram_core burst-queue fix)"
            )
        assert r_last_count == PIPE_BURSTS, (
            f"rlast count {r_last_count} != {PIPE_BURSTS}"
        )
        assert r_mismatch == 0, (
            f"{r_mismatch} pipelined read beats mismatched the written pattern"
        )
        log.info(
            f"  OK: {total} read beats in {total} cycles across "
            f"{PIPE_BURSTS} bursts, zero dead cycles, data exact"
        )

    # ------------------------------------------------------------------
    # Phase 5 — random single-beat fill, then read back
    # ------------------------------------------------------------------
    log.info("Phase 5: random_fill_check")
    random.seed(0xBEEF)
    expected = {}
    for i in range(depth):
        a = i * word_bytes
        d = random.randint(0, mask)
        expected[a] = d
    for a, d in expected.items():
        b = await _axi_write_burst(dut, a, [d], size_log2, burst_type=1)
        assert b == 0
    mismatch = 0
    for a, d_exp in expected.items():
        beats = await _axi_read_burst(dut, a, 1, size_log2, burst_type=1)
        if beats[0][0] != d_exp:
            mismatch += 1
    assert mismatch == 0, f"{mismatch} single-beat readbacks mismatched"
    log.info(f"  OK: {depth} entries round-tripped clean")

    log.info("ALL PHASES PASSED")


# ============================================================================
# pytest wrapper
# ============================================================================

@pytest.mark.parametrize(
    "wr_protocol,rd_protocol,data_width,mem_depth",
    [
        ("AXI4", "AXI4", 64,  64),
        # AXIL/AXIL, mixed AXI4/AXIL, and AXIL/AXI4 variants are
        # functionally exercised by sdpram_core through the AXI4/AXI4
        # path (same core). Dedicated drivers for the AXIL surface live
        # in the per-wrapper tests once those land; until then this
        # test covers only the AXI4 superset surface (s_axi_*).
        ("AXI4", "AXI4", 256, 32),
    ],
)
def test_sdpram_slave(request, wr_protocol, rd_protocol, data_width, mem_depth):
    """Pytest wrapper -- exercises sdpram_slave_axi4_axi4 (FUB + core)."""
    here = Path(__file__).resolve().parent
    tag = f"wr{wr_protocol}_rd{rd_protocol}_dw{data_width}_d{mem_depth}"
    sim_build = here / "local_sim_build" / f"sdpram_slave_{tag}"
    log_dir = here / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    sim_build.mkdir(parents=True, exist_ok=True)
    log_path = log_dir / f"sdpram_slave_{tag}.log"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=_repo_root,
        module='sdpram_slave_axi4_axi4')

    extra_env = {
        "DUT_DATA_WIDTH":   str(data_width),
        "DUT_MEM_DEPTH":    str(mem_depth),
        "DUT_WR_PROTOCOL":  wr_protocol,
        "DUT_RD_PROTOCOL":  rd_protocol,
        "LOG_PATH":         str(log_path),
        "COCOTB_LOG_LEVEL": "INFO",
        "SEED":             os.environ.get('SEED', str(random.randint(0, 100000))),
    }

    parameters = {
        "DATA_WIDTH":   data_width,
        "MEM_DEPTH":    mem_depth,
        "AXI_ID_WIDTH": 4,
    }

    run(
        python_search=[str(here)],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="sdpram_slave_axi4_axi4",
        module="test_sdpram_slave",
        testcase="cocotb_test_sdpram_slave",
        parameters=parameters,
        sim_build=str(sim_build),
        extra_env=extra_env,
        simulator=os.environ.get("SIM", "verilator"),
        keep_files=True,
        compile_args=[
            "-Wno-WIDTHEXPAND",
            "-Wno-WIDTHTRUNC",
            "-Wno-TIMESCALEMOD",
            "-Wno-DECLFILENAME",
            "-Wno-UNUSED",
            "-Wno-UNUSEDPARAM",
            "-Wno-CASEINCOMPLETE",
        ],
    )
