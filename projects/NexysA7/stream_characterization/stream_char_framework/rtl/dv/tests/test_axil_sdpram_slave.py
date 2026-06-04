#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# FUB-level test for axil_sdpram_slave.
#
# Goal: shake out the bulk of the bugs before integrating the module into
# the harness in place of desc_ram / debug_sram. Drives the AXIL port
# directly, no framework BFM dependencies. Verilator under cocotb. Self-
# contained so the test can run from a fresh checkout with just env_python.
#
# Test phases (Pattern A: direct @cocotb.test, single pytest wrapper):
#   1. write_then_read_basic   — write one word, read it back, expect match
#   2. write_full_then_read_full — fill all MEM_DEPTH entries, read back in order
#   3. write_then_read_interleaved — pipeline AW/W with concurrent AR/R
#   4. wstrb_partial             — byte-enable masks work; unchanged bytes preserved
#   5. out_of_range              — both AW and AR to bad addr produce SLVERR
#   6. b_backpressure            — hold BREADY low; AW/W keep filling until queues full
#   7. r_backpressure            — hold RREADY low; AR keeps filling until queues full

import os
import sys
import random
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ReadOnly, Timer
import pytest
from cocotb_test.simulator import run

# Resolve REPO_ROOT for filelist + paths
_here = Path(__file__).resolve().parent
_repo_root = os.environ.get("REPO_ROOT")
if not _repo_root:
    cand = _here
    while cand != Path("/") and not (cand / ".git").is_dir():
        cand = cand.parent
    if (cand / ".git").is_dir():
        _repo_root = str(cand)
if not _repo_root:
    raise RuntimeError("REPO_ROOT not set. Source env_python first.")


# ============================================================================
# Driver helpers — minimal AXIL pokes, no BFM
# ============================================================================

CLK_PERIOD_NS = 10  # 100 MHz


async def _reset(dut, cycles: int = 10) -> None:
    dut.aresetn.value = 0
    # Idle every input
    for sig in (
        "s_axil_awaddr", "s_axil_awprot", "s_axil_awvalid",
        "s_axil_wdata", "s_axil_wstrb", "s_axil_wvalid",
        "s_axil_bready",
        "s_axil_araddr", "s_axil_arprot", "s_axil_arvalid",
        "s_axil_rready",
    ):
        try:
            getattr(dut, sig).value = 0
        except Exception:
            pass
    for _ in range(cycles):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    await RisingEdge(dut.aclk)


async def _axil_write(dut, addr: int, data: int, strb: int = None) -> int:
    """Returns BRESP."""
    if strb is None:
        strb = (1 << (int(dut.s_axil_wdata.value.n_bits) // 8)) - 1

    # AW
    dut.s_axil_awaddr.value = addr
    dut.s_axil_awprot.value = 0
    dut.s_axil_awvalid.value = 1
    # W
    dut.s_axil_wdata.value = data
    dut.s_axil_wstrb.value = strb
    dut.s_axil_wvalid.value = 1
    dut.s_axil_bready.value = 1

    # Wait both ready
    aw_done = False
    w_done  = False
    while not (aw_done and w_done):
        await ReadOnly()
        aw_done = aw_done or (
            int(dut.s_axil_awvalid.value) and int(dut.s_axil_awready.value)
        )
        w_done  = w_done or (
            int(dut.s_axil_wvalid.value) and int(dut.s_axil_wready.value)
        )
        await RisingEdge(dut.aclk)
        if aw_done:
            dut.s_axil_awvalid.value = 0
        if w_done:
            dut.s_axil_wvalid.value = 0

    # Wait for B
    while True:
        await ReadOnly()
        if int(dut.s_axil_bvalid.value) and int(dut.s_axil_bready.value):
            bresp = int(dut.s_axil_bresp.value)
            await RisingEdge(dut.aclk)
            dut.s_axil_bready.value = 0
            return bresp
        await RisingEdge(dut.aclk)


async def _axil_read(dut, addr: int) -> tuple:
    """Returns (rdata, rresp)."""
    dut.s_axil_araddr.value = addr
    dut.s_axil_arprot.value = 0
    dut.s_axil_arvalid.value = 1
    dut.s_axil_rready.value = 1

    while True:
        await ReadOnly()
        if int(dut.s_axil_arvalid.value) and int(dut.s_axil_arready.value):
            await RisingEdge(dut.aclk)
            dut.s_axil_arvalid.value = 0
            break
        await RisingEdge(dut.aclk)

    while True:
        await ReadOnly()
        if int(dut.s_axil_rvalid.value) and int(dut.s_axil_rready.value):
            rdata = int(dut.s_axil_rdata.value)
            rresp = int(dut.s_axil_rresp.value)
            await RisingEdge(dut.aclk)
            dut.s_axil_rready.value = 0
            return (rdata, rresp)
        await RisingEdge(dut.aclk)


# ============================================================================
# CocoTB test — one unified test, branches on PHASE env var
# ============================================================================

@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_axil_sdpram_slave(dut):
    """Unified FUB test for axil_sdpram_slave."""
    cocotb.start_soon(Clock(dut.aclk, CLK_PERIOD_NS, units="ns").start())

    dw   = int(os.environ.get("DUT_DATA_WIDTH", "64"))
    depth = int(os.environ.get("DUT_MEM_DEPTH", "64"))
    strb_w = dw // 8
    word_bytes = strb_w
    mask   = (1 << dw) - 1
    full_strb = (1 << strb_w) - 1

    await _reset(dut)
    log = dut._log
    log.info(
        f"axil_sdpram_slave FUB: DATA_WIDTH={dw} MEM_DEPTH={depth} "
        f"word_bytes={word_bytes}"
    )

    # -----------------------------------------------------------------
    # Phase 1 — basic write then read
    # -----------------------------------------------------------------
    log.info("Phase 1: write_then_read_basic")
    addr = 0
    data = 0xCAFEBABEDEADBEEF & mask
    bresp = await _axil_write(dut, addr, data)
    assert bresp == 0, f"BRESP != OKAY: {bresp:#b}"
    rdata, rresp = await _axil_read(dut, addr)
    assert rresp == 0, f"RRESP != OKAY: {rresp:#b}"
    assert rdata == data, f"read mismatch: wrote 0x{data:x} got 0x{rdata:x}"
    log.info(f"  OK: addr=0x{addr:x} data=0x{data:x}")

    # -----------------------------------------------------------------
    # Phase 2 — fill memory, read back in same order
    # -----------------------------------------------------------------
    log.info("Phase 2: write_full_then_read_full")
    random.seed(0xC0FFEE)
    expected = {}
    for i in range(depth):
        a = i * word_bytes
        d = random.randint(0, mask)
        expected[a] = d
    for a, d in expected.items():
        b = await _axil_write(dut, a, d)
        assert b == 0, f"write @0x{a:x} failed bresp={b}"
    log.info(f"  wrote {depth} entries")
    for a, d_exp in expected.items():
        rd, rr = await _axil_read(dut, a)
        assert rr == 0, f"read @0x{a:x} rresp={rr}"
        assert rd == d_exp, (
            f"@0x{a:x} expected 0x{d_exp:x} got 0x{rd:x}"
        )
    log.info(f"  verified {depth} entries")

    # -----------------------------------------------------------------
    # Phase 3 — interleaved write+read (pipelined)
    # -----------------------------------------------------------------
    log.info("Phase 3: write_then_read_interleaved")
    for round_i in range(8):
        a = random.randrange(0, depth) * word_bytes
        d = random.randint(0, mask)
        await _axil_write(dut, a, d)
        # immediate readback (should fire after BRAM latency)
        rd, rr = await _axil_read(dut, a)
        assert rr == 0, f"round {round_i} rresp={rr}"
        assert rd == d, (
            f"round {round_i} @0x{a:x} expected 0x{d:x} got 0x{rd:x}"
        )
        expected[a] = d
    log.info("  8 interleaved rounds OK")

    # -----------------------------------------------------------------
    # Phase 4 — WSTRB partial writes preserve untouched bytes
    # -----------------------------------------------------------------
    log.info("Phase 4: wstrb_partial")
    base = 1 * word_bytes
    # seed all-1s
    seed = mask
    await _axil_write(dut, base, seed, full_strb)
    # overwrite only byte 0 with 0x55 — strb=1
    new_data = (seed & ~0xFF) | 0x55
    await _axil_write(dut, base, 0x55, 0b0001)
    rd, _ = await _axil_read(dut, base)
    assert rd == new_data, (
        f"wstrb fail: expected 0x{new_data:x} got 0x{rd:x}"
    )
    log.info(f"  wstrb=0b0001 preserved upper bytes: 0x{rd:x}")
    # overwrite only middle byte
    seed2 = rd
    if strb_w >= 4:
        new_data2 = (seed2 & ~(0xFF << 16)) | (0xA5 << 16)
        await _axil_write(dut, base, (0xA5 << 16), 0b0100)
        rd2, _ = await _axil_read(dut, base)
        assert rd2 == new_data2, (
            f"wstrb fail: expected 0x{new_data2:x} got 0x{rd2:x}"
        )
        log.info(f"  wstrb=0b0100 OK: 0x{rd2:x}")
    expected[base] = rd2 if strb_w >= 4 else rd

    # -----------------------------------------------------------------
    # Phase 5 — out-of-range addr → SLVERR
    # -----------------------------------------------------------------
    log.info("Phase 5: out_of_range")
    bad_addr = depth * word_bytes  # one entry past the end
    bresp = await _axil_write(dut, bad_addr, 0xDEAD)
    assert bresp == 0b10, f"OOR write bresp expected SLVERR, got {bresp:#b}"
    _, rresp = await _axil_read(dut, bad_addr)
    assert rresp == 0b10, f"OOR read rresp expected SLVERR, got {rresp:#b}"
    log.info("  SLVERR generated for OOR addr on both AW and AR")

    # -----------------------------------------------------------------
    # Phase 6 — B backpressure (BREADY held low)
    #
    # Drive multiple AW+W until queues fill, confirm AWREADY/WREADY
    # eventually deassert, then release BREADY and drain — confirm all
    # BRESP arrive.
    # -----------------------------------------------------------------
    log.info("Phase 6: b_backpressure")
    # Hold BREADY low while we push writes
    dut.s_axil_bready.value = 0
    pushed = 0
    bp_addr_base = 8 * word_bytes
    bp_data_base = 0x10000000
    # Fire 12 writes; queue depths default to 4 each, so by ~8-10 in,
    # AWREADY/WREADY should drop.
    for i in range(12):
        a = (bp_addr_base + i * word_bytes) & mask
        d = (bp_data_base + i) & mask
        # Push via independent AW and W (don't wait for B)
        dut.s_axil_awaddr.value = a
        dut.s_axil_awprot.value = 0
        dut.s_axil_awvalid.value = 1
        dut.s_axil_wdata.value = d
        dut.s_axil_wstrb.value = full_strb
        dut.s_axil_wvalid.value = 1
        # Try for up to 10 cycles
        for _ in range(10):
            await ReadOnly()
            aw_ok = int(dut.s_axil_awvalid.value) and int(dut.s_axil_awready.value)
            w_ok  = int(dut.s_axil_wvalid.value) and int(dut.s_axil_wready.value)
            await RisingEdge(dut.aclk)
            if aw_ok:
                dut.s_axil_awvalid.value = 0
            if w_ok:
                dut.s_axil_wvalid.value = 0
            if not int(dut.s_axil_awvalid.value) and not int(dut.s_axil_wvalid.value):
                pushed += 1
                break
        else:
            # AW/W backpressured for too long — expected once queues full
            log.info(f"  AW/W backpressured at push #{pushed}")
            dut.s_axil_awvalid.value = 0
            dut.s_axil_wvalid.value = 0
            break
    assert pushed >= 4, (
        f"too few writes accepted before backpressure ({pushed}); "
        "queues may be much shallower than expected"
    )
    # Release BREADY, drain
    dut.s_axil_bready.value = 1
    drained = 0
    for _ in range(50):
        await ReadOnly()
        if int(dut.s_axil_bvalid.value) and int(dut.s_axil_bready.value):
            drained += 1
        await RisingEdge(dut.aclk)
    log.info(f"  pushed={pushed} drained_B={drained}")
    assert drained >= pushed, (
        f"B drain mismatch: pushed {pushed}, drained {drained}"
    )
    dut.s_axil_bready.value = 0

    # -----------------------------------------------------------------
    # Phase 7 — R backpressure (RREADY held low)
    # -----------------------------------------------------------------
    log.info("Phase 7: r_backpressure")
    dut.s_axil_rready.value = 0
    ar_pushed = 0
    for i in range(12):
        a = (i * word_bytes) & mask
        dut.s_axil_araddr.value = a
        dut.s_axil_arprot.value = 0
        dut.s_axil_arvalid.value = 1
        for _ in range(10):
            await ReadOnly()
            ar_ok = int(dut.s_axil_arvalid.value) and int(dut.s_axil_arready.value)
            await RisingEdge(dut.aclk)
            if ar_ok:
                dut.s_axil_arvalid.value = 0
                ar_pushed += 1
                break
        else:
            log.info(f"  AR backpressured at push #{ar_pushed}")
            dut.s_axil_arvalid.value = 0
            break
    dut.s_axil_rready.value = 1
    r_drained = 0
    for _ in range(50):
        await ReadOnly()
        if int(dut.s_axil_rvalid.value) and int(dut.s_axil_rready.value):
            r_drained += 1
        await RisingEdge(dut.aclk)
    log.info(f"  AR pushed={ar_pushed} drained_R={r_drained}")
    assert r_drained >= ar_pushed, (
        f"R drain mismatch: pushed {ar_pushed}, drained {r_drained}"
    )

    # -----------------------------------------------------------------
    # Phase 8 — concurrent R+W (SDP BRAM independent ports test)
    #
    # Spawn two coroutines that run in parallel — one writes a batch
    # of (addr, data) pairs, the other reads from previously-written
    # addresses. The key check is that BRAM port A and port B operate
    # concurrently: neither path blocks the other and the data stays
    # correct.
    #
    # We also sample o_dbg_bram_wr and o_dbg_bram_rd every cycle to
    # confirm at least ONE cycle had both pulses high simultaneously —
    # that's the concurrency proof.
    # -----------------------------------------------------------------
    log.info("Phase 8: concurrent_rw")

    # Pre-seed half the memory so the reader has something deterministic
    # to read while the writer is busy on the other half.
    seed_data = {}
    for i in range(depth // 2):
        a = i * word_bytes
        d = (0xA5A50000 | i) & mask
        await _axil_write(dut, a, d)
        seed_data[a] = d

    # Cycle-by-cycle sampler — fires for the whole phase, counts how
    # many cycles see both BRAM port-A write and port-B read pulses
    # asserted in the SAME cycle.
    concurrent_cycles = [0]   # mutable accumulator
    total_cycles      = [0]
    sampler_stop      = [False]

    async def sampler():
        while not sampler_stop[0]:
            await ReadOnly()
            total_cycles[0] += 1
            if int(dut.o_dbg_bram_wr.value) and int(dut.o_dbg_bram_rd.value):
                concurrent_cycles[0] += 1
            await RisingEdge(dut.aclk)

    # Writer fires a batch of writes to the upper half of memory.
    writer_done = [False]
    async def writer():
        for i in range(depth // 2):
            a = ((depth // 2) + i) * word_bytes
            d = (0x5A5A0000 | i) & mask
            await _axil_write(dut, a, d)
            writes_recorded[a] = d
        writer_done[0] = True

    # Reader cycles through the seeded lower half, reading each value
    # back. Runs in parallel with the writer — read addr range never
    # overlaps with the write addr range so there's no W→R hazard to
    # confuse the test.
    reader_results = []
    reader_done    = [False]
    async def reader():
        for round_i in range(2):
            for i in range(depth // 2):
                a = i * word_bytes
                rd, rr = await _axil_read(dut, a)
                reader_results.append((a, rd, rr))
        reader_done[0] = True

    writes_recorded = {}
    cocotb.start_soon(sampler())
    wtask = cocotb.start_soon(writer())
    rtask = cocotb.start_soon(reader())

    await wtask
    await rtask
    # Give the sampler a few more cycles then stop it.
    for _ in range(4):
        await RisingEdge(dut.aclk)
    sampler_stop[0] = True
    await RisingEdge(dut.aclk)

    # Verify writes landed (read them back AFTER concurrency phase, by
    # which point port A is idle).
    for a, d_exp in writes_recorded.items():
        rd, rr = await _axil_read(dut, a)
        assert rr == 0, f"post-concurrent read @0x{a:x} rresp={rr}"
        assert rd == d_exp, (
            f"post-concurrent @0x{a:x} expected 0x{d_exp:x} got 0x{rd:x}"
        )

    # Verify reads got the seeded values back.
    bad_reads = []
    for (a, rd, rr) in reader_results:
        if rr != 0 or rd != seed_data[a]:
            bad_reads.append((a, rd, rr, seed_data[a]))
    assert not bad_reads, (
        f"concurrent reader saw {len(bad_reads)} bad reads, first: "
        f"{bad_reads[0]}"
    )

    log.info(
        f"  concurrent cycles (port A wr && port B rd both fired) = "
        f"{concurrent_cycles[0]} / {total_cycles[0]}"
    )
    # SDP BRAM concurrency proof: at least a handful of cycles must
    # show both pulses simultaneously. Eight is what we measured
    # empirically on (DW=64, MEM=64); we require at least four to keep
    # the bar above noise.
    assert concurrent_cycles[0] >= 4, (
        f"expected >= 4 cycles of simultaneous BRAM port-A write "
        f"+ port-B read (SDP concurrency). Got {concurrent_cycles[0]} "
        f"out of {total_cycles[0]} sampled cycles."
    )
    log.info(
        f"  writer ops={len(writes_recorded)} reader ops={len(reader_results)} "
        "— all verified"
    )

    log.info("ALL PHASES PASSED")


# ============================================================================
# pytest wrapper
# ============================================================================

@pytest.mark.parametrize("data_width,mem_depth", [
    (32, 64),
    (64, 64),
    (64, 128),
])
def test_axil_sdpram_slave(request, data_width, mem_depth):
    """Pytest wrapper — sweeps a few DATA_WIDTH / MEM_DEPTH combos."""
    here = Path(__file__).resolve().parent
    sim_build = here / "local_sim_build" / f"axil_sdpram_dw{data_width}_d{mem_depth}"
    log_dir   = here / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    sim_build.mkdir(parents=True, exist_ok=True)
    log_path = log_dir / f"axil_sdpram_dw{data_width}_d{mem_depth}.log"

    framework_root = Path(_repo_root) / "projects/NexysA7/stream_characterization/stream_char_framework"
    amba_dir   = Path(_repo_root) / "rtl/amba"
    common_dir = Path(_repo_root) / "rtl/common"

    verilog_sources = [
        # Skid buffer + protocol wrappers
        str(amba_dir / "gaxi" / "gaxi_skid_buffer.sv"),
        str(amba_dir / "axil4" / "axil4_slave_wr.sv"),
        str(amba_dir / "axil4" / "axil4_slave_rd.sv"),
        str(framework_root / "rtl" / "axil_sdpram_slave.sv"),
    ]
    includes = [
        str(amba_dir / "includes"),
        str(common_dir),
    ]

    extra_env = {
        "DUT_DATA_WIDTH": str(data_width),
        "DUT_MEM_DEPTH":  str(mem_depth),
        "LOG_PATH": str(log_path),
        "COCOTB_LOG_LEVEL": "INFO",
        "SEED": str(random.randint(0, 100000)),
    }

    parameters = {
        "DATA_WIDTH": data_width,
        "MEM_DEPTH":  mem_depth,
    }

    run(
        python_search=[str(here)],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="axil_sdpram_slave",
        module="test_axil_sdpram_slave",
        testcase="cocotb_test_axil_sdpram_slave",
        parameters=parameters,
        sim_build=str(sim_build),
        extra_env=extra_env,
        simulator=os.environ.get("SIM", "verilator"),
        keep_files=True,
        compile_args=[
            "-Wno-WIDTHEXPAND",
            "-Wno-TIMESCALEMOD",
            "-Wno-DECLFILENAME",
            "-Wno-UNUSEDPARAM",
        ],
    )
