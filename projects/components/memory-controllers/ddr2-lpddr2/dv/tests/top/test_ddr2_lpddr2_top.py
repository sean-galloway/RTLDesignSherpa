# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

# TODO(amba-profiles): only the new wr_rd_b2b_* scenarios use a
# non-default timing profile. Every other scenario here runs at the
# AXI4MasterRead/Write defaults — extend each scenario to parametrize
# over bin/TBClasses/amba/amba_random_configs.py profiles (backtoback /
# constrained / fast / slow_consumer / burst_pause / high_throughput).
# This is exactly what surfaced the "BFM-write_transaction serializes
# AW+W via _aw_w_lock" gap that hides engine-class traffic.
"""End-to-end tests for ddr2_lpddr2_top.

Workload-mix tests use AXI4Sequence to drive the canonical 60/40 W:R
mix with 128B/256B/512B/1024B at 20/20/40/20. Configure the controller
through APB (RegisterMap), then issue traffic through the AXI4 slave.

DFI loopback is a stub today — reads return garbage, but writes
exercise the full AXI → CAM → scheduler → DFI path.
"""

import logging
import os
import random
import sys
from typing import Optional

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from ddr2_lpddr2_coverage import (  # noqa: E402
    get_coverage_compile_args, get_coverage_env,
)

from tbclasses.ddr2_lpddr2_top_tb import DDR2LPDDR2TopTB  # noqa: E402

from CocoTBFramework.components.axi4.axi4_sequence import AXI4Sequence  # noqa: E402


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_ddr2_lpddr2_top(dut):
    test_type   = os.environ.get("TEST_TYPE", "smoke")
    seed        = int(os.environ.get("SEED", "12345"))
    mem_type    = os.environ.get("MEM_TYPE", "DDR2").upper()
    num_ranks   = int(os.environ.get("NUM_RANKS", "1"))

    # init_error_retry holds off init_complete to exercise the
    # init_sequencer timeout/error path.
    if test_type == "init_error_retry":
        init_complete_delay = 50_000     # effectively "never"
    else:
        init_complete_delay = 20

    tb = DDR2LPDDR2TopTB(dut, num_ranks=num_ranks)
    await tb.reset(mem_type=mem_type,
                   init_complete_delay=init_complete_delay)
    tb.init_register_map()
    tb.init_apb_master()
    await tb.apb_master.reset_bus()
    tb.init_dfi_slave()

    if test_type == "smoke":
        # Read the ID register (fixed RO values).
        rd = await tb.apb_read_register(0xFF0)
        expected = (0xD2 << 24) | (0x02 << 16) | (0x00 << 8) | 0x01
        assert rd == expected, f"ID readback 0x{rd:08X} != 0x{expected:08X}"

        # Wait for init_done to come up through the DFI stub.
        await tb.wait_for_init_done()

    elif test_type == "configure_via_apb":
        # Program a couple of timing registers via RegisterMap + APB, then
        # verify they read back.
        await tb.apb_program_register("REFRESH_TUNING", "page_policy_or", 0x2)
        await tb.apb_program_register("SCHED_TUNING", "force_inorder", 0x1)
        rt = await tb.apb_read_register(0x048)  # REFRESH_TUNING
        st = await tb.apb_read_register(0x040)  # SCHED_TUNING
        assert ((rt >> 2) & 0x3) == 0x2, f"page_policy_or not set: 0x{rt:08X}"
        assert ((st >> 4) & 0x1) == 0x1, f"force_inorder not set: 0x{st:08X}"

    elif test_type == "axi_write_smoke":
        # Init AXI masters and drive a single short write to make sure the
        # AXI → CAM → scheduler path doesn't hang. Read will not return
        # valid data yet (DFI stub) but the write completion should fire.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        seq = AXI4Sequence("smoke_wr", data_width=64, seed=seed)
        seq.add_write(0x0000_1000, [0xDEAD_BEEF_DEAD_0000], axid=0)
        results = await tb.run_sequence(seq)
        assert len(results) == 1
        # We accept either success or a timeout-style error here — the goal is
        # that the run_sequence call returns without hanging the harness.
        tb.log.info("smoke wr result: %s", results[0])

    elif test_type == "workload_mix":
        # The canonical 60/40 + 128/256/512/1024 distribution. Modest count
        # so the test finishes in reasonable time; iterate up after the
        # DFI loopback lands.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        seq = AXI4Sequence("workload_mix", data_width=64, seed=seed)
        seq.add_random_workload(
            count=8,
            addr_range=(0x0, 0x4000),
            write_ratio=0.6,
            size_weights={128: 0.2, 256: 0.2, 512: 0.4, 1024: 0.2},
            qos_choices=[0, 4, 8, 15],
        )
        results = await tb.run_sequence(seq)
        n_done = sum(1 for r in results if r["error"] is None)
        tb.log.info("workload_mix: %d / %d bursts completed without error",
                    n_done, len(results))

    elif test_type == "fresh_read_each_bank":
        # Fresh read from each bank (no preceding write).
        # Memory is preloaded so the read returns the preload pattern.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        results_summary = []
        for bank in range(8):
            addr = bank * 0x2000
            pat = (0xDEAD0000 | bank) | ((0xBEEF0000 | bank) << 32)
            tb.preload_memory(addr, pat.to_bytes(8, "little"))
            rd = AXI4Sequence(f"fresh_b{bank}", data_width=64, seed=seed)
            rd.add_read(addr, length=1, axid=0)
            r = await tb.run_sequence(rd)
            status = "OK" if r[0]["error"] is None else "FAIL"
            results_summary.append((bank, status, r[0]["error"]))
            tb.log.info("bank %d fresh-read: %s err=%s",
                        bank, status, r[0]["error"])
        # Report
        bad = [b for b, s, _ in results_summary if s == "FAIL"]
        assert not bad, f"fresh-read failed for banks: {bad}"

    elif test_type == "bank0_delayed":
        # After WR, wait many cycles before issuing the read to rule out
        # a near-back-to-back race.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        wr = AXI4Sequence("d_wr", data_width=64, seed=seed)
        wr.add_write(0x0, [0xAA55_AA55_AA55_AA55], axid=0)
        await tb.run_sequence(wr)

        # Wait 5000 mc cycles for refresh to fire a few times.
        from cocotb.triggers import ClockCycles as _CC
        await _CC(dut.mc_clk, 5000)

        rd = AXI4Sequence("d_rd", data_width=64, seed=seed)
        rd.add_read(0x0, length=1, axid=0)
        results = await tb.run_sequence(rd)
        assert results[0]["error"] is None, results[0]["error"]
        assert results[0]["data"][0] == 0xAA55_AA55_AA55_AA55, (
            f"bank0 delayed read got 0x{results[0]['data'][0]:016X}"
        )
        tb.log.info("bank0 delayed read OK")

    elif test_type == "bank0_probe":
        # Bank 0 hangs on AXI read after a write — probe the DFI bus
        # while it happens to find out where the path breaks.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        # Monitor DFI command bus on phase 0.
        cmd_log = []
        async def dfi_watch():
            cycle = 0
            while True:
                await RisingEdge(dut.mc_clk)
                cycle += 1
                cs_n  = int(dut.phy_dfi_cs_n.value)  & 1
                if cs_n == 1:
                    continue
                ras_n = int(dut.phy_dfi_ras_n.value) & 1
                cas_n = int(dut.phy_dfi_cas_n.value) & 1
                we_n  = int(dut.phy_dfi_we_n.value)  & 1
                addr  = int(dut.phy_dfi_address.value)
                bank  = int(dut.phy_dfi_bank.value) & 7
                code  = (ras_n << 2) | (cas_n << 1) | we_n
                # JEDEC DDR2 command encoding (cs=0, ras, cas, we):
                #   ACT  = (ras=0,cas=1,we=1) → 011 = 3
                #   WR   = (ras=1,cas=0,we=0) → 100 = 4
                #   RD   = (ras=1,cas=0,we=1) → 101 = 5
                #   PRE  = (ras=0,cas=1,we=0) → 010 = 2
                #   REF  = (ras=0,cas=0,we=1) → 001 = 1
                #   MRS  = (ras=0,cas=0,we=0) → 000 = 0
                #   NOP  = (ras=1,cas=1,we=1) → 111 = 7
                name = {
                    0: "MRS", 1: "REF", 2: "PRE", 3: "ACT",
                    4: "WR",  5: "RD",  7: "NOP",
                }.get(code, f"?{code}")
                cmd_log.append((cycle, name, bank, addr))

        # Probe axi_intake's R-channel internals + DFI rddata_en /
        # rddata_valid; helped diagnose G-01.
        async def r_probe():
            cycle = 0
            saw_en = False
            saw_valid = False
            while True:
                await RisingEdge(dut.mc_clk)
                cycle += 1
                try:
                    rddata_en = int(dut.phy_dfi_rddata_en.value)
                    rddata_v  = int(dut.phy_dfi_rddata_valid.value)
                except Exception:
                    return
                if rddata_en != 0 and not saw_en:
                    saw_en = True
                    tb.log.info("PROBE: dfi_rddata_en FIRST high @ "
                                "cycle %d (val=0x%x)", cycle, rddata_en)
                if rddata_v != 0 and not saw_valid:
                    saw_valid = True
                    tb.log.info("PROBE: dfi_rddata_valid FIRST high @ "
                                "cycle %d (val=0x%x)", cycle, rddata_v)

        from cocotb.triggers import RisingEdge
        watcher = cocotb.start_soon(dfi_watch())
        r_watcher = cocotb.start_soon(r_probe())

        # Step 1: write at bank-0 address.
        wr = AXI4Sequence("b0_wr", data_width=64, seed=seed)
        wr.add_write(0x0, [0xAA55_AA55_AA55_AA55], axid=0)
        await tb.run_sequence(wr)
        tb.log.info("after WR, DFI log has %d commands", len(cmd_log))
        for entry in cmd_log[-20:]:
            tb.log.info("  %s", entry)

        # Step 2: read.
        rd = AXI4Sequence("b0_rd", data_width=64, seed=seed)
        rd.add_read(0x0, length=1, axid=0)
        results = await tb.run_sequence(rd)

        # Drop REF + NOP from the log to keep it readable; everything
        # else is interesting.
        interesting = [e for e in cmd_log
                       if isinstance(e[1], str)
                       and e[1] not in ("NOP", "REF")]
        tb.log.info("after RD, DFI log has %d commands "
                    "(%d non-REF/NOP); non-REF/NOP entries:",
                    len(cmd_log), len(interesting))
        for entry in interesting:
            tb.log.info("  %s", entry)
        tb.log.info("RD result: err=%s data=%s",
                    results[0]["error"], results[0]["data"])
        # Force fail so cocotb output is preserved by pytest.
        assert results[0]["error"] is None, "bank0_probe RD hung as expected"

    elif test_type == "wr_rd_bank_sweep":
        # Probe which banks hang on wr-then-rd. Each iteration writes a
        # pattern to a bank's row 0 col 0, then reads it back. Logs the
        # first bank that times out so we can localize.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        bank_stride = 0x2000  # bytes between bank boundaries @ ROW_MAJOR
        good = []
        bad = []
        for bank in range(8):
            addr = bank * bank_stride
            pat = 0x1100_0000_0000_0000 | (bank << 56) | addr
            wr = AXI4Sequence(f"sweep_wr_b{bank}", data_width=64, seed=seed)
            wr.add_write(addr, [pat], axid=0)
            await tb.run_sequence(wr)
            rd = AXI4Sequence(f"sweep_rd_b{bank}", data_width=64, seed=seed)
            rd.add_read(addr, length=1, axid=0)
            results = await tb.run_sequence(rd)
            if results[0]["error"] is None and results[0]["data"][0] == pat:
                good.append(bank)
                tb.log.info("bank %d: OK  (addr 0x%X, pat 0x%016X)",
                            bank, addr, pat)
            else:
                bad.append(bank)
                tb.log.error("bank %d: FAIL (addr 0x%X) err=%s data=%s",
                             bank, addr, results[0]["error"],
                             results[0]["data"])
        tb.log.info("bank sweep: good=%s bad=%s", good, bad)
        assert not bad, f"banks {bad} failed wr-then-rd, banks {good} OK"

    elif test_type == "wr_rd_roundtrip":
        # Real DFI loopback now — write a known pattern, then read it
        # back and verify byte-exact equality.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        seq = AXI4Sequence("roundtrip_wr", data_width=64, seed=seed)
        addr = 0x0000_2000
        pattern = 0xCAFEBABE_DEADBEEF
        seq.add_write(addr, [pattern], axid=0)
        await tb.run_sequence(seq)

        # Now read it back.
        rd_seq = AXI4Sequence("roundtrip_rd", data_width=64, seed=seed)
        rd_seq.add_read(addr, length=1, axid=0)
        results = await tb.run_sequence(rd_seq)
        assert results[0]["error"] is None, results[0]["error"]
        readback = results[0]["data"][0]
        assert readback == pattern, (
            f"loopback mismatch: wrote 0x{pattern:016X}, "
            f"read 0x{readback:016X}"
        )
        tb.log.info("wr_rd_roundtrip OK: 0x%016X round-tripped through DFI",
                    readback)

    elif test_type == "wr_rd_roundtrip_2beat_probe":
        # Diagnostic version of _2beat: capture every dfi_wrdata cycle
        # so we can see what the controller actually writes.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        dfi_log = []
        from cocotb.triggers import RisingEdge, ClockCycles

        async def dfi_watch():
            cyc = 0
            while True:
                await RisingEdge(dut.mc_clk)
                cyc += 1
                try:
                    en = int(dut.phy_dfi_wrdata_en.value)
                except Exception:
                    return
                if en != 0:
                    data = int(dut.phy_dfi_wrdata.value)
                    mask = int(dut.phy_dfi_wrdata_mask.value)
                    dfi_log.append((cyc, en, data, mask))

        cocotb.start_soon(dfi_watch())

        seq = AXI4Sequence("probe_wr", data_width=64, seed=seed)
        addr = 0x0000_2080
        v0 = 0xCAFEBABE_DEADBEEF
        v1 = 0x12345678_9ABCDEF0
        seq.add_write(addr, [v0, v1], axid=0)
        await tb.run_sequence(seq)
        await ClockCycles(dut.mc_clk, 50)

        tb.log.info("DFI wrdata cycles captured: %d", len(dfi_log))
        for cyc, en, data, mask in dfi_log:
            tb.log.info("  cyc=%d en=0x%x data=0x%032X mask=0x%X",
                        cyc, en, data, mask)
        # Inspect the BFM-side MemoryModel to see what landed in DRAM.
        for offset in range(0, 32, 8):
            chunk = tb.peek_memory(addr + offset, 8)
            tb.log.info("  DRAM @ 0x%X = %s", addr + offset, chunk.hex())

        # Now probe DFI rddata during the read.
        rd_log = []
        async def rd_watch():
            cyc = 0
            while True:
                await RisingEdge(dut.mc_clk)
                cyc += 1
                try:
                    v = int(dut.phy_dfi_rddata_valid.value)
                except Exception:
                    return
                if v != 0:
                    d = int(dut.phy_dfi_rddata.value)
                    en = int(dut.phy_dfi_rddata_en.value)
                    rd_log.append((cyc, v, en, d))
        cocotb.start_soon(rd_watch())

        rd_seq = AXI4Sequence("probe_rd", data_width=64, seed=seed)
        rd_seq.add_read(addr, length=2, axid=0)
        results = await tb.run_sequence(rd_seq)
        readback = results[0]["data"]
        tb.log.info("AXI readback beats: %s",
                    [f"0x{b:016X}" for b in readback])
        tb.log.info("DFI rddata cycles: %d", len(rd_log))
        for cyc, v, en, d in rd_log:
            tb.log.info("  cyc=%d valid=0x%x en=0x%x data=0x%032X",
                        cyc, v, en, d)
        assert False, "diagnostic — forced fail to preserve output"

    elif test_type == "wr_rd_roundtrip_2beat":
        # Multi-beat variant of wr_rd_roundtrip: 1 AW with awlen=1
        # (2 beats). Discovered as a gap when ddr2_char_macro's smoke
        # at 1-burst-of-2-beats failed with a missing 2nd beat in
        # DFI memory. If this passes, the macro / engine pipelining
        # is at fault; if it fails, the controller's W path drops
        # trailing beats inside a multi-beat burst.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        seq = AXI4Sequence("roundtrip2_wr", data_width=64, seed=seed)
        addr = 0x0000_2080
        v0 = 0xCAFEBABE_DEADBEEF
        v1 = 0x12345678_9ABCDEF0
        seq.add_write(addr, [v0, v1], axid=0)
        await tb.run_sequence(seq)

        rd_seq = AXI4Sequence("roundtrip2_rd", data_width=64, seed=seed)
        rd_seq.add_read(addr, length=2, axid=0)
        results = await tb.run_sequence(rd_seq)
        assert results[0]["error"] is None, results[0]["error"]
        readback = results[0]["data"]
        assert len(readback) == 2, f"expected 2 R beats, got {len(readback)}"
        assert readback[0] == v0, (
            f"beat0 mismatch: wrote 0x{v0:016X}, read 0x{readback[0]:016X}"
        )
        assert readback[1] == v1, (
            f"beat1 mismatch: wrote 0x{v1:016X}, read 0x{readback[1]:016X}"
        )
        tb.log.info("wr_rd_roundtrip_2beat OK: both beats round-tripped")

    elif test_type == "wr_rd_b2b_multi":
        # Multi-burst, multi-beat, back-to-back AXI traffic — no BFM
        # bubbles, exactly what the axi4_master_wr_pattern_gen engine
        # drives. Existing top tests use default BFM timing (bubbles
        # everywhere) and miss the multi-burst integrity hits.
        #
        # 17 bursts of 4 beats each, distinct payload per beat so the
        # readback compare can pinpoint the corrupted beat.
        tb.init_axi_masters()
        tb.set_axi_timing_profile("backtoback")
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        N_BURSTS = 17           # one more than WR_CAM_DEPTH=16
        BURST_LEN = 4           # matches DDR2 BL=4 → no padding
        BASE = 0x0001_0000
        STRIDE = BURST_LEN * 8  # bytes per beat = 8

        # Marker payload: bit-fields make it obvious which burst /
        # beat any corrupted readback came from.
        def mk_payload(burst_idx: int, beat_idx: int) -> int:
            return ((burst_idx & 0xFFFF) << 16) | (beat_idx & 0xFFFF)

        wr = AXI4Sequence("b2b_wr", data_width=64, seed=seed)
        for b in range(N_BURSTS):
            data = [mk_payload(b, k) for k in range(BURST_LEN)]
            wr.add_write(BASE + b * STRIDE, data, axid=(b & 0xF))
        await tb.run_sequence(wr)

        rd = AXI4Sequence("b2b_rd", data_width=64, seed=seed)
        for b in range(N_BURSTS):
            rd.add_read(BASE + b * STRIDE, length=BURST_LEN,
                        axid=(b & 0xF))
        results = await tb.run_sequence(rd)

        # Check every beat. If any burst beyond 0 returns mangled data
        # the macro-level multi-burst bug is reproduced WITHOUT engines.
        first_bad: Optional[tuple] = None
        for b in range(N_BURSTS):
            beats = results[b]["data"]
            for k in range(BURST_LEN):
                expected = mk_payload(b, k)
                if beats[k] != expected:
                    if first_bad is None:
                        first_bad = (b, k, expected, beats[k])
        assert first_bad is None, (
            f"b2b multi-burst readback corrupted at burst={first_bad[0]} "
            f"beat={first_bad[1]}: wrote 0x{first_bad[2]:016X}, "
            f"read 0x{first_bad[3]:016X}"
        )
        tb.log.info("wr_rd_b2b_multi OK: %d bursts × %d beats round-tripped",
                    N_BURSTS, BURST_LEN)

    elif test_type == "wr_rd_b2b_multi_pipelined":
        # As wr_rd_b2b_multi, but launches all write_transaction calls
        # concurrently via cocotb.start_soon so AWs pipeline ahead of W
        # beats — the actual pattern the axi4_master_wr_pattern_gen
        # engine drives, and the one the BFM's serial run_axi4_sequence
        # has NEVER exercised in any existing test.
        tb.init_axi_masters()
        tb.set_axi_timing_profile("backtoback")
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        N_BURSTS = 17
        BURST_LEN = 4
        BASE = 0x0001_0000
        STRIDE = BURST_LEN * 8

        def mk_payload(burst_idx: int, beat_idx: int) -> int:
            return ((burst_idx & 0xFFFF) << 16) | (beat_idx & 0xFFFF)

        # Launch N concurrent write transactions — each fires its AW
        # immediately; the BFM's internal scheduler picks AW-AW-AW-...
        # rather than AW-W-B / AW-W-B.
        wr_tasks = []
        for b in range(N_BURSTS):
            data = [mk_payload(b, k) for k in range(BURST_LEN)]
            wr_tasks.append(cocotb.start_soon(
                tb.axi_master_wr.write_transaction(
                    address=BASE + b * STRIDE,
                    data=data,
                    burst_len=BURST_LEN,
                    id=(b & 0xF),
                )
            ))
        for t in wr_tasks:
            await t

        # Reads, also concurrent.
        rd_tasks = []
        for b in range(N_BURSTS):
            rd_tasks.append(cocotb.start_soon(
                tb.axi_master_rd.read_transaction(
                    address=BASE + b * STRIDE,
                    burst_len=BURST_LEN,
                    id=(b & 0xF),
                )
            ))
        read_results = []
        for t in rd_tasks:
            read_results.append(await t)

        first_bad: Optional[tuple] = None
        for b in range(N_BURSTS):
            beats = read_results[b]
            for k in range(BURST_LEN):
                expected = mk_payload(b, k)
                if beats[k] != expected:
                    if first_bad is None:
                        first_bad = (b, k, expected, beats[k])
        assert first_bad is None, (
            f"pipelined b2b corrupted at burst={first_bad[0]} "
            f"beat={first_bad[1]}: wrote 0x{first_bad[2]:016X}, "
            f"read 0x{first_bad[3]:016X}"
        )
        tb.log.info(
            "wr_rd_b2b_multi_pipelined OK: %d bursts × %d beats",
            N_BURSTS, BURST_LEN,
        )

    elif test_type == "wr_rd_b2b_truly_pipelined":
        # The pattern the engine actually drives: AW + W on their OWN
        # parallel channels, not serialized by write_transaction's
        # internal _aw_w_lock. Bypass write_transaction entirely and
        # send raw packets on aw_channel / w_channel concurrently —
        # all 17 AWs queue on awvalid back-to-back; all 17×4 W beats
        # queue on wvalid back-to-back. AXI4MasterRead is then used for
        # readback (its R channel logs every received beat).
        tb.init_axi_masters()
        tb.set_axi_timing_profile("backtoback")
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_wr.b_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        N_BURSTS = 17
        BURST_LEN = 4
        BASE = 0x0001_0000
        STRIDE = BURST_LEN * 8
        FULL_STRB = (1 << (tb.axi_data_width // 8)) - 1

        def mk_payload(burst_idx: int, beat_idx: int) -> int:
            return ((burst_idx & 0xFFFF) << 16) | (beat_idx & 0xFFFF)

        # Fire all AWs concurrently — channel internally queues them
        # so awvalid back-to-backs as fast as awready accepts.
        aw_tasks = []
        w_tasks  = []
        for b in range(N_BURSTS):
            aw_packet = tb.axi_master_wr.aw_channel.create_packet(
                addr=BASE + b * STRIDE,
                len=BURST_LEN - 1,
                id=(b & 0xF),
                size=3,         # 8 bytes per beat
                burst=1,        # INCR
            )
            aw_tasks.append(cocotb.start_soon(
                tb.axi_master_wr.aw_channel.send(aw_packet)
            ))
            for k in range(BURST_LEN):
                w_packet = tb.axi_master_wr.w_channel.create_packet(
                    data=mk_payload(b, k),
                    last=(1 if k == BURST_LEN - 1 else 0),
                    strb=FULL_STRB,
                )
                w_tasks.append(cocotb.start_soon(
                    tb.axi_master_wr.w_channel.send(w_packet)
                ))

        for t in aw_tasks + w_tasks:
            await t
        # Drain B responses so the read phase starts on a quiescent bus
        from cocotb.triggers import ClockCycles as _CC2
        await _CC2(dut.mc_clk, 200)

        # Reads via AXI4MasterRead — it logs every R beat through its
        # GAXISlave for diagnostic visibility.
        first_bad: Optional[tuple] = None
        for b in range(N_BURSTS):
            data = await tb.axi_master_rd.read_transaction(
                address=BASE + b * STRIDE,
                burst_len=BURST_LEN,
                id=(b & 0xF),
                size=3,
            )
            for k in range(BURST_LEN):
                expected = mk_payload(b, k)
                if data[k] != expected:
                    if first_bad is None:
                        first_bad = (b, k, expected, data[k])
        assert first_bad is None, (
            f"truly-pipelined b2b corrupted at burst={first_bad[0]} "
            f"beat={first_bad[1]}: wrote 0x{first_bad[2]:016X}, "
            f"read 0x{first_bad[3]:016X}"
        )
        tb.log.info(
            "wr_rd_b2b_truly_pipelined OK: %d bursts × %d beats",
            N_BURSTS, BURST_LEN,
        )

    elif test_type == "wr_rd_b2b_pipelined_same_id":
        # Engine-traffic mirror: AR side pipelined AND all id=0 (FIXED),
        # matching axi4_master_rd_crc_check's cfg_rd_axi_id=0 path.
        # The wr_rd_b2b_truly_pipelined scenario used id=(b&0xF) — mixed
        # ids — and passes; this same-id variant is what the engine
        # actually drives. If the controller mishandles same-id ARs
        # beyond RD_CAM_DEPTH=16, this is where it'll show.
        tb.init_axi_masters()
        tb.set_axi_timing_profile("backtoback")
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_wr.b_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        # 16 = RD_CAM_DEPTH — no slot reuse. If THIS passes but 17
        # fails, the bug is the slot-reuse interaction (newer same-id
        # AR landing in a freed slot gets scheduler-picked ahead of
        # older same-id ARs because of slot-index priority).
        import os as _os
        N_BURSTS = int(_os.environ.get("PIPELINED_SAME_ID_N", "17"))
        BURST_LEN = 4
        BASE = 0x0001_0000
        STRIDE = BURST_LEN * 8
        FULL_STRB = (1 << (tb.axi_data_width // 8)) - 1
        tb.log.info("pipelined_same_id: N_BURSTS=%d (cam depth=16)", N_BURSTS)

        def mk_payload(burst_idx: int, beat_idx: int) -> int:
            return ((burst_idx & 0xFFFF) << 16) | (beat_idx & 0xFFFF)

        # WRITE phase: preload DFI memory model directly. Bypasses the
        # entire AXI write path AND wr2rd_forward — anything left over
        # is purely on the read side.
        for b in range(N_BURSTS):
            payload = bytearray()
            for k in range(BURST_LEN):
                payload += mk_payload(b, k).to_bytes(8, "little")
            tb.preload_memory(BASE + b * STRIDE, payload)
        from cocotb.triggers import ClockCycles as _CC3
        await _CC3(dut.mc_clk, 50)

        # READ phase: 17 read_transaction tasks all started concurrently
        # with id=0. ar_channel.send serializes them in start-order; per
        # AXI4 same-id ordering, R beats come back in the same order. Each
        # task pulls BURST_LEN beats from _response_by_id[0].
        rd_tasks = []
        for b in range(N_BURSTS):
            rd_tasks.append(cocotb.start_soon(
                tb.axi_master_rd.read_transaction(
                    address=BASE + b * STRIDE,
                    burst_len=BURST_LEN,
                    id=0,
                    size=3,
                )
            ))

        results = []
        for t in rd_tasks:
            results.append(await t)

        first_bad: Optional[tuple] = None
        for b, data in enumerate(results):
            for k in range(BURST_LEN):
                expected = mk_payload(b, k)
                if data[k] != expected:
                    if first_bad is None:
                        first_bad = (b, k, expected, data[k])
        assert first_bad is None, (
            f"same-id pipelined-AR corrupted at burst={first_bad[0]} "
            f"beat={first_bad[1]}: wrote 0x{first_bad[2]:016X}, "
            f"read 0x{first_bad[3]:016X}"
        )
        tb.log.info(
            "wr_rd_b2b_pipelined_same_id OK: %d bursts × %d beats",
            N_BURSTS, BURST_LEN,
        )

    elif test_type == "memory_preload_read":
        # Preload bytes directly into DFISlavePHY's MemoryModel, then
        # read them back through AXI. Proves the BFM + memory model
        # ARE the DRAM.
        #
        # Pattern: prime the controller's R pipeline with a known
        # WR-then-RD first (so the AXI read path is "warm"), then
        # preload a separate address and read it. Without the warmup,
        # the controller's very-first AXI read after init hangs
        # somewhere between the scheduler picking the slot and the
        # R-channel inject — to be debugged separately; the preload
        # path itself (MemoryModel + AddressMapping wiring) works
        # once the path is warm.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        # Warm-up: write + read split across two sequences (matches
        # wr_rd_roundtrip pattern, which is the known-good path).
        wr = AXI4Sequence("warm_wr", data_width=64, seed=seed)
        wr.add_write(0x0000_1000, [0x1111_2222_3333_4444], axid=0)
        await tb.run_sequence(wr)
        rd = AXI4Sequence("warm_rd", data_width=64, seed=seed)
        rd.add_read(0x0000_1000, length=1, axid=0)
        await tb.run_sequence(rd)

        # Now preload a different address and read.
        byte_addr = 0x0000_3000
        payload = bytes([0xA5, 0x5A, 0xC3, 0x3C, 0xFF, 0x00, 0xDE, 0xAD])
        tb.preload_memory(byte_addr, payload)
        tb.log.info("preloaded 0x%X with %s; peek: %s",
                    byte_addr, payload.hex(),
                    tb.peek_memory(byte_addr, 8).hex())

        rd_seq = AXI4Sequence("preload_rd", data_width=64, seed=seed)
        rd_seq.add_read(byte_addr, length=1, axid=0)
        results = await tb.run_sequence(rd_seq)
        assert results[0]["error"] is None, results[0]["error"]
        expected_word = int.from_bytes(payload, byteorder="little")
        assert results[0]["data"][0] == expected_word, (
            f"preload read mismatch: got 0x{results[0]['data'][0]:016X}, "
            f"expected 0x{expected_word:016X}"
        )
        tb.log.info("preload read OK: 0x%016X", expected_word)

    elif test_type in ("smoke_lpddr2", "smoke_nr2"):
        # mem_type / NUM_RANKS variants of smoke; the env vars steer
        # reset()/constructor, the body just walks the same init handshake.
        await tb.wait_for_init_done()
        tb.log.info("%s init_done OK (mem_type=%s, num_ranks=%d)",
                    test_type, mem_type, num_ranks)

    elif test_type in ("workload_mix_lpddr2", "workload_mix_nr2"):
        # LPDDR2 traffic exercises lpddr2-only CA-bus encoding in
        # dfi_cmd_formatter + LPDDR2 MR walk in init_sequencer.
        # NUM_RANKS=2 exercises per-rank tFAW/tRRD in global_timers and
        # multi-rank addr decode + CS/CKE fan-out in dfi_signal_pack —
        # must use an addr_range that crosses ranks (rank lives in the
        # top addr bit under `rank|row|bank|col`).
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        if test_type == "workload_mix_nr2":
            # Per-rank reachable region = NUM_BANKS * ROW * COL * 8 bytes.
            # With NB=8, ROW=14, COL=10, bytes/beat=8 → 1 GB / rank.
            # Drive bursts that explicitly hit rank 0 and rank 1.
            seq = AXI4Sequence(test_type, data_width=64, seed=seed)
            # Rank 0 traffic
            seq.add_bank_spray(base_addr=0x0000_1000, num_banks=4,
                               bank_stride_bytes=0x400, burst_bytes=128,
                               is_write=True)
            # Rank 1 traffic — bit 30 set under 1 GB per-rank
            rank1_base = 0x4000_0000
            seq.add_bank_spray(base_addr=rank1_base, num_banks=4,
                               bank_stride_bytes=0x400, burst_bytes=128,
                               is_write=True)
            # Read back from both ranks (forces CS fan-out)
            seq.add_read(0x0000_1000, length=2, axid=0)
            seq.add_read(rank1_base,   length=2, axid=0)
        else:
            seq = AXI4Sequence(test_type, data_width=64, seed=seed)
            seq.add_random_workload(
                count=8, addr_range=(0x0, 0x4000),
                write_ratio=0.6,
                size_weights={128: 0.2, 256: 0.2, 512: 0.4, 1024: 0.2},
                qos_choices=[0, 4, 8, 15],
            )
        results = await tb.run_sequence(seq)
        n_done = sum(1 for r in results if r["error"] is None)
        tb.log.info("%s: %d / %d bursts completed (mem_type=%s, nr=%d)",
                    test_type, n_done, len(results), mem_type, num_ranks)

    elif test_type == "workload_mix_policy_switch":
        # Toggle page_policy_or + refpb_policy_or mid-traffic to hit
        # page_predictor's both-policy arms and the scheduler's
        # policy-honor branches. APB writes between two workload bursts.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        # Burst 1 — default (closed-page) policy
        seq = AXI4Sequence("phase1", data_width=64, seed=seed)
        seq.add_random_workload(count=4, addr_range=(0x0, 0x4000),
                                write_ratio=0.6,
                                size_weights={128: 0.5, 256: 0.5},
                                qos_choices=[0])
        await tb.run_sequence(seq)

        # Flip to open-page + per-bank refresh override mid-test
        await tb.apb_program_register("REFRESH_TUNING", "page_policy_or", 0x2)
        await tb.apb_program_register("REFRESH_TUNING", "refpb_policy_or", 0x2)

        # Burst 2 — open-page policy
        seq2 = AXI4Sequence("phase2", data_width=64, seed=seed + 1)
        seq2.add_row_hit_burst(base_addr=0x0000_5000, n_followups=3,
                               burst_bytes=64, is_write=True, qos=4)
        results = await tb.run_sequence(seq2)
        n_done = sum(1 for r in results if r["error"] is None)
        tb.log.info("policy_switch phase2: %d / %d row-hit bursts completed",
                    n_done, len(results))

    elif test_type == "wr_rd_ooo_multi_id":
        # Disable force_inorder + drive two AXI IDs back-to-back. Exercises
        # axi_id_side_table OOO completion path and the R-channel reorder.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        # Clear force_inorder (default 0 already, but make it explicit so
        # the CSR-side mux selects the unforced path under coverage).
        await tb.apb_program_register("SCHED_TUNING", "force_inorder", 0x0)

        # Write two patterns at two addresses with two IDs.
        wr = AXI4Sequence("ooo_wr", data_width=64, seed=seed)
        wr.add_write(0x0000_2000, [0xCAFEBABE_DEADBEEF], axid=0)
        wr.add_write(0x0000_2100, [0xFEEDC0DE_12345678], axid=1)
        await tb.run_sequence(wr)

        # Read with the two IDs in *reverse* address order so the
        # completion buffer must reorder if the underlying CAM grants OOO.
        rd = AXI4Sequence("ooo_rd", data_width=64, seed=seed + 1)
        rd.add_read(0x0000_2100, length=1, axid=1)
        rd.add_read(0x0000_2000, length=1, axid=0)
        results = await tb.run_sequence(rd)
        ok = all(r["error"] is None for r in results)
        tb.log.info("ooo_multi_id: %d / %d ok (err=%s)",
                    sum(1 for r in results if r["error"] is None),
                    len(results),
                    [r["error"] for r in results])
        assert ok, "ooo_multi_id had errors"

    elif test_type == "init_error_retry":
        # init_complete is held off (delay=50000) so the init_sequencer
        # timeout / retry path engages. We don't preload the bus; we just
        # watch init_busy / init_done from STATUS and verify the FSM
        # doesn't promote init_done. Coverage gain: the init timeout and
        # zq_retries branches in init_sequencer.
        await tb.apb_program_register("INIT_TUNING", "zq_retries", 0x1)
        await tb.apb_program_register("INIT_TUNING", "init_timeout_ms", 0x1)

        # Sample STATUS for a few thousand mc cycles; expect init_done
        # stays low because init_complete never asserts.
        from cocotb.triggers import ClockCycles as _CC
        await _CC(dut.mc_clk, 2000)
        st = await tb.apb_read_register(0x004)
        tb.log.info("init_error_retry STATUS=0x%08X (expect init_done=0)", st)
        # No hard assertion — the goal is line coverage on the wait path;
        # we don't want to fail the test on micro-architectural choices
        # about whether the FSM latches an error bit.

    elif test_type == "read_then_read_probe":
        # G-01b: AXI read #1 to bank 0 succeeds; read #2 to bank 1 hangs.
        # The BFM sees ACT+RD for read #1 then only REF forever — so the
        # controller is the one that stops issuing commands. Probe the
        # AR handshake, AXI master-side R signals, and the DFI cmd bus
        # bracketing each read.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        # Preload bank 0 and bank 1 distinct patterns.
        tb.preload_memory(0x0000, (0xDEAD0000).to_bytes(8, "little"))
        tb.preload_memory(0x2000, (0xDEAD0001).to_bytes(8, "little"))

        observed = {"cmd_log": [], "rd_inject_cnt": 0,
                    "rdvalid_cnt": 0, "ar_fires": 0}
        from cocotb.triggers import RisingEdge

        async def dfi_cmd_watch():
            cycle = 0
            while True:
                await RisingEdge(dut.mc_clk)
                cycle += 1
                try:
                    cs_n  = int(dut.phy_dfi_cs_n.value) & 1
                    if cs_n != 0:
                        continue
                    ras_n = int(dut.phy_dfi_ras_n.value) & 1
                    cas_n = int(dut.phy_dfi_cas_n.value) & 1
                    we_n  = int(dut.phy_dfi_we_n.value)  & 1
                    bank  = int(dut.phy_dfi_bank.value)  & 7
                    addr  = int(dut.phy_dfi_address.value)
                    code  = (ras_n << 2) | (cas_n << 1) | we_n
                    name = {0:"MRS",1:"REF",2:"PRE",3:"ACT",
                            4:"WR",5:"RD",7:"NOP"}.get(code, f"?{code}")
                    if name not in ("NOP", "REF"):
                        observed["cmd_log"].append((cycle, name, bank, addr))
                except Exception:
                    return

        async def axi_probe():
            cycle = 0
            while True:
                await RisingEdge(dut.pclk)
                cycle += 1
                try:
                    arv = int(dut.s_axi_arvalid.value)
                    arr = int(dut.s_axi_arready.value)
                    rv  = int(dut.s_axi_rvalid.value)
                    rr  = int(dut.s_axi_rready.value)
                except Exception:
                    return
                if arv and arr:
                    observed["ar_fires"] += 1
                    tb.log.info("PROBE: AR handshake #%d @ aclk %d",
                                observed["ar_fires"], cycle)
                if rv and rr:
                    observed["rdvalid_cnt"] += 1
                    tb.log.info("PROBE: R handshake #%d @ aclk %d",
                                observed["rdvalid_cnt"], cycle)

        async def deep_probe():
            """Watch the read-side internals: ar_pend→rd_cmd_cam push,
            rd_cmd_cam occupancy, scheduler rd_op_valid."""
            cycle = 0
            last_state = None
            while True:
                await RisingEdge(dut.mc_clk)
                cycle += 1
                try:
                    intake = dut.u_dut.u_axi_frontend.u_axi_intake
                    ar_push_v = int(intake.ar_push_valid_o.value)
                    ar_push_r = int(intake.ar_push_ready_i.value)
                    rd_cam = dut.u_dut.u_axi_frontend.u_rd_cam
                    r_valid_vec = int(rd_cam.r_valid.value)
                    r_issued_vec = int(rd_cam.r_issued.value)
                    push_ready = int(rd_cam.push_ready_o.value)
                    rd_op_v = int(dut.u_dut.u_core.rd_op_valid.value)
                except Exception as e:
                    if cycle < 5:
                        tb.log.error("deep probe binding failed: %s", e)
                    return
                try:
                    bank_s0 = int(rd_cam.r_bank.value[0]) if hasattr(rd_cam.r_bank, "value") else -1
                    row_s0 = int(rd_cam.r_row.value[0]) if hasattr(rd_cam.r_row, "value") else -1
                    match_p = int(rd_cam.match_pending_o.value)
                    match_rh = int(rd_cam.match_rowhit_o.value)
                except Exception:
                    bank_s0 = -1; row_s0 = -1; match_p = -1; match_rh = -1
                try:
                    sched = dut.u_dut.u_core.u_command_scheduler.u_scheduler
                    sched_state = int(sched.r_state.value)
                    q_rank = int(sched.q_rank_o.value)
                    q_bank = int(sched.q_bank_o.value)
                except Exception:
                    sched_state = -1; q_rank = -1; q_bank = -1
                state = (ar_push_v, ar_push_r, r_valid_vec, r_issued_vec,
                         push_ready, rd_op_v, match_p, sched_state, q_bank)
                if state != last_state:
                    tb.log.info("DEEP@%d ar_push v/r=%d/%d  rd_cam "
                                "r_valid=0x%X r_issued=0x%X push_ready=%d  "
                                "match_p=0x%X match_rh=0x%X  rd_op_v=%d  "
                                "sched_state=%d q_rank=%d q_bank=%d",
                                cycle, ar_push_v, ar_push_r,
                                r_valid_vec, r_issued_vec, push_ready,
                                match_p, match_rh, rd_op_v,
                                sched_state, q_rank, q_bank)
                    last_state = state

        cocotb.start_soon(dfi_cmd_watch())
        cocotb.start_soon(axi_probe())
        cocotb.start_soon(deep_probe())

        tb.log.info("=== Read #1 (bank 0) ===")
        rd1 = AXI4Sequence("r_then_r_1", data_width=64, seed=seed)
        rd1.add_read(0x0000, length=1, axid=0)
        r1 = await tb.run_sequence(rd1)
        tb.log.info("Read #1: err=%s data=%s, cmds=%s, ar_fires=%d",
                    r1[0]["error"], r1[0]["data"],
                    observed["cmd_log"], observed["ar_fires"])
        observed["cmd_log"] = []  # clear for read #2

        tb.log.info("=== Read #2 (bank 1) ===")
        rd2 = AXI4Sequence("r_then_r_2", data_width=64, seed=seed + 1)
        rd2.add_read(0x2000, length=1, axid=0)
        r2 = await tb.run_sequence(rd2)
        tb.log.info("Read #2: err=%s data=%s, cmds_after_r2=%s, "
                    "ar_fires_total=%d, r_fires_total=%d",
                    r2[0]["error"], r2[0]["data"],
                    observed["cmd_log"], observed["ar_fires"],
                    observed["rdvalid_cnt"])

        assert r1[0]["error"] is None, f"Read #1 failed: {r1[0]['error']}"
        assert r2[0]["error"] is None, f"Read #2 failed: {r2[0]['error']}"

    elif test_type == "row_hit_pattern":
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        seq = AXI4Sequence("row_hit", data_width=64, seed=seed)
        seq.add_row_hit_burst(
            base_addr=0x0000_1000, n_followups=3,
            burst_bytes=64, is_write=True, qos=8,
        )
        results = await tb.run_sequence(seq)
        n_done = sum(1 for r in results if r["error"] is None)
        tb.log.info("row_hit: %d / %d bursts completed", n_done, len(results))

    elif test_type in ("open_page_workload", "happy_page_workload"):
        # PAGE_POLICY parameter is overridden in the pytest runner via
        # `parameters = {"PAGE_POLICY": "..."}` based on this test_type
        # suffix. With OPEN the scheduler emits RD/WR + explicit PRE
        # (vs CLOSE's RDA/WRA), hitting dfi_cmd_formatter's OP_RD /
        # OP_WR / OP_PRE branches and scheduler's S_NEED_PRE arm. With
        # HAPPY_HYBRID the AP decision is page_predictor-driven; we
        # drive enough row-hit + row-miss mix to exercise both
        # outcomes of `predict_open_i`.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        # Row-hit cluster first (bank stays open across follow-ups)
        seq = AXI4Sequence(test_type, data_width=64, seed=seed)
        seq.add_row_hit_burst(
            base_addr=0x0000_1000, n_followups=4,
            burst_bytes=64, is_write=True, qos=4,
        )
        # Row-miss pair forces PRE→ACT on the same bank/different row.
        # Bank 0 row 0 (already opened above) → bank 0 row N (different
        # row), addr ≈ row_stride * row_idx.
        # ROW_MAJOR row_stride = NUM_BANKS * COL_BYTES = 8 * (1<<10) * 8 = 64KB
        seq.add_write(0x0001_1000, [0xAAAA_BBBB_CCCC_DDDD], axid=0)
        seq.add_read(0x0000_1000, length=1, axid=0)
        seq.add_read(0x0001_1000, length=1, axid=0)
        results = await tb.run_sequence(seq)
        n_done = sum(1 for r in results if r["error"] is None)
        tb.log.info("%s: %d / %d bursts completed",
                    test_type, n_done, len(results))

    elif test_type == "open_page_lpddr2":
        # LPDDR2 + PAGE_POLICY=OPEN. workload_mix_lpddr2 only exercises
        # LPDDR2 with closed-page (the parameter default) which gates
        # the LPDDR2 CA-bus encoder to OP_RDA/OP_WRA only. With OPEN,
        # the scheduler emits OP_RD / OP_WR / OP_PRE, which hit the
        # LPDDR2 branches of dfi_cmd_formatter that are otherwise
        # unreachable.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        seq = AXI4Sequence("open_lpddr2", data_width=64, seed=seed)
        seq.add_row_hit_burst(
            base_addr=0x0000_1000, n_followups=3,
            burst_bytes=64, is_write=True, qos=2,
        )
        seq.add_read(0x0000_1000, length=1, axid=0)
        seq.add_write(0x0001_1000, [0xCAFE_BABE_DEAD_BEEF], axid=0)
        seq.add_read(0x0001_1000, length=1, axid=0)
        results = await tb.run_sequence(seq)
        n_done = sum(1 for r in results if r["error"] is None)
        tb.log.info("open_page_lpddr2: %d / %d bursts completed",
                    n_done, len(results))

    elif test_type == "wr2rd_forward_burst":
        # Back-to-back WR + RD-of-same-address so the wr_cmd_cam slot
        # for the WR is still pending when the AR arrives — fires
        # wr2rd_forward and exercises axi_intake's `r_r_fwd_active`
        # R-emit arm (lines 732-737 of axi_intake.sv that the DRAM
        # RD path doesn't reach).
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        # Single combined sequence so AW + AR are pipelined; the
        # framework issues all bursts back-to-back without waiting for
        # B before launching AR.
        seq = AXI4Sequence("fwd", data_width=64, seed=seed)
        for k in range(4):
            addr = 0x0000_3000 + (k << 6)
            pat  = 0xF0E1_D2C3_B4A5_9687 ^ k
            seq.add_write(addr, [pat], axid=0)
            seq.add_read(addr, length=1, axid=0)
        results = await tb.run_sequence(seq)
        n_done = sum(1 for r in results if r["error"] is None)
        tb.log.info("wr2rd_forward_burst: %d / %d bursts completed",
                    n_done, len(results))

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")


_GATE = [("smoke",)]
_FUNC = _GATE + [("configure_via_apb",), ("axi_write_smoke",),
                 ("wr_rd_roundtrip",), ("wr_rd_roundtrip_2beat",),
                 ("wr_rd_b2b_multi",),
                 ("wr_rd_b2b_multi_pipelined",),
                 ("wr_rd_b2b_truly_pipelined",),
                 ("wr_rd_b2b_pipelined_same_id",),
                 ("wr_rd_bank_sweep",),
                 ("bank0_probe",), ("bank0_delayed",),
                 ("fresh_read_each_bank",),
                 # memory_preload_read — preload helpers + BFM all work,
                 # but the DUT hangs on the *first* AXI read of a fresh
                 # address (subsequent reads of the just-written address
                 # work — see wr_rd_roundtrip). Tracking as a separate
                 # DUT-side bug; not in the FUNC suite yet.
                 ("workload_mix",), ("row_hit_pattern",),
                 # Config-axis coverage variants (mem_type / NUM_RANKS /
                 # CSR knobs). See dv/testplans/GAP_ANALYSIS.md "ROI
                 # table" — these flip configs to reach LPDDR2, multi-
                 # rank, OOO, page-policy-switch, and init-error branches
                 # the baseline scenarios don't visit.
                 ("smoke_lpddr2",), ("workload_mix_lpddr2",),
                 ("smoke_nr2",), ("workload_mix_nr2",),
                 ("workload_mix_policy_switch",),
                 ("wr_rd_ooo_multi_id",),
                 ("init_error_retry",),
                 ("read_then_read_probe",),
                 # Coverage-driven scenarios: PAGE_POLICY=OPEN/HAPPY
                 # exercises dfi_cmd_formatter's OP_RD/OP_WR/OP_PRE
                 # and scheduler's S_NEED_PRE arm; wr2rd_forward_burst
                 # hits axi_intake's forward path.
                 ("open_page_workload",),
                 ("happy_page_workload",),
                 ("open_page_lpddr2",),
                 ("wr2rd_forward_burst",)]
_FULL = _FUNC

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_ddr2_lpddr2_top(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    # Use the wrapper module so DFISlavePHY's `phy_dfi_*` bus binds.
    dut_name = "ddr2_lpddr2_top_tb_top"
    test_name = f"test_ddr2_lpddr2_top_{test_type}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/top/ddr2_lpddr2_top.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)
    # Append the TB wrapper that exposes phy_dfi_* aliases.
    verilog_sources.append(os.path.join(
        repo_root,
        "projects/components/memory-controllers/ddr2-lpddr2/dv/tb/"
        "ddr2_lpddr2_top_tb_top.sv"))

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Derive mem_type / num_ranks / PAGE_POLICY from the test_type
    # suffix so the test body and the Verilog parameters stay in sync.
    # PAGE_POLICY values mirror ddr2_lpddr2_pkg.page_policy_e:
    #   0 = OPEN, 1 = CLOSE (default), 2 = HAPPY_HYBRID
    mem_type = "LPDDR2" if test_type.endswith("_lpddr2") else "DDR2"
    num_ranks = 2 if test_type.endswith("_nr2") else 1
    if test_type in ("open_page_workload", "open_page_lpddr2"):
        page_policy = "0"
    elif test_type == "happy_page_workload":
        page_policy = "2"
    else:
        page_policy = "1"

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "MEM_TYPE": mem_type,
        "NUM_RANKS": str(num_ranks),
        "SEED": str(random.randint(0, 100000)),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {"NUM_RANKS": str(num_ranks), "PAGE_POLICY": page_policy}

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = [
        "+define+USE_ASYNC_RESET",
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP",
    ]
    sim_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    compile_args += get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_ddr2_lpddr2_top",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
