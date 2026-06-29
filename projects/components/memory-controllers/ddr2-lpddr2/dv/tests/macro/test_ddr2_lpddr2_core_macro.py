# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Tests for ddr2_lpddr2_core_macro — the AXI-to-DFI macro.

The DUT is the core controller WITHOUT the CSR slave layer; cfg signals
are driven directly by the TB. Two BFM populations drive the DUT:

  - AXI4MasterWrite + AXI4MasterRead on s_axi_* (host traffic)
  - DFISlavePHY + MemoryModel on phy_dfi_* (DFI loopback with
    preloadable / inspectable backing memory)

The headline test is `test_ddr2_lpddr2_core_macro_profile_sweep` —
parametric 31-config cross-product across the AXI_RANDOMIZER_CONFIGS
profiles applied per channel. Catches cross-channel-timing bugs that
the controller-top env can hit, but here at the AXI-to-DFI level
without CSR overhead so each sim is faster.
"""

from __future__ import annotations

import os
import random
import sys
from typing import Optional

import cocotb
import pytest
from cocotb.triggers import ClockCycles

from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.ddr2_lpddr2_core_macro_tb import DDR2LPDDR2CoreMacroTB  # noqa: E402


# ---------------------------------------------------------------------------
# cocotb entry
# ---------------------------------------------------------------------------


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_ddr2_lpddr2_core_macro(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    mem_type  = os.environ.get("MEM_TYPE", "DDR2").upper()

    tb = DDR2LPDDR2CoreMacroTB(dut, num_ranks=1)
    await tb.reset(mem_type=mem_type, init_complete_delay=20)
    tb.init_dfi_slave()
    tb.init_axi_masters()
    await tb.axi_master_wr.aw_channel.reset_bus()
    await tb.axi_master_wr.w_channel.reset_bus()
    await tb.axi_master_wr.b_channel.reset_bus()
    await tb.axi_master_rd.ar_channel.reset_bus()
    await tb.axi_master_rd.r_channel.reset_bus()
    await tb.wait_for_init_done()

    if test_type == "smoke":
        # Single write + read at one address to prove the AXI+DFI path
        # comes up clean under default timing.
        data_word = 0xCAFEBABE_DEADBEEF
        await tb.axi_master_wr.write_transaction(
            address=0x0001_0000, data=[data_word], id=0, size=3,
        )
        await ClockCycles(dut.mc_clk, 100)
        got = await tb.axi_master_rd.read_transaction(
            address=0x0001_0000, burst_len=1, id=0, size=3,
        )
        assert got[0] == data_word, (
            f"smoke roundtrip: wrote 0x{data_word:016X}, read 0x{got[0]:016X}"
        )

    elif test_type == "engine_mirror_kbN":
        # Exact mirror of the NexysA7 kb_* engine-driven scenarios at
        # the core_macro BFM level. Engines use:
        #   cfg_*_burst_len = BURST
        #   cfg_*_txn_count = N
        #   cfg_*_axi_id    = 0       (FIXED)
        #   cfg_*_id_mode   = 0       (FIXED — not OOO)
        #   cfg_*_gap       = 0       (back-to-back)
        import os as _os
        N = int(_os.environ.get("KBN_N", "128"))
        BURST = 4
        BASE = 0x0001_0000
        tb.log.info("engine_mirror_kbN: N=%d via shared sequences", N)
        await tb.wait_for_init_done()

        from tbclasses.ddr2_lpddr2_sequences import (
            build_b2b_wr_rd_sequences, diff_results,
        )
        from CocoTBFramework.components.axi4.axi4_sequence import (
            run_axi4_sequence,
        )

        wr_seq, rd_seq, expected = build_b2b_wr_rd_sequences(
            n_bursts=N, burst_len=BURST, base_addr=BASE,
            data_width=tb.axi_data_width,
            name="engine_mirror_kbN",
        )
        await run_axi4_sequence(wr_seq, master_wr=tb.axi_master_wr)
        from cocotb.triggers import ClockCycles as _CC_kbn
        await _CC_kbn(dut.mc_clk, 100)

        # === LOCALIZER A: AXI-WR ↔ DFI-WR ===
        # After WR drains, the DFISlavePHY's MemoryModel should hold
        # exactly what the AXI WR bursts intended. A mismatch here
        # means the controller corrupted on the way down — wbuf /
        # wr_beat_sequencer / dfi_signal_pack.
        STRIDE = BURST * (tb.axi_data_width // 8)
        wr_expected: dict[int, bytes] = {}
        for bi, beats in enumerate(expected):
            payload = bytearray()
            for beat in beats:
                payload += int(beat).to_bytes(tb.axi_data_width // 8,
                                              "little")
            wr_expected[BASE + bi * STRIDE] = bytes(payload)
        wr_bad = tb.verify_wr_path(wr_expected)
        assert wr_bad is None, (
            f"WR PATH CORRUPTION (kbN N={N}) at byte_addr=0x{wr_bad[0]:X} "
            f"offset={wr_bad[1]}: expected=0x{wr_bad[2]:02X} "
            f"actual=0x{wr_bad[3]:02X} — controller corrupted between AXI "
            f"WR ingress and DFI WR egress (wbuf / wr_beat_sequencer / "
            f"dfi_signal_pack)"
        )
        tb.log.info("WR-path localizer OK: all %d bursts × %d beats "
                    "intact in MemoryModel", N, BURST)

        rd_dicts = await run_axi4_sequence(
            rd_seq, master_rd=tb.axi_master_rd,
        )
        results = [r["data"] for r in rd_dicts]

        # === LOCALIZER B: DFI-RD ↔ AXI-RD ===
        # MemoryModel is now the source of truth for what DFI replays.
        # Each AXI RD burst's beats should equal MemoryModel[addr].
        # Mismatch here = corruption on the way up — rd_cl_aligner /
        # axi_intake R-emit.
        rd_first_bad: tuple | None = None
        for bi in range(N):
            bad = tb.verify_rd_path(
                BASE + bi * STRIDE, results[bi],
                data_width_bits=tb.axi_data_width,
            )
            if bad is not None:
                rd_first_bad = (bi, *bad)
                break
        assert rd_first_bad is None, (
            f"RD PATH CORRUPTION (kbN N={N}) at burst={rd_first_bad[0]} "
            f"beat={rd_first_bad[1]}: MemoryModel had 0x{rd_first_bad[2]:016X} "
            f"AXI returned 0x{rd_first_bad[3]:016X} — controller corrupted "
            f"between DFI RD ingress and AXI RD egress (rd_cl_aligner / "
            f"axi_intake R-emit)"
        )
        tb.log.info("RD-path localizer OK: all %d bursts intact across "
                    "DFI→AXI", N)

        # End-to-end (kept for completeness; both localizers already
        # passed if we got here).
        first_bad = diff_results(expected, results)
        assert first_bad is None, (
            f"engine_mirror_kbN (N={N}) corrupted at "
            f"burst={first_bad[0]} beat={first_bad[1]}: "
            f"wrote 0x{first_bad[2]:016X} read 0x{first_bad[3]:016X}"
        )
        tb.log.info("engine_mirror_kbN OK N=%d", N)

    elif test_type == "profile_sweep_b2b":
        # Per-channel random-timing profile sweep at the AXI-to-DFI
        # macro level. Pipelines 17 writes then 17 reads via
        # AXI4Sequence so the BFM dispatches ARs/AWs back-to-back
        # the way an engine would. NEVER start_soon parallel
        # read_transaction / write_transaction — that's per-id
        # deque contention, not real bus traffic.
        aw = os.environ.get("AXI_PROFILE_AW", "fast")
        w  = os.environ.get("AXI_PROFILE_W",  "fast")
        b  = os.environ.get("AXI_PROFILE_B",  "fast")
        ar = os.environ.get("AXI_PROFILE_AR", "fast")
        r  = os.environ.get("AXI_PROFILE_R",  "fast")
        tb.set_axi_timing_per_channel(aw=aw, w=w, b=b, ar=ar, r=r)

        N_BURSTS = 17
        BURST_LEN = 4
        BASE = 0x0001_0000

        from tbclasses.ddr2_lpddr2_sequences import (
            build_b2b_wr_rd_sequences, diff_results,
        )
        from CocoTBFramework.components.axi4.axi4_sequence import (
            run_axi4_sequence,
        )
        wr_seq, rd_seq, expected = build_b2b_wr_rd_sequences(
            n_bursts=N_BURSTS, burst_len=BURST_LEN, base_addr=BASE,
            data_width=tb.axi_data_width,
            name="profile_sweep_b2b",
        )
        await run_axi4_sequence(wr_seq, master_wr=tb.axi_master_wr)
        await ClockCycles(dut.mc_clk, 200)  # let B drain
        rd_dicts = await run_axi4_sequence(
            rd_seq, master_rd=tb.axi_master_rd,
        )
        results = [d["data"] for d in rd_dicts]

        first_bad = diff_results(expected, results)
        assert first_bad is None, (
            f"profile_sweep_b2b "
            f"(aw={aw} w={w} b={b} ar={ar} r={r}) "
            f"corrupted at burst={first_bad[0]} beat={first_bad[1]}: "
            f"wrote 0x{first_bad[2]:016X} read 0x{first_bad[3]:016X}"
        )
        tb.log.info(
            "profile_sweep_b2b OK aw=%s w=%s b=%s ar=%s r=%s",
            aw, w, b, ar, r,
        )

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_AXI_PROFILES = ("fixed", "constrained", "fast", "backtoback",
                 "burst_pause", "slow_producer", "high_throughput")


def _build_core_profile_matrix() -> list[tuple[str, str, str, str, str]]:
    """31-config matrix — same shape as controller-top + FUB sweeps."""
    seen: set[tuple[str, str, str, str, str]] = set()
    matrix: list[tuple[str, str, str, str, str]] = []

    def add(t: tuple[str, str, str, str, str]) -> None:
        if t not in seen:
            seen.add(t)
            matrix.append(t)

    for p in _AXI_PROFILES:
        add((p, p, p, p, p))
    fast = "fast"
    for p in _AXI_PROFILES:
        if p == fast:
            continue
        add((p,    fast, fast, fast, fast))
        add((fast, p,    fast, fast, fast))
        add((fast, fast, fast, p,    fast))
        add((fast, fast, fast, fast, p   ))
    return matrix


_CORE_PROFILE_MATRIX = _build_core_profile_matrix()


def _run_core_macro(*, test_name, test_type, extra_env_extra=None):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "ddr2_lpddr2_core_macro_tb_top"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/macro/ddr2_lpddr2_core_macro.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)
    verilog_sources.append(os.path.join(
        repo_root,
        "projects/components/memory-controllers/ddr2-lpddr2/dv/tb/"
        "ddr2_lpddr2_core_macro_tb_top.sv"))

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "MEM_TYPE": "DDR2",
        "NUM_RANKS": "1",
        "SEED": os.environ.get("OVERRIDE_SEED", str(random.randint(0, 100000))),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    if extra_env_extra:
        extra_env.update(extra_env_extra)
    parameters = {"NUM_RANKS": "1", "PAGE_POLICY": "1"}

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = [
        "+define+USE_ASYNC_RESET",
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP",
    ]
    sim_args: list = []
    plus_args: list = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_ddr2_lpddr2_core_macro",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")


def test_ddr2_lpddr2_core_macro_smoke():
    _run_core_macro(test_name="test_ddr2_lpddr2_core_macro_smoke",
                    test_type="smoke")


@pytest.mark.parametrize("n_bursts", [16, 17, 18, 20, 24, 32, 64, 128, 1024],
                         ids=lambda v: f"n{v}")
def test_ddr2_lpddr2_core_macro_engine_mirror_kbN(request, n_bursts):
    """Mirror of NexysA7 char_macro kb_* shapes at the BFM-driven
    AXI-to-DFI level. Each parametrize value matches one engine
    test: 16 = kb_16burst, 17 = kb_17burst, 32 = kb1, 128 = kb4,
    1024 = kb32. If any of these fail here the bug is in the
    controller, not in the engine path."""
    _run_core_macro(
        test_name=f"test_ddr2_lpddr2_core_macro_engine_mirror_kbN_n{n_bursts}",
        test_type="engine_mirror_kbN",
        extra_env_extra={"KBN_N": str(n_bursts)},
    )


@pytest.mark.parametrize(
    "profile_aw,profile_w,profile_b,profile_ar,profile_r",
    _CORE_PROFILE_MATRIX,
    ids=[f"aw_{a}_w_{w}_b_{b}_ar_{ar}_r_{r}"
         for (a, w, b, ar, r) in _CORE_PROFILE_MATRIX],
)
def test_ddr2_lpddr2_core_macro_profile_sweep(
    request, profile_aw, profile_w, profile_b, profile_ar, profile_r,
):
    tag = (f"aw_{profile_aw}_w_{profile_w}_b_{profile_b}"
           f"_ar_{profile_ar}_r_{profile_r}")
    test_name = f"test_ddr2_lpddr2_core_macro_profile_sweep_{tag}"
    _run_core_macro(
        test_name=test_name,
        test_type="profile_sweep_b2b",
        extra_env_extra={
            "AXI_PROFILE_AW": profile_aw,
            "AXI_PROFILE_W":  profile_w,
            "AXI_PROFILE_B":  profile_b,
            "AXI_PROFILE_AR": profile_ar,
            "AXI_PROFILE_R":  profile_r,
        },
    )
