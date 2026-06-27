# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

# TODO: extend every AXI4 / GAXI BFM-driven scenario in this suite with
# the framework's random timing profiles (see bin/TBClasses/amba/
# amba_random_configs.py — backtoback / constrained / fast / slow_*).
# The macro test today only exercises engine-driven traffic; mixing in
# BFM-driven peers with profile rotation will catch interface-level edge
# conditions (skid races, FIFO drain corners, mid-burst stalls) that a
# single timing profile misses.
"""Smoke test for ddr2_char_macro.

Wires up the two AXI4 master-side characterization engines + the
ddr2-lpddr2 controller behind one tb_top, then runs a tiny end-to-end
workload:

  1. Bring up APB CSR + DFI loopback through the existing
     DDR2LPDDR2TopTB infrastructure.
  2. Wait for init_done.
  3. Program the writer engine for a small LFSR workload, fire
     cfg_wr_start, wait cfg_wr_done.
  4. Program the reader engine to walk the same addresses, fire
     cfg_rd_start, wait cfg_rd_done.
  5. Assert no integrity errors and the CRC contract holds.

The controller's DFI side talks to the existing DFISlavePHY BFM
backed by MemoryModel — so writes persist and reads return the same
bytes.
"""

import logging
import os
import random
import sys

import cocotb
import pytest
from cocotb.triggers import ClockCycles, RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Reuse the controller's TB infrastructure for APB + DFI bring-up. The
# class only touches phy_dfi_* / s_apb_* / memtype_i / t_phy_wrlat_i etc.,
# all of which exist on ddr2_char_macro_tb_top with the same names.
_CTRL_DV_DIR = os.path.abspath(os.path.join(
    "/mnt/data/github/RTLDesignSherpa",
    "projects/components/memory-controllers/ddr2-lpddr2/dv"))
if _CTRL_DV_DIR not in sys.path:
    sys.path.insert(0, _CTRL_DV_DIR)

from tbclasses.ddr2_lpddr2_top_tb import DDR2LPDDR2TopTB  # noqa: E402


_NBA_SETTLE_PS = 100


# ---------------------------------------------------------------------------
# Engine cfg helpers — drive the cfg ports directly. The macro's cfg surface
# is just SV input ports, so a plain `dut.cfg_*.value = ...` is enough.
# ---------------------------------------------------------------------------


async def _drive_engine_idle(dut) -> None:
    """Idle all writer + reader cfg surfaces so the engines stay in
    S_IDLE until we explicitly pulse cfg_*_start."""
    for prefix in ("cfg_wr", "cfg_rd"):
        getattr(dut, f"{prefix}_start_addr").value       = 0
        getattr(dut, f"{prefix}_addr_stride_0").value    = 0
        getattr(dut, f"{prefix}_addr_stride_1").value    = 0
        getattr(dut, f"{prefix}_addr_wrap_mask_0").value = 0
        getattr(dut, f"{prefix}_addr_wrap_mask_1").value = 0
        getattr(dut, f"{prefix}_burst_len").value        = 1
        getattr(dut, f"{prefix}_txn_count").value        = 0
        getattr(dut, f"{prefix}_axi_id").value           = 0
        getattr(dut, f"{prefix}_id_mode").value          = 0
        getattr(dut, f"{prefix}_axi_size").value         = 3
        getattr(dut, f"{prefix}_axi_burst").value        = 1
        getattr(dut, f"{prefix}_lfsr_seed").value        = 0
        getattr(dut, f"{prefix}_data_mode").value        = 0
        getattr(dut, f"{prefix}_hash_seed0").value       = 0
        getattr(dut, f"{prefix}_hash_seed1").value       = 0
        getattr(dut, f"{prefix}_hash_seed2").value       = 0
    dut.cfg_wr_gap.value   = 0
    dut.cfg_rd_gap.value   = 0
    dut.cfg_wr_start.value = 0
    dut.cfg_rd_start.value = 0


async def _program_writer(dut, *, start_addr: int, stride_0: int,
                          burst_len: int, txn_count: int,
                          axi_id: int = 0, axi_size: int = 3,
                          lfsr_seed: int = 0) -> None:
    dut.cfg_wr_start_addr.value    = start_addr
    dut.cfg_wr_addr_stride_0.value = stride_0
    dut.cfg_wr_burst_len.value     = burst_len
    dut.cfg_wr_txn_count.value     = txn_count
    dut.cfg_wr_axi_id.value        = axi_id
    dut.cfg_wr_axi_size.value      = axi_size
    dut.cfg_wr_lfsr_seed.value     = lfsr_seed
    await RisingEdge(dut.mc_clk)
    await Timer(_NBA_SETTLE_PS, units="ps")


async def _program_reader(dut, *, start_addr: int, stride_0: int,
                          burst_len: int, txn_count: int,
                          axi_id: int = 0, axi_size: int = 3,
                          lfsr_seed: int = 0) -> None:
    dut.cfg_rd_start_addr.value    = start_addr
    dut.cfg_rd_addr_stride_0.value = stride_0
    dut.cfg_rd_burst_len.value     = burst_len
    dut.cfg_rd_txn_count.value     = txn_count
    dut.cfg_rd_axi_id.value        = axi_id
    dut.cfg_rd_axi_size.value      = axi_size
    dut.cfg_rd_lfsr_seed.value     = lfsr_seed
    await RisingEdge(dut.mc_clk)
    await Timer(_NBA_SETTLE_PS, units="ps")


async def _pulse(dut, port_name: str) -> None:
    getattr(dut, port_name).value = 1
    await RisingEdge(dut.mc_clk)
    await Timer(_NBA_SETTLE_PS, units="ps")
    getattr(dut, port_name).value = 0


async def _wait_done(dut, done_signal: str, timeout: int = 500_000) -> None:
    sig = getattr(dut, done_signal)
    for _ in range(timeout):
        await RisingEdge(dut.mc_clk)
        await Timer(_NBA_SETTLE_PS, units="ps")
        if int(sig.value):
            return
    raise TimeoutError(
        f"{done_signal} did not assert within {timeout} cycles"
    )


# ---------------------------------------------------------------------------
# cocotb test entry
# ---------------------------------------------------------------------------


@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_ddr2_char_macro(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    mem_type  = os.environ.get("MEM_TYPE", "DDR2").upper()

    tb = DDR2LPDDR2TopTB(dut, num_ranks=1)
    await _drive_engine_idle(dut)
    # Drain the reader-engine debug FIFO via the framework's GAXISlave.
    # Each received packet carries (actual, expected, mismatch) for one
    # R beat the engine observed — gives the test log EXACTLY which beat
    # went wrong and what the engine's LFSR mirror expected at that
    # phase. multi_sig=True binds the three named signals
    # (rd_dbg_actual, rd_dbg_expected, rd_dbg_mismatch) under the
    # rd_dbg_ prefix; the slave drives rd_dbg_ready.
    from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
    from CocoTBFramework.components.shared.field_config import (
        FieldConfig, FieldDefinition,
    )
    dbg_field_cfg = FieldConfig()
    dbg_field_cfg.add_field(FieldDefinition(name="actual",   bits=64))
    dbg_field_cfg.add_field(FieldDefinition(name="expected", bits=64))
    dbg_field_cfg.add_field(FieldDefinition(name="mismatch", bits=1))
    rd_dbg_slave = GAXISlave(
        dut=dut, title="rd_dbg_drain", prefix="rd_dbg",
        clock=dut.mc_clk, field_config=dbg_field_cfg,
        multi_sig=True, log=tb.log,
    )

    def _on_dbg_beat(packet):
        actual   = getattr(packet, "actual", 0)
        expected = getattr(packet, "expected", 0)
        mismatch = getattr(packet, "mismatch", 0)
        tag = "MISMATCH" if mismatch else "ok"
        tb.log.info(
            "RDDBG %s actual=0x%016X expected=0x%016X",
            tag, actual, expected,
        )

    rd_dbg_slave.add_callback(_on_dbg_beat)
    await tb.reset(mem_type=mem_type, init_complete_delay=20)
    tb.init_register_map()
    tb.init_apb_master()
    await tb.apb_master.reset_bus()
    tb.init_dfi_slave()
    await tb.wait_for_init_done()

    # 1x1 known-good; 1x2 isolates multi-beat-in-burst; 2x1 isolates
    # multi-burst; 2x2 was the original failing config.
    SHAPES = {
        "smoke":     dict(burst=1, n=1,    base=0x0000_2000),
        "smoke_1x2": dict(burst=2, n=1,    base=0x0000_2040),
        "smoke_2x1": dict(burst=1, n=2,    base=0x0000_2080),
        "smoke_2x2": dict(burst=2, n=2,    base=0x0000_20C0),
        # Scaled workloads. Burst len = BL=4 so each AXI burst maps 1-to-1
        # to a DRAM BL burst. Reader walks the same descriptor + per-beat
        # compares against the local LFSR.
        "kb_4burst":  dict(burst=4, n=4,    base=0x0001_0000),
        "kb_16burst": dict(burst=4, n=16,   base=0x0001_0000),
        "kb_17burst": dict(burst=4, n=17,   base=0x0001_0000),
        "kb_20burst": dict(burst=4, n=20,   base=0x0001_0000),
        "kb_24burst": dict(burst=4, n=24,   base=0x0001_0000),
        "kb1":       dict(burst=4, n=32,   base=0x0001_0000),
        "kb4":       dict(burst=4, n=128,  base=0x0001_0000),
        "kb32":      dict(burst=4, n=1024, base=0x0001_0000),
    }
    if test_type == "pacing_sweep_b2b":
        # Engine-PACING sweep — NOT an AXI random-profile sweep.
        # The AXI_RANDOMIZER_CONFIGS BFM cross-product lives at the
        # controller-only level on test_ddr2_lpddr2_core_macro. Here
        # the engines drive the AXI bus directly, so what we sweep is
        # the engines' own inter-burst pacing knobs (cfg_wr_gap,
        # cfg_rd_gap). Each gap pair stresses a different
        # writer/reader timing relationship — fast/fast catches
        # throughput corners; slow/fast catches cam-fill / wbuf-drain
        # corners; skewed (fast wr / slow rd) catches wr2rd_forward
        # arming windows.
        wr_gap = int(os.environ.get("WR_GAP", "0"))
        rd_gap = int(os.environ.get("RD_GAP", "0"))
        tb.log.info("pacing_sweep_b2b: wr_gap=%d rd_gap=%d", wr_gap, rd_gap)

        BURST = 4
        N = 17  # past RD_CAM_DEPTH=16 — exercises slot reuse + same-id
        BASE = 0x0001_0000
        BYTES_PER_BEAT = 8
        STRIDE = BURST * BYTES_PER_BEAT
        SEED = 0xDEAD_BEEF

        await _program_writer(dut, start_addr=BASE, stride_0=STRIDE,
                              burst_len=BURST, txn_count=N, lfsr_seed=SEED)
        await _program_reader(dut, start_addr=BASE, stride_0=STRIDE,
                              burst_len=BURST, txn_count=N, lfsr_seed=SEED)
        dut.cfg_wr_gap.value = wr_gap
        dut.cfg_rd_gap.value = rd_gap
        await RisingEdge(dut.mc_clk)

        await _pulse(dut, "cfg_wr_start")
        await _wait_done(dut, "cfg_wr_done", timeout=1_000_000)
        await _pulse(dut, "cfg_rd_start")
        await _wait_done(dut, "cfg_rd_done", timeout=1_000_000)

        assert int(dut.o_bresp_error.value) == 0
        assert int(dut.o_rresp_error.value) == 0
        assert int(dut.o_data_error.value) == 0, (
            f"data error (wr_gap={wr_gap} rd_gap={rd_gap})"
        )
        assert int(dut.o_beats_mismatched.value) == 0
        exp = int(dut.o_expected_crc.value)
        act = int(dut.o_actual_crc.value)
        assert exp == act, (
            f"CRC mismatch (wr_gap={wr_gap} rd_gap={rd_gap}): "
            f"exp=0x{exp:08X} act=0x{act:08X}"
        )
        tb.log.info(
            "pacing_sweep_b2b OK wr_gap=%d rd_gap=%d", wr_gap, rd_gap,
        )

    elif test_type in SHAPES:
        shape = SHAPES[test_type]
        BURST = shape["burst"]
        N     = shape["n"]
        BASE  = shape["base"]
        BYTES_PER_BEAT = 8   # AXI_DATA_WIDTH=64 → 8 bytes
        STRIDE = BURST * BYTES_PER_BEAT
        SEED = 0xDEAD_BEEF

        await _program_writer(dut, start_addr=BASE, stride_0=STRIDE,
                              burst_len=BURST, txn_count=N,
                              lfsr_seed=SEED)
        await _program_reader(dut, start_addr=BASE, stride_0=STRIDE,
                              burst_len=BURST, txn_count=N,
                              lfsr_seed=SEED)

        # Fire the writer first; let all B's drain before the reader
        # starts walking the same descriptor.
        await _pulse(dut, "cfg_wr_start")
        await _wait_done(dut, "cfg_wr_done")

        # Dump 1 beat per burst so we can see which burst's data went
        # wrong if the reader's per-beat compare latches.
        for burst_idx in range(N):
            byte_addr = BASE + burst_idx * STRIDE
            payload = tb.peek_memory(byte_addr, BYTES_PER_BEAT)
            tb.log.info(
                "DUMP burst=%d addr=0x%X mem=%s",
                burst_idx, byte_addr,
                payload.hex() if hasattr(payload, 'hex') else str(payload))

        await _pulse(dut, "cfg_rd_start")
        await _wait_done(dut, "cfg_rd_done")

        # Integrity contract — clean DFI loopback should produce zero
        # protocol errors and matching CRCs.
        assert int(dut.o_bresp_error.value) == 0, "BRESP error latched"
        assert int(dut.o_rresp_error.value) == 0, "RRESP error latched"
        assert int(dut.o_data_error.value) == 0, (
            "o_data_error latched — readback data didn't match LFSR"
        )
        assert int(dut.o_beats_mismatched.value) == 0
        assert int(dut.o_expected_crc_valid.value) == 1
        assert int(dut.o_actual_crc_valid.value) == 1
        exp = int(dut.o_expected_crc.value)
        act = int(dut.o_actual_crc.value)
        assert exp == act, (
            f"CRC mismatch: expected=0x{exp:08X}, actual=0x{act:08X}"
        )

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_ALL_TYPES = ["smoke", "smoke_1x2", "smoke_2x1", "smoke_2x2",
              "kb_4burst", "kb_16burst", "kb_17burst",
              "kb_20burst", "kb_24burst", "kb1", "kb4", "kb32"]
_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = _ALL_TYPES   # GATE == FUNC == FULL for now


@pytest.mark.parametrize("test_type", _PARAMS, ids=_PARAMS)
def test_ddr2_char_macro(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "ddr2_char_macro_tb_top"
    test_name = f"test_ddr2_char_macro_{test_type}"

    filelist_path = ("projects/NexysA7/ddr2-characterization/"
                     "ddr2_char_framework/dv/filelists/"
                     "ddr2_char_macro_tb_top.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "MEM_TYPE": "DDR2",
        "SEED": str(random.randint(0, 100000)),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {"NUM_RANKS": "1", "PAGE_POLICY": "1",
                  "RD_DBG_FIFO_DEPTH": "32"}

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    # Inherit the controller's canonical waiver set (autogenerated CSR
    # has known MULTIDRIVEN / UNUSED warnings that are not actionable).
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

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_ddr2_char_macro",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")


# ============================================================================
# Engine-pacing sweep — NOT an AXI random-profile sweep.
#
# The AXI random-profile (BFM AXI_RANDOMIZER_CONFIGS) cross-product
# lives on the controller-only env:
#   projects/components/memory-controllers/ddr2-lpddr2/dv/tests/macro/
#     test_ddr2_lpddr2_core_macro.py::test_ddr2_lpddr2_core_macro_profile_sweep
#
# This sweep is the engine-integration analog: it varies the engines'
# own inter-burst pacing knobs (cfg_wr_gap, cfg_rd_gap). Tests
# engine ↔ controller timing relationships rather than BFM
# valid/ready randomization. Same 31-config matrix shape (7 uniform +
# 12 single-axis + 12 skewed) to mirror the discipline of the
# components-side profile sweep.
# ============================================================================

_GAP_VALUES = (0, 1, 2, 4, 8, 16, 32)


def _build_macro_gap_matrix() -> list[tuple[int, int]]:
    """31-entry matrix: 7 uniform + 12 axis-only + 12 skewed pairs."""
    seen: set[tuple[int, int]] = set()
    matrix: list[tuple[int, int]] = []

    def add(t: tuple[int, int]) -> None:
        if t not in seen:
            seen.add(t)
            matrix.append(t)

    # 7 uniform
    for g in _GAP_VALUES:
        add((g, g))
    # 12 single-axis variants (other axis at 0)
    for g in _GAP_VALUES:
        if g == 0:
            continue
        add((g, 0))
        add((0, g))
    # 12 skewed pairs (factor-of-2 / extreme corners)
    skewed = [
        (1, 2), (2, 1), (2, 4), (4, 2), (4, 8), (8, 4),
        (8, 16), (16, 8), (16, 32), (32, 16), (1, 32), (32, 1),
    ]
    for t in skewed:
        add(t)
    return matrix


_MACRO_GAP_MATRIX = _build_macro_gap_matrix()


@pytest.mark.parametrize(
    "wr_gap,rd_gap",
    _MACRO_GAP_MATRIX,
    ids=[f"wr_{w}_rd_{r}" for (w, r) in _MACRO_GAP_MATRIX],
)
def test_ddr2_char_macro_pacing_sweep(request, wr_gap, rd_gap):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "ddr2_char_macro_tb_top"
    tag = f"wr_{wr_gap}_rd_{rd_gap}"
    test_name = f"test_ddr2_char_macro_pacing_sweep_{tag}"

    filelist_path = ("projects/NexysA7/ddr2-characterization/"
                     "ddr2_char_framework/dv/filelists/"
                     "ddr2_char_macro_tb_top.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": "pacing_sweep_b2b",
        "MEM_TYPE": "DDR2",
        "WR_GAP": str(wr_gap),
        "RD_GAP": str(rd_gap),
        "SEED": str(random.randint(0, 100000)),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {"NUM_RANKS": "1", "PAGE_POLICY": "1",
                  "RD_DBG_FIFO_DEPTH": "32"}

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
        testcase="cocotb_test_ddr2_char_macro",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
