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


@cocotb.test(timeout_time=120, timeout_unit="ms")
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

    elif test_type == "profile_sweep_b2b":
        # Engine-traffic mirror: pipelined writes + same-id pipelined
        # reads with a per-channel profile assignment. This is the
        # exact workload the controller-top env runs; here it lands
        # at the AXI-to-DFI macro level (no CSR / APB overhead).
        aw = os.environ.get("AXI_PROFILE_AW", "fast")
        w  = os.environ.get("AXI_PROFILE_W",  "fast")
        b  = os.environ.get("AXI_PROFILE_B",  "fast")
        ar = os.environ.get("AXI_PROFILE_AR", "fast")
        r  = os.environ.get("AXI_PROFILE_R",  "fast")
        tb.set_axi_timing_per_channel(aw=aw, w=w, b=b, ar=ar, r=r)

        N_BURSTS = 17
        BURST_LEN = 4
        BASE = 0x0001_0000
        STRIDE = BURST_LEN * 8
        FULL_STRB = (1 << (tb.axi_data_width // 8)) - 1

        def mk_payload(bi: int, ki: int) -> int:
            return ((bi & 0xFFFF) << 16) | (ki & 0xFFFF)

        aw_tasks: list = []
        w_tasks:  list = []
        for bi in range(N_BURSTS):
            aw_packet = tb.axi_master_wr.aw_channel.create_packet(
                addr=BASE + bi * STRIDE,
                len=BURST_LEN - 1,
                id=(bi & 0xF),
                size=3,
                burst=1,
            )
            aw_tasks.append(cocotb.start_soon(
                tb.axi_master_wr.aw_channel.send(aw_packet)
            ))
            for ki in range(BURST_LEN):
                w_packet = tb.axi_master_wr.w_channel.create_packet(
                    data=mk_payload(bi, ki),
                    last=(1 if ki == BURST_LEN - 1 else 0),
                    strb=FULL_STRB,
                )
                w_tasks.append(cocotb.start_soon(
                    tb.axi_master_wr.w_channel.send(w_packet)
                ))
        for t in aw_tasks + w_tasks:
            await t
        await ClockCycles(dut.mc_clk, 2000)

        rd_tasks: list = []
        for bi in range(N_BURSTS):
            rd_tasks.append(cocotb.start_soon(
                tb.axi_master_rd.read_transaction(
                    address=BASE + bi * STRIDE,
                    burst_len=BURST_LEN,
                    id=0,
                    size=3,
                )
            ))
        results = []
        for t in rd_tasks:
            results.append(await t)

        first_bad: Optional[tuple] = None
        for bi, data in enumerate(results):
            for ki in range(BURST_LEN):
                expected = mk_payload(bi, ki)
                if data[ki] != expected:
                    if first_bad is None:
                        first_bad = (bi, ki, expected, data[ki])
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
        "SEED": str(random.randint(0, 100000)),
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
