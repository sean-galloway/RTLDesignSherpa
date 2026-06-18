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
        "forward_smoke":   _run_forward_smoke,
        "miss_smoke":      _run_miss_smoke,
        "random_directed": _run_random_directed,
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
# Pytest wrapper
# ---------------------------------------------------------------------------

# Initial gate-level matrix — three scenarios, single timing profile, NR=1.
_INITIAL_PARAMS = [
    ("forward_smoke",   1, "backtoback"),
    ("miss_smoke",      1, "backtoback"),
    ("random_directed", 1, "backtoback"),
]


@pytest.mark.parametrize("test_type,num_ranks,timing_profile", _INITIAL_PARAMS,
                         ids=[f"{t[0]}-nr{t[1]}-{t[2]}" for t in _INITIAL_PARAMS])
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
    if enable_waves:
        compile_args += ["--trace", "--trace-structs"]
        extra_env["VERILATOR_TRACE"] = "1"

    parameters = {"NUM_RANKS": str(num_ranks)}

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
        timescale="1ns/1ps",
    )
