# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Author: sean galloway
# Created: 2026-06-20

"""
Unit-test runner for `dfi_signal_pack_fub`.

Scenarios:
  reset_values  immediately after reset, all outputs at their safe defaults
  smoke         drive one bus snapshot; output matches input one cycle later
  stream        20 cycles of varied input, sliding 1-cycle scoreboard
  random_soak   N cycles of random bus values
"""

import os
import sys
import random
import logging
import pytest

import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.dfi_signal_pack_tb import DfiSignalPackTB, DfiBus  # noqa: E402


# ---------------------------------------------------------------------------
# CocoTB dispatch
# ---------------------------------------------------------------------------

@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_dfi_signal_pack(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    log = logging.getLogger("dfi_signal_pack_test")
    log.info(f"TEST_TYPE={test_type}")

    tb = DfiSignalPackTB(dut)
    await tb.setup_clocks_and_reset()

    scenarios = {
        "reset_values": _reset_values,
        "smoke":        _smoke,
        "stream":       _stream,
        "random_soak":  _random_soak,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)

    await tb.wait_clocks('mc_clk', 4)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------

async def _reset_values(tb: DfiSignalPackTB):
    """Outputs immediately after reset must be safe defaults."""
    expected = tb.reset_expected()
    tb.check(expected, label="post-reset")


async def _smoke(tb: DfiSignalPackTB):
    """Drive one bus snapshot; output matches it one cycle later."""
    b = DfiBus(
        address     = 0x1234,
        bank        = 0x5,
        cas_n       = 0b01,            # for rate-2
        ras_n       = 0b10,
        we_n        = 0b11,
        cs_n        = 0b01,
        cke         = 0b11,
        odt         = 0b10,
        wrdata      = 0xDEAD_BEEF_DEAD_BEEF_CAFE_BABE_CAFE_BABE,
        wrdata_en   = 1,
        wrdata_mask = 0,
        rddata_en   = 1,
    )
    tb.drive(b)
    await tb.wait_clocks('mc_clk', 1)
    tb.check(b, label="1-cycle latency")


async def _stream(tb: DfiSignalPackTB):
    """Sliding scoreboard — at any moment between edges, the output
    reflects what was sampled at the most recent edge, which is what
    was driven in the PREVIOUS iteration. So drive, then check
    (output still holds `prev`), then wait for the next edge."""
    rng = random.Random(tb.SEED ^ 0xA5A5)
    prev = None
    for i in range(20):
        cur = tb.random_bus(rng)
        tb.drive(cur)
        if prev is not None:
            tb.check(prev, label=f"cycle {i}")
        await tb.wait_clocks('mc_clk', 1)
        prev = cur


async def _random_soak(tb: DfiSignalPackTB):
    rng = random.Random(tb.SEED ^ 0x5A5A)
    n = {'gate': 30, 'func': 120, 'full': 500}.get(tb.TEST_LEVEL, 120)
    prev = None
    for i in range(n):
        cur = tb.random_bus(rng)
        tb.drive(cur)
        if prev is not None:
            tb.check(prev, label=f"random {i}")
        await tb.wait_clocks('mc_clk', 1)
        prev = cur


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_ALL_TYPES = ["reset_values", "smoke", "stream", "random_soak"]

_GATE = [(t, 2, 1) for t in ["reset_values", "smoke", "stream"]]
_FUNC = [(t, 2, 1) for t in _ALL_TYPES] + [(t, 4, 1) for t in ["smoke", "stream"]]
_FULL = _FUNC + [(t, 4, 2) for t in _ALL_TYPES] + [
    ("random_soak", 2, 1),
    ("random_soak", 4, 2),
]

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type,dfi_rate,num_ranks", _PARAMS,
                         ids=[f"{t[0]}-r{t[1]}-nr{t[2]}" for t in _PARAMS])
def test_dfi_signal_pack(request, test_type, dfi_rate, num_ranks):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "dfi_signal_pack_fub"

    test_name = f"test_dfi_signal_pack_{test_type}_r{dfi_rate}_nr{num_ranks}"

    filelist_path = (
        "projects/components/memory-controllers/ddr2-lpddr2/"
        "rtl/filelists/fub/dfi_signal_pack_fub.f"
    )
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path
    )

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    log_path     = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")
    os.makedirs(log_dir, exist_ok=True)

    # For rate-N: DFI_DATA_WIDTH = 64 × rate
    dfi_data_width = 64 * dfi_rate

    extra_env = {
        "DUT":               dut_name,
        "LOG_PATH":          log_path,
        "COCOTB_LOG_LEVEL":  "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        "SEED":              str(random.randint(0, 100000)),
        "TEST_TYPE":         test_type,
        "TEST_LEVEL":        _TEST_LEVEL.lower(),
        "NUM_RANKS":         str(num_ranks),
        "DFI_RATE":          str(dfi_rate),
        "DFI_ADDR_WIDTH":    "14",
        "DFI_BANK_WIDTH":    "3",
        "DFI_CTRL_WIDTH":    "1",
        "DFI_CS_WIDTH":      str(num_ranks),
        "DFI_DATA_WIDTH":    str(dfi_data_width),
        "DFI_EN_WIDTH":      "1",
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        extra_env["VERILATOR_TRACE"] = "1"
        extra_env["VERILATOR_TRACE_FST"] = "1"

    parameters = {
        "NUM_RANKS":      str(num_ranks),
        "DFI_RATE":       str(dfi_rate),
        "DFI_ADDR_WIDTH": "14",
        "DFI_BANK_WIDTH": "3",
        "DFI_CTRL_WIDTH": "1",
        "DFI_CS_WIDTH":   str(num_ranks),
        "DFI_DATA_WIDTH": str(dfi_data_width),
        "DFI_EN_WIDTH":   "1",
    }

    sim_args  = []
    plus_args = []
    if enable_waves:
        sim_args  += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args += ["--trace"]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_dfi_signal_pack",
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
