# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit-test runner for `axi4_dma_slaves` -- the bundle wrapper combining
`axi4_slave_rd_pattern_gen` (AR/R) and `axi4_slave_wr_crc_check` (AW/W/B)
behind one aclk/aresetn.

The TB drives BOTH sides of the one DUT with the RDS-DV framework's
AXI4MasterRead/AXI4MasterWrite BFMs -- never a hand-rolled poke.

Integration scenario (from the module header comment): "the master
writes back the same LFSR data it read, so both sides compute against
the same CRC". This is the one thing only the bundle can prove -- the
per-block tests (test_axi4_slave_rd_pattern_gen.py,
test_axi4_slave_wr_crc_check.py) already cover each side in isolation.

REG_LEVEL (env, default FUNC) selects how many (test_type, test_level)
combinations run; TEST_LEVEL (gate/func/full) scales how much work each
combination does.
"""

import os
import random
import pytest

import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.axi4.axi4_dma_slaves_tb import DmaSlavesTB


_DEPTH = {
    "gate": {"n": 4},
    "func": {"n": 16},
    "full": {"n": 64},
}


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_axi4_dma_slaves(dut):
    test_type = os.environ.get("TEST_TYPE", "read_smoke")
    test_level = os.environ.get("TEST_LEVEL", "gate").lower()
    if test_level not in _DEPTH:
        test_level = "gate"
    depth = _DEPTH[test_level]

    tb = DmaSlavesTB(dut)
    await tb.setup_clocks_and_reset()

    scenarios = {
        "read_smoke": _read_smoke,
        "write_smoke": _write_smoke,
        "echo_pass_through": _echo_pass_through,
        "echo_corrupted": _echo_corrupted,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb, depth)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------


async def _read_smoke(tb: DmaSlavesTB, depth: dict):
    """Basic read from the pattern-gen side works in the bundled DUT."""
    n = depth["n"]
    got = await tb.read_burst(addr=0x100, burst_len=n, axi_id=0)
    assert len(got) == n
    await tb.settle()
    assert tb.read_crc_valid(0) == 1
    assert tb.read_beat_count(0) == n


async def _write_smoke(tb: DmaSlavesTB, depth: dict):
    """Basic write to the crc-check side works in the bundled DUT."""
    n = depth["n"]
    data_list = [0xA5A5_0000_0000_0000 | i for i in range(n)]
    result = await tb.write_burst(addr=0x200, data_list=data_list, axi_id=1)
    assert result["success"], result
    await tb.settle()
    assert tb.write_crc_valid(0) == 1
    assert tb.write_beat_count(0) == n


async def _echo_pass_through(tb: DmaSlavesTB, depth: dict):
    """Read N beats from the pattern generator, write the exact same
    beats back to the CRC checker: both sides' per-channel CRC and beat
    count must match (same data, same CRC config) -- the integrity
    contract this module exists to support."""
    n = depth["n"]
    read_data = await tb.read_burst(addr=0x1000, burst_len=n, axi_id=0)
    result = await tb.write_burst(addr=0x2000, data_list=read_data, axi_id=0)
    assert result["success"], result
    await tb.settle()

    assert tb.read_beat_count(0) == n
    assert tb.write_beat_count(0) == n

    read_crc = tb.read_crc_value(0)
    write_crc = tb.write_crc_value(0)
    assert read_crc == write_crc, (
        f"pass-through echo diverged: read side CRC=0x{read_crc:08X} "
        f"write side CRC=0x{write_crc:08X} over identical {n}-beat data"
    )


async def _echo_corrupted(tb: DmaSlavesTB, depth: dict):
    """Same echo, but flip one beat before writing it back: the two
    sides' CRCs must diverge -- this is the end-to-end detection
    mechanism (axi4_slave_wr_crc_check has no error output of its own;
    see that block's TB docstring). Mutation-check anchor: without the
    flip, this collapses to the pass-through scenario above and the two
    CRCs are equal again."""
    n = depth["n"]
    read_data = await tb.read_burst(addr=0x3000, burst_len=n, axi_id=0)
    corrupted = list(read_data)
    flip_idx = n // 2
    corrupted[flip_idx] = corrupted[flip_idx] ^ 0x1

    result = await tb.write_burst(addr=0x4000, data_list=corrupted, axi_id=0)
    assert result["success"], result
    await tb.settle()

    read_crc = tb.read_crc_value(0)
    write_crc = tb.write_crc_value(0)
    assert read_crc != write_crc, (
        f"corrupted echo (beat {flip_idx} flipped) produced matching CRCs "
        f"(0x{read_crc:08X}) -- corruption would be invisible to a "
        f"downstream comparator"
    )


# ---------------------------------------------------------------------------
# REG_LEVEL grid
# ---------------------------------------------------------------------------

_CORE_TYPES = ["read_smoke", "write_smoke"]
_FUNC_TYPES = _CORE_TYPES + ["echo_pass_through", "echo_corrupted"]
_ALL_TYPES = _FUNC_TYPES

_REG_LEVEL = os.environ.get("REG_LEVEL", "FUNC").upper()

if _REG_LEVEL == "GATE":
    _COMBOS = [(t, "gate") for t in _CORE_TYPES]
elif _REG_LEVEL == "FULL":
    _COMBOS = [(t, lvl) for t in _ALL_TYPES for lvl in ("gate", "func", "full")]
else:  # FUNC (default)
    _COMBOS = [(t, "func") for t in _FUNC_TYPES]


@pytest.mark.parametrize("test_type, test_level", _COMBOS)
def test_axi4_dma_slaves(request, test_type, test_level):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "axi4_dma_slaves"
    test_name = f"test_axi4_dma_slaves_{test_type}_{test_level}_{_REG_LEVEL.lower()}"

    filelist_path = "rtl/amba/filelists/axi4_dma_slaves.f"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "TEST_LEVEL": test_level,
        "REG_LEVEL": _REG_LEVEL,
        "AXI_DATA_WIDTH": "64",
        "AXI_ID_WIDTH": "8",
        "NUM_CHANNELS": "1",
        "SEED": os.environ.get("SEED", str(random.randint(0, 100000))),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {
        "AXI_DATA_WIDTH": "64",
        "AXI_ID_WIDTH": "8",
        "AXI_ADDR_WIDTH": "32",
        "AXI_USER_WIDTH": "1",
        "NUM_CHANNELS": "1",
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET", "-Wno-WIDTHTRUNC"]
    sim_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_axi4_dma_slaves",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
