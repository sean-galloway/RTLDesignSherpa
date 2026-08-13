# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit-test runner for `axi4_slave_wr_crc_check`.

This block IS an AXI4 slave (per-channel CRC-32 accumulator over AW/W/B).
The TB drives it with the RDS-DV framework's AXI4MasterWrite BFM -- never
a hand-rolled AW/W/B poke.

Pins (see the TB docstring for the architectural note that this module
has NO error output -- it is a pure accumulator, not a comparator):
  - writing a known LFSR-shaped stream produces a CRC-32 matching an
    independent software reference (REFIN=1/REFOUT=1 standard CRC-32)
  - corrupting one beat changes the resulting CRC to match the
    CORRUPTED stream's software CRC (accumulation is over what was
    actually received) and diverges from the clean stream's CRC -- the
    mechanism an external comparator (axi4_dma_slaves) relies on to
    detect corruption
  - the inline 16-deep B-response FIFO does not drop or misroute B
    responses when several gapless bursts complete before BREADY drains
    them (this FIFO exists precisely because an earlier 1-bit
    r_b_pending design DID drop B's under exactly this pattern)
  - NUM_CHANNELS>1: each channel's CRC/beat-count state is independent

REG_LEVEL (env, default FUNC) selects how many (test_type, test_level)
combinations run; TEST_LEVEL (gate/func/full) scales how much work each
combination does. See vault/handbook/dv/test-runner.md.
"""

import os
import random
import pytest

import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.axi4.axi4_slave_wr_crc_check_tb import SlaveWrCrcCheckTB


_DEPTH = {
    "gate": {"burst": 4,  "corrupt_n": 4,  "b_bursts": 3, "b_len": 2, "ch0": 2, "ch1": 2},
    "func": {"burst": 16, "corrupt_n": 8,  "b_bursts": 5, "b_len": 3, "ch0": 4, "ch1": 3},
    "full": {"burst": 64, "corrupt_n": 16, "b_bursts": 8, "b_len": 4, "ch0": 8, "ch1": 6},
}


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_axi4_slave_wr_crc_check(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    test_level = os.environ.get("TEST_LEVEL", "gate").lower()
    if test_level not in _DEPTH:
        test_level = "gate"
    depth = _DEPTH[test_level]

    tb = SlaveWrCrcCheckTB(dut)
    await tb.setup_clocks_and_reset()

    scenarios = {
        "smoke": _smoke,
        "multi_beat_burst": _multi_beat_burst,
        "corrupted_beat": _corrupted_beat,
        "b_fifo_gapless_multi_id": _b_fifo_gapless_multi_id,
        "multi_channel_independent": _multi_channel_independent,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb, depth)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------


async def _smoke(tb: SlaveWrCrcCheckTB, depth: dict):
    """Single-beat write -- CRC + beat count telemetry after one beat."""
    words = tb.channel_words(1, channel=0)
    result = await tb.write_burst(addr=0x100, words=words, axi_id=0)
    assert result["success"], result
    assert result["id"] == 0
    await tb.settle()
    assert tb.crc_valid(0) == 1
    assert tb.beat_count(0) == 1
    assert tb.crc_value(0) == tb.expected_crc32_over_words(words)


async def _multi_beat_burst(tb: SlaveWrCrcCheckTB, depth: dict):
    """One AW burst of N beats -- CRC accumulates over all N."""
    n = depth["burst"]
    words = tb.channel_words(n, channel=0)
    result = await tb.write_burst(addr=0x200, words=words, axi_id=1)
    assert result["success"], result
    assert result["id"] == 1
    await tb.settle()
    assert tb.beat_count(0) == n
    assert tb.beat_count_total() == n
    want = tb.expected_crc32_over_words(words)
    got = tb.crc_value(0)
    assert got == want, f"CRC mismatch: got 0x{got:08X} want 0x{want:08X} over {n} beats"


async def _corrupted_beat(tb: SlaveWrCrcCheckTB, depth: dict):
    """Flip one beat mid-stream: the resulting CRC must match the
    CORRUPTED stream (accumulation is over actual received data) and
    diverge from the clean stream's CRC (the divergence IS the
    corruption becoming externally visible -- this module has no error
    output of its own; a downstream comparator relies on exactly this
    property). Mutation-check anchor: revert the corruption and the two
    CRCs collapse back to equal."""
    n = depth["corrupt_n"]
    clean = tb.channel_words(n, channel=0)
    corrupted = list(clean)
    flip_idx = n // 2
    corrupted[flip_idx] = corrupted[flip_idx] ^ 0x0000_0001

    result = await tb.write_burst(addr=0x300, words=corrupted, axi_id=2)
    assert result["success"], result
    await tb.settle()

    want_corrupted = tb.expected_crc32_over_words(corrupted)
    want_clean = tb.expected_crc32_over_words(clean)
    assert want_corrupted != want_clean, (
        "test bug: corrupted and clean streams produced the same "
        "software CRC -- the flip didn't change anything"
    )
    got = tb.crc_value(0)
    assert got == want_corrupted, (
        f"CRC did not track the actually-received (corrupted) data: "
        f"got 0x{got:08X} want 0x{want_corrupted:08X}"
    )
    assert got != want_clean, (
        f"CRC matched the CLEAN stream (0x{want_clean:08X}) despite beat "
        f"{flip_idx} being corrupted -- corruption would be invisible "
        f"to a downstream comparator"
    )


async def _b_fifo_gapless_multi_id(tb: SlaveWrCrcCheckTB, depth: dict):
    """Launch several gapless bursts concurrently with distinct IDs while
    BREADY is delayed, so multiple completed bursts queue in the inline
    B FIFO before draining. Every B must come back with the RIGHT id --
    the FIFO exists because a 1-bit r_b_pending design silently dropped
    B's under exactly this pattern."""
    n_bursts = depth["b_bursts"]
    b_len = depth["b_len"]
    assert n_bursts < 16, "must stay under the 16-deep inline B FIFO"

    tb.set_bready_delay_profile("burst_pause")

    tasks = []
    for i in range(n_bursts):
        words = tb.channel_words(b_len, channel=0)
        addr = 0x1000 + i * 0x100
        tasks.append(cocotb.start_soon(tb.write_burst(addr, words, axi_id=i)))

    results = [await t for t in tasks]
    await tb.settle()

    for i, result in enumerate(results):
        assert result["success"], f"burst {i}: {result}"
        assert result["id"] == i, (
            f"burst {i}: B response carried id={result['id']}, expected {i} "
            f"-- a dropped/misrouted B under queued backpressure"
        )
    assert tb.beat_count(0) == n_bursts * b_len
    assert tb.beat_count_total() == n_bursts * b_len


async def _multi_channel_independent(tb: SlaveWrCrcCheckTB, depth: dict):
    """NUM_CHANNELS=2 build: write to channel 0 then channel 1 -- each
    channel's CRC/beat-count state is independent."""
    assert tb.NUM_CHANNELS == 2, "this scenario requires a NUM_CHANNELS=2 build"
    n0, n1 = depth["ch0"], depth["ch1"]

    words0 = tb.channel_words(n0, channel=0)
    words1 = tb.channel_words(n1, channel=1)

    r0 = await tb.write_burst(addr=0x4000, words=words0, axi_id=0)
    r1 = await tb.write_burst(addr=0x5000, words=words1, axi_id=1)
    assert r0["success"] and r1["success"]
    await tb.settle()

    assert tb.beat_count(0) == n0
    assert tb.beat_count(1) == n1
    assert tb.beat_count_total() == n0 + n1
    assert tb.crc_value(0) == tb.expected_crc32_over_words(words0)
    assert tb.crc_value(1) == tb.expected_crc32_over_words(words1)


# ---------------------------------------------------------------------------
# REG_LEVEL grid
# ---------------------------------------------------------------------------

_CORE_TYPES = ["smoke", "multi_beat_burst", "corrupted_beat"]
_FUNC_TYPES = _CORE_TYPES + ["b_fifo_gapless_multi_id", "multi_channel_independent"]
_ALL_TYPES = _FUNC_TYPES

_REG_LEVEL = os.environ.get("REG_LEVEL", "FUNC").upper()

if _REG_LEVEL == "GATE":
    _COMBOS = [(t, "gate") for t in _CORE_TYPES]
elif _REG_LEVEL == "FULL":
    _COMBOS = [(t, lvl) for t in _ALL_TYPES for lvl in ("gate", "func", "full")]
else:  # FUNC (default)
    _COMBOS = [(t, "func") for t in _FUNC_TYPES]

_NUM_CHANNELS_FOR = {"multi_channel_independent": 2}


@pytest.mark.parametrize("test_type, test_level", _COMBOS)
def test_axi4_slave_wr_crc_check(request, test_type, test_level):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "axi4_slave_wr_crc_check"
    test_name = f"test_axi4_slave_wr_crc_check_{test_type}_{test_level}_{_REG_LEVEL.lower()}"

    filelist_path = "rtl/amba/filelists/axi4_slave_wr_crc_check.f"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    num_channels = _NUM_CHANNELS_FOR.get(test_type, 1)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "TEST_LEVEL": test_level,
        "REG_LEVEL": _REG_LEVEL,
        "AXI_DATA_WIDTH": "64",
        "AXI_ID_WIDTH": "8",
        "NUM_CHANNELS": str(num_channels),
        "SEED": os.environ.get("SEED", str(random.randint(0, 100000))),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {
        "AXI_DATA_WIDTH": "64",
        "AXI_ID_WIDTH": "8",
        "AXI_ADDR_WIDTH": "32",
        "AXI_USER_WIDTH": "1",
        "NUM_CHANNELS": str(num_channels),
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
        testcase="cocotb_test_axi4_slave_wr_crc_check",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
