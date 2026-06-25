# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Cross-block check: writer fills a memory model with LFSR data; reader
walks the same address descriptor and CRCs the readback. End-to-end
assertions:

  - cfg_done_wr asserts after all B's; o_expected_crc_valid latches
  - cfg_done_rd asserts after all rlasts; o_actual_crc_valid latches
  - o_data_error == 0, o_beats_mismatched == 0, o_bresp_error == 0,
    o_rresp_error == 0
  - o_actual_crc == o_expected_crc (the cross-block contract)
"""

import os
import sys
import random
import pytest

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist


_NBA_SETTLE_PS = 100


async def _setup(dut):
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    # Default everything to safe values
    dut.cfg_start_addr.value       = 0
    dut.cfg_addr_stride_0.value    = 0
    dut.cfg_addr_stride_1.value    = 0
    dut.cfg_addr_wrap_mask_0.value = 0
    dut.cfg_addr_wrap_mask_1.value = 0
    dut.cfg_burst_len.value        = 1
    dut.cfg_txn_count.value        = 0
    dut.cfg_axi_id.value           = 0
    dut.cfg_id_mode.value          = 0
    dut.cfg_axi_size.value         = 3
    dut.cfg_axi_burst.value        = 1
    dut.cfg_lfsr_seed.value        = 0
    dut.cfg_data_mode.value        = 0
    dut.cfg_hash_seed0.value       = 0
    dut.cfg_hash_seed1.value       = 0
    dut.cfg_hash_seed2.value       = 0
    dut.cfg_wr_gap.value           = 0
    dut.cfg_rd_gap.value           = 0
    dut.cfg_start_wr.value         = 0
    dut.cfg_start_rd.value         = 0
    dut.aresetn.value              = 0
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    for _ in range(5):
        await RisingEdge(dut.aclk)


async def _program(dut, *, start_addr: int, stride_0: int = 0,
                   burst_len: int = 4, txn_count: int = 4,
                   axi_id: int = 0, lfsr_seed: int = 0,
                   wr_gap: int = 0, rd_gap: int = 0,
                   data_mode: int = 0,
                   hash_seed0: int = 0,
                   hash_seed1: int = 0,
                   hash_seed2: int = 0,
                   id_mode: int = 0):
    dut.cfg_start_addr.value       = start_addr
    dut.cfg_addr_stride_0.value    = stride_0
    dut.cfg_burst_len.value        = burst_len
    dut.cfg_txn_count.value        = txn_count
    dut.cfg_axi_id.value           = axi_id
    dut.cfg_id_mode.value          = id_mode & 0x3
    dut.cfg_lfsr_seed.value        = lfsr_seed
    dut.cfg_data_mode.value        = data_mode & 0x1
    dut.cfg_hash_seed0.value       = hash_seed0 & 0xFFFFFFFF
    dut.cfg_hash_seed1.value       = hash_seed1 & 0xFFFFFFFF
    dut.cfg_hash_seed2.value       = hash_seed2 & 0xFFFFFFFF
    dut.cfg_wr_gap.value           = wr_gap & 0xF
    dut.cfg_rd_gap.value           = rd_gap & 0xF
    await RisingEdge(dut.aclk)
    await Timer(_NBA_SETTLE_PS, units="ps")


async def _pulse_wr(dut):
    dut.cfg_start_wr.value = 1
    await RisingEdge(dut.aclk)
    await Timer(_NBA_SETTLE_PS, units="ps")
    dut.cfg_start_wr.value = 0


async def _pulse_rd(dut):
    dut.cfg_start_rd.value = 1
    await RisingEdge(dut.aclk)
    await Timer(_NBA_SETTLE_PS, units="ps")
    dut.cfg_start_rd.value = 0


async def _wait_wr_done(dut, timeout: int = 8000):
    for _ in range(timeout):
        await RisingEdge(dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")
        if int(dut.cfg_done_wr.value):
            return
    raise TimeoutError(f"cfg_done_wr did not assert in {timeout} cycles")


async def _wait_rd_done(dut, timeout: int = 8000):
    for _ in range(timeout):
        await RisingEdge(dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")
        if int(dut.cfg_done_rd.value):
            return
    raise TimeoutError(f"cfg_done_rd did not assert in {timeout} cycles")


@cocotb.test(timeout_time=4, timeout_unit="ms")
async def cocotb_test_pair(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    await _setup(dut)
    scenarios = {
        "smoke":         _smoke,
        "row_walk":      _row_walk,
        "seed_override": _seed_override,
        "rerun":         _rerun,
        "gapped":        _gapped,
        "hash_mode":     _hash_mode,
        "hash_mode_low_entropy": _hash_mode_low_entropy_pair,
        "hash_mode_id_counter":  _hash_mode_id_counter,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](dut)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------


async def _check_clean(dut):
    assert int(dut.o_bresp_error.value)       == 0
    assert int(dut.o_rresp_error.value)       == 0
    assert int(dut.o_data_error.value)        == 0
    assert int(dut.o_beats_mismatched.value)  == 0
    assert int(dut.o_expected_crc_valid.value) == 1
    assert int(dut.o_actual_crc_valid.value)   == 1
    exp = int(dut.o_expected_crc.value)
    act = int(dut.o_actual_crc.value)
    assert exp == act, (
        f"CRC mismatch: expected = 0x{exp:08X}, actual = 0x{act:08X}"
    )


async def _check_clean_hash(dut):
    """In hash mode the CRC pipeline is not the contract; the per-beat
    compare (o_data_error/o_beats_mismatched) is what proves end-to-end
    integrity."""
    assert int(dut.o_bresp_error.value)      == 0
    assert int(dut.o_rresp_error.value)      == 0
    assert int(dut.o_data_error.value)       == 0
    assert int(dut.o_beats_mismatched.value) == 0
    # CRC valid bits MUST stay low in hash mode
    assert int(dut.o_expected_crc_valid.value) == 0
    assert int(dut.o_actual_crc_valid.value)   == 0


async def _smoke(dut):
    """4 bursts of 4 beats, contiguous addresses. Writer fills mem; reader
    walks the same descriptor; CRCs must match end-to-end."""
    BURST = 4
    N = 4
    # stride must equal BURST * bytes_per_beat (64-bit beats = 8 bytes)
    await _program(dut, start_addr=0x100, stride_0=BURST * 8,
                   burst_len=BURST, txn_count=N, axi_id=3,
                   lfsr_seed=0xCAFEBABE)
    await _pulse_wr(dut)
    await _wait_wr_done(dut)
    await _pulse_rd(dut)
    await _wait_rd_done(dut)
    await _check_clean(dut)


async def _row_walk(dut):
    """Larger stride — bursts spread across mem. Still must round-trip."""
    BURST = 2
    N = 8
    STRIDE = 0x40   # sparse: bursts don't fill all the mem between them
    await _program(dut, start_addr=0x200, stride_0=STRIDE,
                   burst_len=BURST, txn_count=N, axi_id=5,
                   lfsr_seed=0xDEADBEEF)
    await _pulse_wr(dut)
    await _wait_wr_done(dut)
    await _pulse_rd(dut)
    await _wait_rd_done(dut)
    await _check_clean(dut)


async def _seed_override(dut):
    """Non-default LFSR seed. Both blocks see cfg_lfsr_seed and must
    use it for both pattern emission and pattern check."""
    BURST = 4
    N = 3
    await _program(dut, start_addr=0x80, stride_0=BURST * 8,
                   burst_len=BURST, txn_count=N,
                   lfsr_seed=0xA5A5A5A5)
    await _pulse_wr(dut)
    await _wait_wr_done(dut)
    await _pulse_rd(dut)
    await _wait_rd_done(dut)
    await _check_clean(dut)


async def _gapped(dut):
    """Run with non-zero wr_gap + rd_gap. End-to-end CRC must still
    match — the gap state must not perturb LFSR/CRC accounting."""
    BURST = 4
    N = 4
    await _program(dut, start_addr=0x300, stride_0=BURST * 8,
                   burst_len=BURST, txn_count=N,
                   wr_gap=3, rd_gap=7, lfsr_seed=0xBEEFCAFE)
    await _pulse_wr(dut); await _wait_wr_done(dut)
    await _pulse_rd(dut); await _wait_rd_done(dut)
    await _check_clean(dut)


async def _hash_mode(dut):
    """End-to-end in hash mode. Writer emits f(addr); memory stores it;
    reader regenerates f(addr) locally and compares per beat. No CRC
    contract here — per-beat compare proves the round trip."""
    SEEDS = (0x9E3779B9, 0x85EBCA6B, 0xC2B2AE35)
    BURST = 4
    N = 4
    await _program(dut, start_addr=0x500, stride_0=BURST * 8,
                   burst_len=BURST, txn_count=N, axi_id=4,
                   data_mode=1,
                   hash_seed0=SEEDS[0], hash_seed1=SEEDS[1],
                   hash_seed2=SEEDS[2])
    await _pulse_wr(dut); await _wait_wr_done(dut)
    await _pulse_rd(dut); await _wait_rd_done(dut)
    await _check_clean_hash(dut)


async def _hash_mode_low_entropy_pair(dut):
    """Hash mode with start_addr=0 — the worst case for "naive" data
    functions. Round-trip must still be clean: hash seeds inject enough
    entropy that low-bit-count addresses don't collide."""
    SEEDS = (0xDEADBEEF, 0xCAFEBABE, 0x12345678)
    BURST = 8
    N = 1
    await _program(dut, start_addr=0, stride_0=BURST * 8,
                   burst_len=BURST, txn_count=N,
                   data_mode=1,
                   hash_seed0=SEEDS[0], hash_seed1=SEEDS[1],
                   hash_seed2=SEEDS[2])
    await _pulse_wr(dut); await _wait_wr_done(dut)
    await _pulse_rd(dut); await _wait_rd_done(dut)
    await _check_clean_hash(dut)


async def _hash_mode_id_counter(dut):
    """End-to-end with hash data + COUNTER ID mode. Because hash data is
    a pure function of address, the ID scheme doesn't influence data,
    so this just confirms the round-trip stays clean when IDs vary."""
    SEEDS = (0x9E3779B9, 0x85EBCA6B, 0xC2B2AE35)
    BURST = 4
    N = 6
    await _program(dut, start_addr=0x600, stride_0=BURST * 8,
                   burst_len=BURST, txn_count=N,
                   axi_id=0x10, id_mode=1,
                   data_mode=1,
                   hash_seed0=SEEDS[0], hash_seed1=SEEDS[1],
                   hash_seed2=SEEDS[2])
    await _pulse_wr(dut); await _wait_wr_done(dut)
    await _pulse_rd(dut); await _wait_rd_done(dut)
    await _check_clean_hash(dut)


async def _rerun(dut):
    """Run the pair twice with different descriptors. Both runs must be
    clean (no leftover state poisoning the second pass)."""
    # Run 1
    await _program(dut, start_addr=0x000, stride_0=16,
                   burst_len=2, txn_count=3, axi_id=1,
                   lfsr_seed=0x12345678)
    await _pulse_wr(dut); await _wait_wr_done(dut)
    await _pulse_rd(dut); await _wait_rd_done(dut)
    await _check_clean(dut)
    # Run 2
    await _program(dut, start_addr=0x400, stride_0=32,
                   burst_len=4, txn_count=4, axi_id=7,
                   lfsr_seed=0x87654321)
    await _pulse_wr(dut); await _wait_wr_done(dut)
    await _pulse_rd(dut); await _wait_rd_done(dut)
    await _check_clean(dut)


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_ALL_TYPES = ["smoke", "row_walk", "seed_override", "rerun", "gapped",
              "hash_mode", "hash_mode_low_entropy",
              "hash_mode_id_counter"]
_GATE = [(t,) for t in ["smoke", "row_walk"]]
_FUNC = [(t,) for t in _ALL_TYPES]
_FULL = _FUNC

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_axi4_master_pat_crc_pair(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "tb_axi4_master_pat_crc_pair"
    test_name = f"test_axi4_master_pat_crc_pair_{test_type}"

    # Combine the wr + rd filelists, then add the wrapper
    wr_fl = "rtl/amba/filelists/axi4_master_wr_pattern_gen.f"
    rd_fl = "rtl/amba/filelists/axi4_master_rd_crc_check.f"
    wr_sources, wr_includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=wr_fl)
    rd_sources, rd_includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=rd_fl)
    # Deduplicate while preserving order
    seen = set()
    verilog_sources = []
    for f in wr_sources + rd_sources:
        if f not in seen:
            seen.add(f); verilog_sources.append(f)
    includes = list(dict.fromkeys(wr_includes + rd_includes))
    verilog_sources.append(os.path.join(repo_root, tests_dir,
                                         "tb_axi4_master_pat_crc_pair.sv"))

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "SEED": str(random.randint(0, 100000)),
        "TEST_LEVEL": os.environ.get("TEST_LEVEL", "FUNC"),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET", "-Wno-WIDTHTRUNC"]
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
        testcase="cocotb_test_pair",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
