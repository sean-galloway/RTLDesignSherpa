# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit-test runner for `axi4_master_rd_crc_check`."""

import os
import sys
import random
import pytest

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.axi4.axi4_master_rd_crc_check_tb import RdCrcCheckTB


@cocotb.test(timeout_time=4, timeout_unit="ms")
async def cocotb_test_axi4_master_rd_crc_check(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke_match")
    tb = RdCrcCheckTB(dut)
    await tb.setup_clocks_and_reset()
    scenarios = {
        "smoke_match":         _smoke_match,
        "multi_burst_match":   _multi_burst_match,
        "address_walk":        _address_walk,
        "data_mismatch_sticky": _data_mismatch_sticky,
        "beats_mismatched_count": _beats_mismatched_count,
        "rresp_error_sticky":  _rresp_error_sticky,
        "rerun_after_done":    _rerun_after_done,
        "rd_gap_inserts_idle": _rd_gap_inserts_idle,
        "hash_mode_match":     _hash_mode_match,
        "hash_mode_low_entropy": _hash_mode_low_entropy,
        "arvalid_no_drop":     _arvalid_no_drop,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------


async def _smoke_match(tb: RdCrcCheckTB):
    """Slave returns the matching LFSR pattern → no data_error,
    actual_crc valid at cfg_done."""
    await tb.program(start_addr=0x100, burst_len=1, txn_count=1,
                     axi_id=3, lfsr_seed=0xDEADBEEF)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.ar_log) == 1
    assert int(tb.dut.o_data_error.value)       == 0
    assert int(tb.dut.o_rresp_error.value)      == 0
    assert int(tb.dut.o_actual_crc_valid.value) == 1
    assert int(tb.dut.o_beats_mismatched.value) == 0


async def _multi_burst_match(tb: RdCrcCheckTB):
    """4 bursts of 4 beats, all matching → all clean."""
    BURST = 4
    N = 4
    await tb.program(start_addr=0x200, stride_0=0x20, burst_len=BURST,
                     txn_count=N, axi_id=5)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.ar_log) == N
    assert int(tb.dut.o_data_error.value)       == 0
    assert int(tb.dut.o_beats_mismatched.value) == 0


async def _address_walk(tb: RdCrcCheckTB):
    BASE = 0x4000
    STRIDE = 0x100
    N = 6
    await tb.program(start_addr=BASE, stride_0=STRIDE, burst_len=2,
                     txn_count=N)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.ar_log) == N
    for i, ar in enumerate(tb.ar_log):
        expected = BASE + i * STRIDE
        assert ar.addr == expected, (
            f"AR[{i}].addr = 0x{ar.addr:X} want 0x{expected:X}"
        )


async def _data_mismatch_sticky(tb: RdCrcCheckTB):
    """Slave returns garbage → o_data_error latches."""
    tb.return_lfsr_data = False
    tb.garbage_word = 0xBADCAFE_DEADBEEF
    await tb.program(start_addr=0, burst_len=2, txn_count=2)
    await tb.pulse_start()
    await tb.wait_done()
    assert int(tb.dut.o_data_error.value) == 1, (
        "o_data_error did not latch on garbage R data"
    )


async def _beats_mismatched_count(tb: RdCrcCheckTB):
    """Garbage data → o_beats_mismatched counts every mismatching beat."""
    tb.return_lfsr_data = False
    BURST = 4
    N = 3
    await tb.program(start_addr=0, burst_len=BURST, txn_count=N)
    await tb.pulse_start()
    await tb.wait_done()
    expected_mismatches = BURST * N
    got = int(tb.dut.o_beats_mismatched.value)
    assert got == expected_mismatches, (
        f"o_beats_mismatched = {got}, want {expected_mismatches}"
    )


async def _rresp_error_sticky(tb: RdCrcCheckTB):
    """Slave returns SLVERR on rresp → o_rresp_error latches."""
    tb.rresp_override = 2   # SLVERR
    await tb.program(start_addr=0, burst_len=2, txn_count=2)
    await tb.pulse_start()
    await tb.wait_done()
    assert int(tb.dut.o_rresp_error.value) == 1


async def _rd_gap_inserts_idle(tb: RdCrcCheckTB):
    """cfg_rd_gap > 0 inserts idle cycles between AR bursts. Clean
    workload still completes; LFSR phase still matches the slave's
    pattern responder."""
    await tb.program(start_addr=0, burst_len=2, txn_count=3, rd_gap=7)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.ar_log) == 3
    assert int(tb.dut.o_data_error.value) == 0


async def _arvalid_no_drop(tb: RdCrcCheckTB):
    """At cfg_rd_gap=0 with pipelined AR, arvalid must NOT drop between
    the first AR being driven and the last AR being handshaked."""
    BURST = 4
    N = 4
    await tb.program(start_addr=0x200, stride_0=BURST * 8,
                     burst_len=BURST, txn_count=N, rd_gap=0)
    await tb.pulse_start()

    saw_arvalid_high = False
    ar_handshakes = 0
    drops_observed = 0
    for _ in range(2000):
        await RisingEdge(tb.dut.aclk)
        await Timer(100, units="ps")
        v = int(tb.dut.m_axi_arvalid.value)
        r = int(tb.dut.m_axi_arready.value)
        if v and r:
            ar_handshakes += 1
            if ar_handshakes == N:
                break
        if v:
            saw_arvalid_high = True
        elif saw_arvalid_high and ar_handshakes < N:
            drops_observed += 1
    assert ar_handshakes == N, (
        f"only saw {ar_handshakes}/{N} AR handshakes"
    )
    assert drops_observed == 0, (
        f"arvalid dropped {drops_observed} cycles mid-run at gap=0"
    )
    await tb.wait_done()


async def _hash_mode_match(tb: RdCrcCheckTB):
    """data_mode=1: slave responder returns addr_hash32 of each beat's
    byte address; DUT regenerates the same hash locally and compares per
    beat. Asserts clean compare and o_actual_crc_valid stays low (CRC is
    not the contract in hash mode)."""
    SEEDS = (0x9E3779B9, 0x85EBCA6B, 0xC2B2AE35)
    BURST = 4
    N = 3
    BYTES_PER_BEAT = tb.AXI_DATA_WIDTH // 8
    await tb.program(start_addr=0x100, stride_0=BURST * BYTES_PER_BEAT,
                     burst_len=BURST, txn_count=N, data_mode=1,
                     hash_seed0=SEEDS[0], hash_seed1=SEEDS[1],
                     hash_seed2=SEEDS[2])
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.ar_log) == N
    assert int(tb.dut.o_data_error.value)       == 0
    assert int(tb.dut.o_beats_mismatched.value) == 0
    assert int(tb.dut.o_actual_crc_valid.value) == 0


async def _hash_mode_low_entropy(tb: RdCrcCheckTB):
    """Low-entropy addresses (start at 0, contiguous bytes) must NOT
    produce stuck/repeating data — the whole point of the hash seeds is
    to defeat that. Run with start_addr=0 and check that consecutive
    beats produce distinct data."""
    SEEDS = (0xDEADBEEF, 0xCAFEBABE, 0x12345678)
    BURST = 8
    N = 1
    BYTES_PER_BEAT = tb.AXI_DATA_WIDTH // 8
    await tb.program(start_addr=0, stride_0=BURST * BYTES_PER_BEAT,
                     burst_len=BURST, txn_count=N, data_mode=1,
                     hash_seed0=SEEDS[0], hash_seed1=SEEDS[1],
                     hash_seed2=SEEDS[2])
    await tb.pulse_start()
    await tb.wait_done()
    assert int(tb.dut.o_data_error.value) == 0
    # Sanity check on the Python mirror itself: consecutive byte addresses
    # at addr=0 must not collide. (If they do, the hash is broken even
    # before talking about RTL.)
    from TBClasses.axi4.axi4_master_wr_pattern_gen_tb import WrPatternGenTB
    vals = set()
    for k in range(BURST):
        byte_addr = (k * BYTES_PER_BEAT) & 0xFFFFFFFF
        v = WrPatternGenTB.addr_hash32(byte_addr, *SEEDS)
        vals.add(v)
    assert len(vals) == BURST, (
        f"hash collisions at low-entropy addrs: only {len(vals)}/{BURST} distinct"
    )


async def _rerun_after_done(tb: RdCrcCheckTB):
    """A second cfg_start pulse after cfg_done must re-run cleanly."""
    await tb.program(start_addr=0x100, burst_len=2, txn_count=2)
    await tb.pulse_start()
    await tb.wait_done()
    tb.ar_log.clear()
    await tb.program(start_addr=0x800, burst_len=4, txn_count=3,
                     axi_id=7)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.ar_log) == 3
    assert tb.ar_log[0].addr == 0x800
    assert tb.ar_log[0].axid == 7
    assert int(tb.dut.o_data_error.value) == 0


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_ALL_TYPES = ["smoke_match", "multi_burst_match", "address_walk",
              "data_mismatch_sticky", "beats_mismatched_count",
              "rresp_error_sticky", "rerun_after_done",
              "rd_gap_inserts_idle", "hash_mode_match",
              "hash_mode_low_entropy", "arvalid_no_drop"]
_GATE = [(t,) for t in ["smoke_match", "multi_burst_match",
                        "data_mismatch_sticky"]]
_FUNC = [(t,) for t in _ALL_TYPES]
_FULL = _FUNC

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_axi4_master_rd_crc_check(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "axi4_master_rd_crc_check"
    test_name = f"test_axi4_master_rd_crc_check_{test_type}"

    filelist_path = "rtl/amba/filelists/axi4_master_rd_crc_check.f"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "AXI_DATA_WIDTH": "64",
        "AXI_ID_WIDTH":   "8",
        "SEED": str(random.randint(0, 100000)),
        "TEST_LEVEL": os.environ.get("TEST_LEVEL", "FUNC"),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {
        "AXI_DATA_WIDTH": "64",
        "AXI_ID_WIDTH":   "8",
        "AXI_ADDR_WIDTH": "32",
        "AXI_USER_WIDTH": "1",
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
        testcase="cocotb_test_axi4_master_rd_crc_check",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
