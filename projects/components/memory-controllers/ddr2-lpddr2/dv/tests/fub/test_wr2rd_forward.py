# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit-test runner for `wr2rd_forward`.

The block was `integration_tested` in the testplans; no direct FUB
test pinned its five selection contracts (no-match passthrough,
match→forward, multi-match last-write-wins, partial-strobe gate,
length-match gate). A regression on any one of them would propagate
into the AXI R-channel as either a wrong-bank read or a stale-data
forward with no test failure.
"""

import os
import sys
import random
import pytest

import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from ddr2_lpddr2_coverage import (  # noqa: E402
    get_coverage_compile_args, get_coverage_env,
)

from tbclasses.wr2rd_forward_tb import (  # noqa: E402
    Wr2RdForwardTB, Ar,
)


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_wr2rd_forward(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    tb = Wr2RdForwardTB(dut)
    await tb.setup_clocks_and_reset()
    scenarios = {
        "no_match_passthrough":  _no_match_passthrough,
        "match_forward":         _match_forward,
        "multi_match_highest":   _multi_match_highest,
        "partial_strobe_gate":   _partial_strobe_gate,
        "length_mismatch_gate":  _length_mismatch_gate,
        "field_mismatch":        _field_mismatch,
        "random_soak":           _random_soak,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------


async def _no_match_passthrough(tb: Wr2RdForwardTB):
    """Empty CAM → AR must take the rd_push path with its full tuple."""
    tb.clear_all()
    ar = Ar(axid=3, rank=0, bank=1, row=0x100, col=0x40, length=4, qos=7)
    d = await tb.issue_ar(ar)
    assert d.fwd_valid == 0
    assert d.rd_push_valid == 1
    assert d.rd_push_id   == ar.axid
    assert d.rd_push_rank == ar.rank
    assert d.rd_push_bank == ar.bank
    assert d.rd_push_row  == ar.row
    assert d.rd_push_col  == ar.col
    assert d.rd_push_len  == ar.length
    assert d.rd_push_qos  == ar.qos
    assert d.ar_ready == 1   # downstream ready=1 default


async def _match_forward(tb: Wr2RdForwardTB):
    """Single eligible CAM slot → AR must take the fwd path with the
    cam's w_buf_ptr and the AR's id/len."""
    tb.clear_all()
    tb.write_slot(2, rank=0, bank=1, row=0x100, col=0x40, length=4,
                  w_buf_ptr=0x55, full_strb=True)
    ar = Ar(axid=9, rank=0, bank=1, row=0x100, col=0x40, length=4, qos=3)
    d = await tb.issue_ar(ar)
    assert d.fwd_valid == 1
    assert d.fwd_id    == ar.axid
    assert d.fwd_len   == ar.length
    assert d.fwd_w_buf_ptr == 0x55
    assert d.fwd_src_slot  == 2
    assert d.rd_push_valid == 0
    assert d.ar_ready == 1


async def _multi_match_highest(tb: Wr2RdForwardTB):
    """Two eligible slots → the higher slot index wins
    (last-write-wins, by spec)."""
    tb.clear_all()
    tb.write_slot(1, rank=0, bank=2, row=0x200, col=0, length=2,
                  w_buf_ptr=0x10, full_strb=True)
    tb.write_slot(3, rank=0, bank=2, row=0x200, col=0, length=2,
                  w_buf_ptr=0x40, full_strb=True)
    ar = Ar(rank=0, bank=2, row=0x200, col=0, length=2)
    d = await tb.issue_ar(ar)
    assert d.fwd_valid == 1
    assert d.fwd_src_slot == 3, (
        f"highest-slot pick failed: got slot {d.fwd_src_slot}, "
        "expected 3 (newest)")
    assert d.fwd_w_buf_ptr == 0x40


async def _partial_strobe_gate(tb: Wr2RdForwardTB):
    """Eligible slot with full_strb=0 → forward is excluded; AR falls
    through to rd_push (DRAM round trip). Pins the contract that a
    partial-strobe write cannot satisfy a read of the same address."""
    tb.clear_all()
    tb.write_slot(0, rank=0, bank=3, row=0x300, col=0x10, length=1,
                  w_buf_ptr=0x80, full_strb=False)
    ar = Ar(rank=0, bank=3, row=0x300, col=0x10, length=1)
    d = await tb.issue_ar(ar)
    assert d.fwd_valid == 0
    assert d.rd_push_valid == 1, (
        "partial-strobe write should NOT satisfy the read — must fall "
        "through to rd_push"
    )


async def _length_mismatch_gate(tb: Wr2RdForwardTB):
    """Same address, different length → must NOT forward (partial
    coverage of a read would leak uncommitted data)."""
    tb.clear_all()
    tb.write_slot(0, rank=0, bank=4, row=0x400, col=0, length=8,
                  w_buf_ptr=0, full_strb=True)
    ar = Ar(rank=0, bank=4, row=0x400, col=0, length=4)  # AR is shorter
    d = await tb.issue_ar(ar)
    assert d.fwd_valid == 0
    assert d.rd_push_valid == 1


async def _field_mismatch(tb: Wr2RdForwardTB):
    """Differ in any of (rank, bank, row, col) → no forward.
    Iterates one field at a time to confirm each is part of the
    address match."""
    base_slot = dict(rank=0, bank=2, row=0x500, col=0x40, length=1,
                     w_buf_ptr=0x88, full_strb=True)
    base_ar = Ar(rank=0, bank=2, row=0x500, col=0x40, length=1)

    # Sanity: matching baseline forwards
    tb.clear_all()
    tb.write_slot(0, **base_slot)
    assert (await tb.issue_ar(base_ar)).fwd_valid == 1

    # Perturb each field individually
    for field_name, delta in [("bank", 1), ("row", 1), ("col", 4)]:
        tb.clear_all()
        tb.write_slot(0, **base_slot)
        ar = Ar(**{**vars(base_ar),
                   field_name: getattr(base_ar, field_name) + delta})
        d = await tb.issue_ar(ar)
        assert d.fwd_valid == 0, (
            f"forward fired despite {field_name} mismatch — address "
            "check is incomplete"
        )
        assert d.rd_push_valid == 1


async def _random_soak(tb: Wr2RdForwardTB):
    rng = random.Random(tb.SEED ^ 0xF00D)
    n = {'gate': 16, 'func': 64, 'full': 256}.get(
        os.environ.get("TEST_LEVEL", "FUNC").lower(), 64)
    for _ in range(n):
        # Random CAM population
        tb.clear_all()
        n_valid = rng.randint(0, tb.WR_CAM_DEPTH)
        slot_indices = rng.sample(range(tb.WR_CAM_DEPTH), n_valid)
        for i in slot_indices:
            tb.write_slot(
                i,
                rank=rng.randint(0, max(0, tb.NUM_RANKS - 1)),
                bank=rng.randint(0, tb.NUM_BANKS - 1),
                row=rng.randint(0, (1 << tb.ROW_WIDTH) - 1),
                col=rng.randint(0, (1 << tb.COL_WIDTH) - 1),
                length=rng.randint(1, (1 << tb.BURST_LEN_WIDTH) - 1),
                w_buf_ptr=rng.randint(0, (1 << tb.W_BUF_PTR_WIDTH) - 1),
                full_strb=rng.choice([True, False]),
            )
        # Random AR
        ar = Ar(
            axid=rng.randint(0, (1 << tb.AXI_ID_WIDTH) - 1),
            rank=rng.randint(0, max(0, tb.NUM_RANKS - 1)),
            bank=rng.randint(0, tb.NUM_BANKS - 1),
            row=rng.randint(0, (1 << tb.ROW_WIDTH) - 1),
            col=rng.randint(0, (1 << tb.COL_WIDTH) - 1),
            length=rng.randint(1, (1 << tb.BURST_LEN_WIDTH) - 1),
            qos=rng.randint(0, 15),
        )
        d = await tb.issue_ar(ar)
        # Compute expected decision against the Python mirror
        eligible = []
        for i, s in enumerate(tb.slots):
            if (s.valid and s.full_strb
                    and s.rank == ar.rank and s.bank == ar.bank
                    and s.row == ar.row and s.col == ar.col
                    and s.length == ar.length):
                eligible.append(i)
        if eligible:
            pick = eligible[-1]  # highest slot wins
            assert d.fwd_valid == 1
            assert d.fwd_src_slot == pick
            assert d.fwd_id == ar.axid
            assert d.fwd_len == ar.length
            assert d.fwd_w_buf_ptr == tb.slots[pick].w_buf_ptr
            assert d.rd_push_valid == 0
        else:
            assert d.fwd_valid == 0
            assert d.rd_push_valid == 1
            assert d.rd_push_bank == ar.bank
            assert d.rd_push_row  == ar.row
            assert d.rd_push_col  == ar.col


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_ALL_TYPES = ["no_match_passthrough", "match_forward",
              "multi_match_highest", "partial_strobe_gate",
              "length_mismatch_gate", "field_mismatch",
              "random_soak"]
_GATE = [(t,) for t in ["no_match_passthrough", "match_forward",
                        "multi_match_highest"]]
_FUNC = [(t,) for t in _ALL_TYPES]
_FULL = _FUNC

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_wr2rd_forward(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "wr2rd_forward"
    test_name = f"test_wr2rd_forward_{test_type}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/fub/wr2rd_forward.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "WR_CAM_DEPTH":    "4",
        "AXI_ID_WIDTH":    "4",
        "NUM_RANKS":       "1",
        "NUM_BANKS":       "8",
        "ROW_WIDTH":       "14",
        "COL_WIDTH":       "10",
        "BURST_LEN_WIDTH": "8",
        "W_BUF_PTR_WIDTH": "7",
        "SEED": str(random.randint(0, 100000)),
        "TEST_LEVEL": os.environ.get("TEST_LEVEL", "FUNC"),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {
        "WR_CAM_DEPTH":    "4",
        "AXI_ID_WIDTH":    "4",
        "NUM_RANKS":       "1",
        "NUM_BANKS":       "8",
        "ROW_WIDTH":       "14",
        "COL_WIDTH":       "10",
        "BURST_LEN_WIDTH": "8",
        "W_BUF_PTR_WIDTH": "7",
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

    compile_args += get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_wr2rd_forward",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
