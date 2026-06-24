# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit-test runner for `axi_id_side_table`.

The block is `integration_tested` in the testplans (no direct FUB test
existed before this), but the four lookup contracts — `aw_push_qos`,
`aw_compl_user`, `ar_push_qos`, `ar_compl_user` — are not asserted at
the macro level either. A silent regression (e.g. forcing the lookup
output to 0, or collapsing all IDs to slot 0) would propagate into
the AXI B/R channel as a dropped user/qos echo with no test failure.

These scenarios pin each contract directly.
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

from tbclasses.axi_id_side_table_tb import (  # noqa: E402
    AxiIdSideTableTB, Meta,
)


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_axi_id_side_table(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    tb = AxiIdSideTableTB(dut)
    await tb.setup_clocks_and_reset()
    scenarios = {
        "smoke":            _smoke,
        "all_fields":       _all_fields,
        "id_reuse":         _id_reuse,
        "channel_isolate":  _channel_isolate,
        "random_soak":      _random_soak,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------


async def _smoke(tb: AxiIdSideTableTB):
    """Single AW + single AR with distinct user/qos round-trip cleanly."""
    await tb.write_aw(axid=3, m=Meta(user=0xA5, qos=7))
    await tb.write_ar(axid=5, m=Meta(user=0x5A, qos=11))
    await tb.settle()
    assert await tb.lookup_aw_push_qos(3)   == 7
    assert await tb.lookup_aw_compl_user(3) == 0xA5
    assert await tb.lookup_ar_push_qos(5)   == 11
    assert await tb.lookup_ar_compl_user(5) == 0x5A


async def _all_fields(tb: AxiIdSideTableTB):
    """Several distinct IDs with distinct metadata — confirms the
    AW/AR push/compl lookups *return the captured value* and not 0.
    A regression collapsing all lookups onto slot 0 would fail every
    non-zero ID here."""
    rng = random.Random(tb.SEED ^ 0xAB12)
    ids = [1, 2, 3, 5, 7, 11]
    ids = [i & tb.MASK_ID for i in ids]
    aw_metas = {axid: Meta(user=rng.randint(1, tb.MASK_USER), qos=axid & 0xF)
                for axid in ids}
    ar_metas = {axid: Meta(user=rng.randint(1, tb.MASK_USER),
                           qos=(axid * 3) & 0xF)
                for axid in ids}
    for axid in ids:
        await tb.write_aw(axid, aw_metas[axid])
        await tb.write_ar(axid, ar_metas[axid])
    await tb.settle()
    for axid in ids:
        got_aq = await tb.lookup_aw_push_qos(axid)
        got_au = await tb.lookup_aw_compl_user(axid)
        got_rq = await tb.lookup_ar_push_qos(axid)
        got_ru = await tb.lookup_ar_compl_user(axid)
        assert got_aq == aw_metas[axid].qos, (
            f"id={axid} aw_push_qos got {got_aq:#x} "
            f"want {aw_metas[axid].qos:#x}")
        assert got_au == aw_metas[axid].user, (
            f"id={axid} aw_compl_user got {got_au:#x} "
            f"want {aw_metas[axid].user:#x}")
        assert got_rq == ar_metas[axid].qos, (
            f"id={axid} ar_push_qos got {got_rq:#x} "
            f"want {ar_metas[axid].qos:#x}")
        assert got_ru == ar_metas[axid].user, (
            f"id={axid} ar_compl_user got {got_ru:#x} "
            f"want {ar_metas[axid].user:#x}")


async def _id_reuse(tb: AxiIdSideTableTB):
    """Second write with same ID overwrites the first. Real AXI in-
    order semantics make this safe; pin it so a future "preserve old
    entry" misfire doesn't silently leak stale meta to the new
    completion."""
    await tb.write_aw(axid=2, m=Meta(user=0x11, qos=1))
    await tb.settle()
    assert await tb.lookup_aw_compl_user(2) == 0x11
    await tb.write_aw(axid=2, m=Meta(user=0x22, qos=2))
    await tb.settle()
    assert await tb.lookup_aw_compl_user(2) == 0x22
    assert await tb.lookup_aw_push_qos(2)   == 2


async def _channel_isolate(tb: AxiIdSideTableTB):
    """AW writes to id=X must not perturb AR's lookup of id=X, and vice
    versa — the two tables are independent."""
    await tb.write_aw(axid=4, m=Meta(user=0xAA, qos=15))
    await tb.write_ar(axid=4, m=Meta(user=0xBB, qos=3))
    await tb.settle()
    assert await tb.lookup_aw_compl_user(4) == 0xAA
    assert await tb.lookup_ar_compl_user(4) == 0xBB
    assert await tb.lookup_aw_push_qos(4)   == 15
    assert await tb.lookup_ar_push_qos(4)   == 3


async def _random_soak(tb: AxiIdSideTableTB):
    """Random sequence of AW/AR writes, then read back every touched
    ID. The Python-side scoreboard mirrors the FUB exactly."""
    rng = random.Random(tb.SEED ^ 0xC0DE)
    n = {'gate': 16, 'func': 64, 'full': 256}.get(
        os.environ.get("TEST_LEVEL", "FUNC").lower(), 64)
    aw_sb = {}
    ar_sb = {}
    for _ in range(n):
        is_aw = rng.choice([True, False])
        axid  = rng.randint(0, tb.MASK_ID)
        m = Meta(user=rng.randint(0, tb.MASK_USER),
                 qos=rng.randint(0, 15))
        if is_aw:
            await tb.write_aw(axid, m)
            aw_sb[axid] = m
        else:
            await tb.write_ar(axid, m)
            ar_sb[axid] = m
    await tb.settle()
    for axid, m in aw_sb.items():
        assert await tb.lookup_aw_push_qos(axid)   == m.qos
        assert await tb.lookup_aw_compl_user(axid) == m.user
    for axid, m in ar_sb.items():
        assert await tb.lookup_ar_push_qos(axid)   == m.qos
        assert await tb.lookup_ar_compl_user(axid) == m.user


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_ALL_TYPES = ["smoke", "all_fields", "id_reuse",
              "channel_isolate", "random_soak"]
_GATE = [(t,) for t in ["smoke", "all_fields", "id_reuse"]]
_FUNC = [(t,) for t in _ALL_TYPES]
_FULL = _FUNC

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_axi_id_side_table(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "axi_id_side_table"
    test_name = f"test_axi_id_side_table_{test_type}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/fub/axi_id_side_table.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "AXI_ID_WIDTH":   "4",
        "AXI_USER_WIDTH": "8",
        "SEED": str(random.randint(0, 100000)),
        "TEST_LEVEL": os.environ.get("TEST_LEVEL", "FUNC"),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET"]
    sim_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    compile_args += get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    parameters = {
        "AXI_ID_WIDTH":   "4",
        "AXI_USER_WIDTH": "8",
    }

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_axi_id_side_table",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
