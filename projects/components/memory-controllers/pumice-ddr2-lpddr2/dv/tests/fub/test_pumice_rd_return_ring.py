# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Pattern-B runner for `pumice_rd_return_ring` (AR-order read-return ring)."""

import os
import sys
import random

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from pumice_coverage import get_coverage_compile_args, get_coverage_env  # noqa: E402
from tbclasses.pumice_rd_return_ring_tb import PumiceRdReturnRingTB  # noqa: E402

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "dv/tb/pumice_rd_return_ring_tb_top.f")


def _burst(tb, tag):
    return [((tag & 0xFFFF) << 8) | i for i in range(tb.BL)]


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_pumice_rd_return_ring(dut):
    tb = PumiceRdReturnRingTB(dut)
    await tb.setup_clocks_and_reset()
    D = tb.DEPTH

    # ---- 1. reorder: alloc A,B,C; issue B,A,C; return B,A,C; drain A,B,C ----
    tA = await tb.alloc()
    tB = await tb.alloc()
    tC = await tb.alloc()
    assert (tA, tB, tC) == (0, 1, 2), f"tickets {(tA, tB, tC)} != alloc order 0,1,2"
    assert tb.occ() == 3, f"occ {tb.occ()} != 3 after 3 allocs"

    dA, dB, dC = _burst(tb, 0xA0), _burst(tb, 0xB0), _burst(tb, 0xC0)
    await tb.issue(tB)
    await tb.issue(tA)
    await tb.issue(tC)
    await tb.dfi_return(dB, resp=0)
    await tb.dfi_return(dA, resp=2)          # SLVERR rides with A
    await tb.dfi_return(dC, resp=0)
    await tb.wait_drained(3)
    got = [[d for d, _ in b] for b in tb.drain_out]
    assert got == [dA, dB, dC], f"drain order/data {got} != AR order A,B,C"
    resps = [{r for _, r in b} for b in tb.drain_out]
    assert resps == [{2}, {0}, {0}], f"resp per burst {resps} != [{{2}},{{0}},{{0}}]"
    tb.drain_out.clear()
    await tb.wait_clocks('aclk', 4)
    assert tb.occ() == 0, f"occ {tb.occ()} != 0 after full drain (slots not freed)"

    # ---- 2. an older slot NOT ready must hold a younger READY slot ---------
    t0 = await tb.alloc()
    t1 = await tb.alloc()
    await tb.issue(t1)                        # only the YOUNGER read issues
    await tb.dfi_return(_burst(tb, 0x11))     # ...and returns, complete
    await tb.wait_clocks('aclk', 20)
    assert tb.drain_valid() == 0 and len(tb.drain_out) == 0, (
        "drain released the younger slot ahead of an older, not-returned one "
        "-- AR order broken")
    await tb.issue(t0)
    await tb.dfi_return(_burst(tb, 0x10))
    await tb.wait_drained(2)
    got = [[d for d, _ in b] for b in tb.drain_out]
    assert got == [_burst(tb, 0x10), _burst(tb, 0x11)], f"drain {got} != [0x10.., 0x11..]"
    tb.drain_out.clear()
    await tb.wait_clocks('aclk', 4)

    # ---- 3. partial head: BL-1 beats of the head must not drain -----------
    if tb.BL > 1:
        t = await tb.alloc()
        await tb.issue(t)
        for i in range(tb.BL - 1):
            await tb.dfi_ret_bfm.send(tb.dfi_ret_bfm.create_packet(
                data=(0x4400 | i), resp=0, last=0))
        await tb.wait_clocks('aclk', 10)
        assert tb.drain_valid() == 0 and len(tb.drain_out) == 0, (
            "head slot drained with only BL-1 beats returned")
        await tb.dfi_ret_bfm.send(tb.dfi_ret_bfm.create_packet(
            data=(0x4400 | (tb.BL - 1)), resp=0, last=1))
        await tb.wait_drained(1)
        assert [d for d, _ in tb.drain_out[0]] == [0x4400 | i for i in range(tb.BL)]
        tb.drain_out.clear()
        await tb.wait_clocks('aclk', 4)

    # ---- 4. full: DEPTH allocations block the next; a free re-opens it -----
    ts = []
    for _ in range(D):
        ts.append(await tb.alloc())
    await tb.wait_clocks('aclk', 2)
    assert tb.alloc_ready() == 0, f"alloc_ready still 1 with {D}/{D} allocated"
    assert tb.occ() == D
    # complete and drain only the HEAD; ready must return
    await tb.issue(ts[0])
    await tb.dfi_return(_burst(tb, 0x50 + ts[0]))
    await tb.wait_drained(1)
    await tb.wait_clocks('aclk', 3)
    assert tb.alloc_ready() == 1, "alloc_ready did not return after the head freed"
    # complete the rest in a scrambled issue order, then drain must be in order
    rest = ts[1:]
    order = rest[:]
    random.Random(1).shuffle(order)
    for t in order:
        await tb.issue(t)
    for t in order:
        await tb.dfi_return(_burst(tb, 0x50 + t))
    await tb.wait_drained(D)
    got = [[d for d, _ in b] for b in tb.drain_out]
    exp = [_burst(tb, 0x50 + t) for t in ts]
    assert got == exp, "drain after a full ring is not in alloc order"
    tb.drain_out.clear()
    await tb.wait_clocks('aclk', 4)
    assert tb.occ() == 0

    # ---- 5. wrap + backpressure: 3*DEPTH reads, random issue windows ------
    rng = random.Random(int(os.environ.get("SEED", "5")))
    N = 3 * D
    tb.set_drain_ready(False)
    exp = []
    inflight = []
    n_alloc = 0
    n_issued = 0
    while n_issued < N:
        # allocate while there is room (never more than D outstanding)
        while n_alloc < N and tb.alloc_ready() and len(inflight) < D:
            t = await tb.alloc()
            inflight.append((t, _burst(tb, 0x100 + n_alloc)))
            exp.append(_burst(tb, 0x100 + n_alloc))
            n_alloc += 1
        # issue a random one of the allocated-not-issued, return it
        if inflight:
            k = rng.randrange(len(inflight))
            t, d = inflight.pop(k)
            await tb.issue(t)
            await tb.dfi_return(d)
            n_issued += 1
        if n_issued == D:                     # release the sink mid-run
            tb.set_drain_ready(True)
        if not inflight and n_alloc < N and not tb.alloc_ready():
            await RisingEdge(dut.aclk)
    tb.set_drain_ready(True)
    await tb.wait_drained(N, limit=20000)
    got = [[d for d, _ in b] for b in tb.drain_out]
    assert got == exp, "wrap/backpressure run: drain order or data mismatch"
    await tb.wait_clocks('aclk', 4)
    assert tb.occ() == 0, f"occ {tb.occ()} != 0 at the end"
    tb.log.info("PASS: reorder, AR-order hold, partial head, full/free, wrap x3 with backpressure")


_CFGS = [("d8_b4", 8, 4), ("d8_b1", 8, 1), ("d32_b4", 32, 4)]


@pytest.mark.parametrize("cfg", _CFGS, ids=[c[0] for c in _CFGS])
def test_pumice_rd_return_ring(request, cfg):
    name, depth, beats = cfg
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_rd_return_ring_tb_top"
    test_name = f"cocotb_test_pumice_rd_return_ring_{name}"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST
    )
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")
    os.makedirs(log_dir, exist_ok=True)

    params = {
        "DEPTH":               str(depth),
        "AXI_DATA_WIDTH":      "64",
        "AXI_BEATS_PER_BURST": str(beats),
    }
    extra_env = {
        "DUT": dut_name,
        "LOG_PATH": log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    extra_env.update(params)

    compile_args = ["+define+USE_ASYNC_RESET"] + get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_pumice_rd_return_ring",
        sim_build=sim_build,
        simulator="verilator",
        extra_env=extra_env,
        parameters=params,
        compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        timescale="1ns/1ps",
    )
