# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Pattern-B runner for `pumice_rd_intake` (dumb AXI4 read intake + snarf).

Drives a mix of snarf-HIT and MISS reads (one AR at a time so snarf_hit_i
tracks the probed AR) and checks:
  * MISS -> ar_push emitted (decoded, correct id); R sourced from DFI return.
  * HIT  -> no ar_push; R sourced from the snarf stream.
  * R returns in AR order across an interleave of both sources.
"""

import os
import sys
import random

import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from pumice_coverage import get_coverage_compile_args, get_coverage_env  # noqa: E402
from tbclasses.pumice_rd_intake_tb import PumiceRdIntakeTB, RESP_OKAY  # noqa: E402

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/fub/pumice_rd_intake.f")


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_pumice_rd_intake(dut):
    tb = PumiceRdIntakeTB(dut)
    await tb.setup_clocks_and_reset()

    level = os.environ.get("TEST_LEVEL", "basic").lower()
    n = {"basic": 6, "medium": 24, "full": 64}.get(level, 6)
    rng = random.Random(int(os.environ.get("SEED", "1")))

    # Keep hit and miss key-spaces disjoint: bit 18 of the word address (a row
    # bit) discriminates, so a MISS can never collide with a prior HIT in the
    # persistent hit-set.
    reads = []
    for k in range(n):
        hit  = (rng.random() < 0.5)
        rid  = rng.randint(0, 15)
        word = rng.randint(0, (1 << 18) - 1) | ((1 << 18) if hit else 0)
        addr = word << tb.BYTE_OFFSET_WIDTH
        data = [rng.randrange(1 << tb.AXI_DATA_WIDTH) for _ in range(tb.EXP_BEATS)]
        reads.append((addr, rid, hit, data))
        await tb.read_burst(addr, rid, hit, data)

    # drain
    total = n * tb.EXP_BEATS
    for _ in range(4000):
        if len(tb.r_beats) >= total:
            break
        await tb.wait_clocks('aclk', 1)
    assert len(tb.r_beats) == total, \
        f"R beat count {len(tb.r_beats)} != {total}"

    # ar_push: one per MISS, in order
    misses = [(addr, rid) for (addr, rid, hit, _d) in reads if not hit]
    assert len(tb.ar_push) == len(misses), \
        f"ar_push count {len(tb.ar_push)} != miss count {len(misses)}"
    for (rank, bank, row, col, pid), (addr, rid) in zip(tb.ar_push, misses):
        assert (rank, bank, row, col) == tb.decode(addr), \
            f"ar_push decode {(rank,bank,row,col)} != {tb.decode(addr)}"
        assert pid == rid, f"ar_push id {pid} != {rid}"

    # R: bursts in AR order, correct data/id/last/resp
    idx = 0
    for bk, (addr, rid, hit, data) in enumerate(reads):
        for i, d in enumerate(data):
            gid, gd, gl, gr = tb.r_beats[idx]
            idx += 1
            assert gid == rid, f"read {bk} beat {i}: rid {gid} != {rid}"
            assert gd == d, f"read {bk} beat {i}: rdata {gd:#x} != {d:#x}"
            assert gl == (1 if i == tb.EXP_BEATS - 1 else 0), \
                f"read {bk} beat {i}: rlast {gl}"
            assert gr == RESP_OKAY, f"read {bk} beat {i}: rresp {gr}"

    n_hit = sum(1 for r in reads if r[2])
    tb.log.info(f"PASS: {n} reads ({n_hit} snarf, {n - n_hit} DFI), "
                f"{total} R beats in order")


def test_pumice_rd_intake(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_rd_intake"
    test_name = "cocotb_test_pumice_rd_intake"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST
    )

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")
    os.makedirs(log_dir, exist_ok=True)

    params = {
        "AXI_DATA_WIDTH":  "64",
        "NUM_RANKS":       "1",
        "NUM_BANKS":       "8",
        "ROW_WIDTH":       "14",
        "COL_WIDTH":       "10",
        "BYTE_OFFSET_WIDTH": "3",
        "AXI_BEATS_PER_BURST":              "4",
    }
    extra_env = {
        "DUT": dut_name,
        "LOG_PATH": log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
        "TEST_LEVEL": os.environ.get("TEST_LEVEL", "basic").lower(),
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
        testcase="cocotb_test_pumice_rd_intake",
        sim_build=sim_build,
        simulator="verilator",
        extra_env=extra_env,
        parameters=params,
        compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        timescale="1ns/1ps",
    )
