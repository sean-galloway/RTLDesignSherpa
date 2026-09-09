# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Pattern-B runner for `pumice_rd_cmd_cam` (read scheduling window)."""

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
from tbclasses.pumice_rd_cmd_cam_tb import PumiceRdCmdCamTB  # noqa: E402

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/fub/pumice_rd_cmd_cam.f")


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_pumice_rd_cmd_cam(dut):
    tb = PumiceRdCmdCamTB(dut)
    await tb.setup_clocks_and_reset()
    N = tb.NUM_ENTRIES

    # insert A,B,C in AR order -> deterministic slots 0,1,2, tickets 10,11,12
    await tb.insert(bank=1, row=10, col=5, rid=0xA, ticket=10)  # slot 0
    await tb.insert(bank=2, row=20, col=6, rid=0xB, ticket=11)  # slot 1
    await tb.insert(bank=1, row=10, col=7, rid=0xC, ticket=12)  # slot 2
    await tb.wait_clocks('aclk', 2)
    assert tb.sch_valid() == 0b111, f"sch_valid {tb.sch_valid():#b} != 0b111"

    # oldest = A
    ov, ob, orow, ocol, oid, oslot = tb.oldest()
    assert ov == 1 and oid == 0xA and oslot == 0, f"oldest {(ov,oid,oslot)} != A/slot0"

    # sched {bank1,row10} oldest = A (col5)
    res = await tb.sched_query([(1, 1, 10), (1, 2, 20), (1, 5, 5)])
    assert res[0][0] == 1 and res[0][2] == 5 and res[0][3] == 0xA, f"sched A {res[0]}"
    assert res[1][0] == 1 and res[1][3] == 0xB, f"sched B {res[1]}"
    assert res[2][0] == 0, "sched {bank5,row5} miss"

    # ISSUE B (reordered): its TICKET goes out on iss_*, its entry FREES
    await tb.issue(1)
    await tb.wait_iss(1)
    assert list(tb.iss_out) == [11], f"iss tickets {list(tb.iss_out)} != [11]"
    await tb.wait_clocks('aclk', 1)
    assert tb.sch_valid() == 0b101, f"sch_valid {tb.sch_valid():#b} != 0b101 after issuing slot 1"
    # oldest is still A; {bank2,row20} now misses
    assert tb.oldest()[4] == 0xA
    res = await tb.sched_query([(1, 2, 20)])
    assert res[0][0] == 0, "issued entry still matched a sched lookup"

    # the freed slot is reusable: D lands in slot 1 with its own ticket
    await tb.insert(bank=3, row=30, col=8, rid=0xD, ticket=13)
    await tb.wait_clocks('aclk', 2)
    assert tb.sch_valid() == 0b111, f"sch_valid {tb.sch_valid():#b} != 0b111 after reuse"
    res = await tb.sched_query([(1, 3, 30)])
    assert res[0][0] == 1 and res[0][1] == 1 and res[0][3] == 0xD, f"D not in slot 1: {res[0]}"

    # issue A, C, D -> tickets in issue order, window empty
    await tb.issue(0)
    await tb.issue(2)
    await tb.issue(1)
    await tb.wait_iss(4)
    assert list(tb.iss_out) == [11, 10, 12, 13], f"iss tickets {list(tb.iss_out)}"
    await tb.wait_clocks('aclk', 1)
    assert tb.sch_valid() == 0 and tb.oldest()[0] == 0, "window not empty after issuing all"
    tb.iss_out.clear()

    # ---- window full: N inserts block the (N+1)th until an issue frees one --
    for k in range(N):
        await tb.insert(bank=k % tb.NUM_BANKS, row=100 + k, col=k, rid=0x20 + k, ticket=k)
    await tb.wait_clocks('aclk', 2)
    assert tb.sch_valid() == (1 << N) - 1
    assert tb.ins_ready() == 0, f"ins_ready still 1 with {N}/{N} entries"
    await tb.issue(3)
    await tb.wait_iss(1)
    assert list(tb.iss_out) == [3]
    await tb.wait_clocks('aclk', 1)
    assert tb.ins_ready() == 1, "ins_ready did not return after an issue freed a slot"
    tb.iss_out.clear()

    # ---- downstream backpressure on iss_* holds issue_ready (no ticket lost) --
    tb.set_iss_ready(False)
    await tb.wait_clocks('aclk', 2)
    assert int(dut.issue_ready_o.value) == 0, "issue_ready must follow iss_ready (ring issue_q)"
    tb.set_iss_ready(True)
    for k in range(N):
        if k != 3:
            await tb.issue(k)
    await tb.wait_iss(N - 1)
    assert sorted(tb.iss_out) == sorted(k for k in range(N) if k != 3), f"tickets {list(tb.iss_out)}"
    await tb.wait_clocks('aclk', 1)
    assert tb.sch_valid() == 0

    # =====================================================================
    # sch_head_rel_o -- the scheduler's cross-CAM ordering key
    # =====================================================================
    # Checked behaviourally rather than against absolute cycle counts:
    #   1. nothing schedulable                 -> 0
    #   2. one entry, then a younger one       -> tracks the OLDER
    #   3. free-running                        -> +1 per clock, exactly
    #   4. issue the oldest                    -> DROPS to the younger's age
    await tb.assert_reset()
    await tb.wait_clocks('aclk', 4)
    await tb.deassert_reset()
    await tb.wait_clocks('aclk', 4)

    assert tb.head_rel() == 0, (
        f"empty CAM must report head_rel 0, got {tb.head_rel()}")

    await tb.insert(bank=3, row=30, col=1, rid=0x1, ticket=1)     # older
    await tb.wait_clocks('aclk', 8)
    await tb.insert(bank=4, row=40, col=2, rid=0x2, ticket=2)     # younger
    await tb.wait_clocks('aclk', 2)

    h_old = tb.head_rel()
    assert h_old >= 8, (
        f"head_rel must track the OLDER entry (inserted 10+ cycles ago), "
        f"got {h_old} -- a value near 0 means it is reporting the YOUNGER one")

    await tb.wait_clocks('aclk', 1)
    h_next = tb.head_rel()
    assert h_next == h_old + 1, (
        f"head_rel must advance exactly 1 per clock: {h_old} -> {h_next}")

    await tb.issue(0)
    await tb.wait_clocks('aclk', 2)
    h_after = tb.head_rel()
    assert h_after < h_next, (
        f"after issuing the oldest, head_rel must drop to the younger entry's "
        f"age: {h_next} -> {h_after}")
    assert h_after > 0, f"the younger entry is still schedulable, got {h_after}"

    tb.log.info("PASS: insert(AR)+ticket / issue frees + forwards ticket / reuse / "
                "full window / iss backpressure / oldest + sched lookups / head_rel")


def test_pumice_rd_cmd_cam(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_rd_cmd_cam"
    test_name = "cocotb_test_pumice_rd_cmd_cam"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST
    )
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")
    os.makedirs(log_dir, exist_ok=True)

    params = {
        "NUM_ENTRIES":   "8",
        "N_SCHED_LU":    "4",
        "NUM_BANKS":     "8",
        "ROW_WIDTH":     "14",
        "COL_WIDTH":     "10",
        "AXI_ID_WIDTH":  "8",
        "RD_RET_DEPTH":  "32",
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
        testcase="cocotb_test_pumice_rd_cmd_cam",
        sim_build=sim_build,
        simulator="verilator",
        extra_env=extra_env,
        parameters=params,
        compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        timescale="1ns/1ps",
    )
