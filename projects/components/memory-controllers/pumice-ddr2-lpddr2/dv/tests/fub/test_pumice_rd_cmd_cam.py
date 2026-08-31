# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Pattern-B runner for `pumice_rd_cmd_cam` (read reorder buffer)."""

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
    BL = tb.BL

    def mkdata(tag):
        return [(tag << 8) | i for i in range(BL)]

    dA, dB, dC = mkdata(0xA0), mkdata(0xB0), mkdata(0xC0)

    # insert A,B,C in AR order -> deterministic slots 0,1,2
    await tb.insert(bank=1, row=10, col=5, rid=0xA)  # slot 0
    await tb.insert(bank=2, row=20, col=6, rid=0xB)  # slot 1
    await tb.insert(bank=1, row=10, col=7, rid=0xC)  # slot 2
    await tb.wait_clocks('aclk', 2)

    # oldest not-issued = A
    ov, ob, orow, ocol, oid, oslot = tb.oldest()
    assert ov == 1 and oid == 0xA and oslot == 0, f"oldest {(ov,oid,oslot)} != A/slot0"

    # sched {bank1,row10} oldest not-issued = A (col5)
    res = await tb.sched_query([(1, 1, 10), (1, 2, 20), (1, 5, 5)])
    assert res[0][0] == 1 and res[0][2] == 5 and res[0][3] == 0xA, f"sched A {res[0]}"
    assert res[1][0] == 1 and res[1][3] == 0xB, f"sched B {res[1]}"
    assert res[2][0] == 0, "sched {bank5,row5} miss"

    # ISSUE in reordered order: B, A, C
    await tb.issue(1)   # B
    await tb.issue(0)   # A
    await tb.issue(2)   # C
    await tb.wait_clocks('aclk', 2)

    # everything issued -> oldest not-issued empty
    assert tb.oldest()[0] == 0, "oldest not-issued should be empty after all issued"

    # DFI returns in ISSUE order: B, A, C
    await tb.dfi_return(dB)
    await tb.dfi_return(dA)
    await tb.dfi_return(dC)

    # drain must release in AR order: A, B, C (the reorder)
    for _ in range(400):
        if len(tb.drain_out) >= 3:
            break
        await tb.wait_clocks('aclk', 1)
    assert len(tb.drain_out) == 3, f"drain bursts {len(tb.drain_out)} != 3"

    exp = [(0xA, dA), (0xB, dB), (0xC, dC)]
    for k, (want_id, want_data) in enumerate(exp):
        burst = tb.drain_out[k]
        got_ids = {b[0] for b in burst}
        got_data = [b[1] for b in burst]
        assert got_ids == {want_id}, f"drain {k}: id {got_ids} != {want_id}"
        assert got_data == want_data, f"drain {k}: data {got_data} != {want_data}"

    # =====================================================================
    # sch_head_rel_o -- the scheduler's cross-CAM ordering key
    # =====================================================================
    # This output had NO value coverage: every test drove it as an arbiter
    # INPUT and nothing checked the CAM's computation of it. It was rewritten
    # (PUMICE-017) from a serial max-reduce over w_rel[] -- which put the
    # free-running age counter on the scheduling critical path and cost the
    # design 63.6 ns against a 15 ns period -- to an oldest-via-age-order-matrix
    # pick plus a single subtract. Identical value, so it needs a test that
    # would notice if it were not.
    #
    # Checked behaviourally rather than against absolute cycle counts, so the
    # test does not encode the CAM's internal insert latency:
    #   1. nothing schedulable                 -> 0
    #   2. one entry, then a younger one       -> tracks the OLDER
    #   3. free-running                        -> +1 per clock, exactly
    #   4. retire the oldest                   -> DROPS to the younger's age
    # Pulse reset to clear the entries the earlier phases left behind. NOT
    # setup_clocks_and_reset() -- that would start a second clock driver.
    await tb.assert_reset()
    await tb.wait_clocks('aclk', 4)
    await tb.deassert_reset()
    await tb.wait_clocks('aclk', 4)

    assert tb.head_rel() == 0, (
        f"empty CAM must report head_rel 0, got {tb.head_rel()}")

    await tb.insert(bank=3, row=30, col=1, rid=0x1)     # older
    await tb.wait_clocks('aclk', 8)
    await tb.insert(bank=4, row=40, col=2, rid=0x2)     # younger
    await tb.wait_clocks('aclk', 2)

    h_old = tb.head_rel()
    assert h_old >= 8, (
        f"head_rel must track the OLDER entry (inserted 10+ cycles ago), "
        f"got {h_old} -- a value near 0 means it is reporting the YOUNGER one")

    # Free-running: exactly +1 per clock. This is the property that separates
    # a real age from a constant or a stale capture.
    await tb.wait_clocks('aclk', 1)
    h_next = tb.head_rel()
    assert h_next == h_old + 1, (
        f"head_rel must advance exactly 1 per clock: {h_old} -> {h_next}")

    # Retire the older entry. head_rel must fall back to the younger one, which
    # is strictly newer -- so the value DROPS. A selector stuck on slot 0, or
    # one ignoring the schedulable predicate, keeps climbing here.
    await tb.issue(0)
    await tb.wait_clocks('aclk', 2)
    h_after = tb.head_rel()
    assert h_after < h_next, (
        f"after issuing the oldest, head_rel must drop to the younger entry's "
        f"age: {h_next} -> {h_after}")
    assert h_after > 0, f"the younger entry is still schedulable, got {h_after}"

    tb.log.info("PASS: sch_head_rel_o tracks the oldest schedulable entry "
                "(older=%d, +1/clk=%d, after-retire=%d)",
                h_old, h_next, h_after)

    tb.log.info("PASS: insert(AR) / issue(reordered B,A,C) / return(issue-order) "
                "-> drain(AR-order A,B,C); oldest + sched lookups verified")


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
        "AXI_DATA_WIDTH": "64",
        "AXI_BEATS_PER_BURST":            "4",
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
