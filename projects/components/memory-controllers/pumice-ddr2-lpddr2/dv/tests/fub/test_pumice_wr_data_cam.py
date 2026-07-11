# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Pattern-B runner for `pumice_wr_data_cam`."""

import os
import sys
import random

import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from pumice_coverage import get_coverage_compile_args, get_coverage_env  # noqa: E402
from tbclasses.pumice_wr_data_cam_tb import PumiceWrDataCamTB  # noqa: E402

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/fub/pumice_wr_data_cam.f")


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_pumice_wr_data_cam(dut):
    tb = PumiceWrDataCamTB(dut)
    await tb.setup_clocks_and_reset()
    BL = tb.BL
    rng = random.Random(int(os.environ.get("SEED", "1")))

    def mkdata(tag):
        return [(tag << 8) | i for i in range(BL)]

    d0 = mkdata(0xA0)
    d1 = mkdata(0xB0)
    d2 = mkdata(0xC0)
    dW = mkdata(0xD0)

    # insert 3 distinct entries (0 and 2 share {bank1,row10})
    await tb.write_entry(bank=1, row=10, col=5, wid=0xA, data=d0)
    await tb.write_entry(bank=2, row=20, col=6, wid=0xB, data=d1)
    await tb.write_entry(bank=1, row=10, col=7, wid=0xC, data=d2)
    await tb.wait_clocks('aclk', 2)

    # oldest = entry0 (first inserted)
    ov, ob, orow, ocol, oid, oslot = tb.oldest()
    assert ov == 1 and (ob, orow, ocol, oid) == (1, 10, 5, 0xA), \
        f"oldest {(ov,ob,orow,ocol,oid)} != entry0"

    # snarf entry1 -> d1 (matching id 0xB, matching len)
    hit, burst = await tb.snarf(2, 20, 6, rid=0xB)
    assert hit and burst == d1, f"snarf entry1 hit={hit} burst={burst} != {d1}"

    # snarf miss (unknown address)
    hit, _ = await tb.snarf(7, 99, 1, rid=0x0)
    assert hit == 0, "snarf should miss on unknown address"

    # LIMIT 1 — id mismatch: right address but wrong AXI id must NOT snarf
    hit, _ = await tb.snarf(2, 20, 6, rid=0x3)
    assert hit == 0, "snarf must miss on id mismatch (cross-id has no ordering)"

    # LIMIT 2 — burst-length mismatch: right addr+id but arlen != BL-1 must NOT snarf
    hit, _ = await tb.snarf(2, 20, 6, rid=0xB, arlen=0)
    assert hit == 0, "snarf must miss when read burst length != write burst length"

    # WAW: new write to entry0's exact key -> snarf returns YOUNGEST (dW), id 0xD
    await tb.write_entry(bank=1, row=10, col=5, wid=0xD, data=dW)
    await tb.wait_clocks('aclk', 2)
    hit, burst = await tb.snarf(1, 10, 5, rid=0xD)
    assert hit and burst == dW, f"WAW snarf youngest hit={hit} burst={burst} != {dW}"

    # scheduler lookups
    res = await tb.sched_query([(1, 1, 10), (1, 2, 20), (0, 0, 0), (1, 5, 5)])
    assert res[0][0] == 1 and res[0][2] == 5 and res[0][3] == 0xA, \
        f"sched {{bank1,row10}} oldest-match {res[0]} != col5/idA"
    assert res[1][0] == 1 and res[1][3] == 0xB, f"sched {{bank2,row20}} {res[1]}"
    assert res[2][0] == 0, "disabled query must not hit"
    assert res[3][0] == 0, "sched {bank5,row5} should miss"

    # commit the oldest (entry0) -> stream d0, evict, oldest advances
    burst = await tb.commit(oslot)
    assert burst == d0, f"commit burst {burst} != {d0}"
    await tb.wait_clocks('aclk', 3)
    ov2, ob2, orow2, ocol2, oid2, _ = tb.oldest()
    assert ov2 == 1 and oid2 == 0xB, \
        f"after committing entry0, oldest id {oid2} != 0xB (entry1)"

    # LIMIT 3 — scheduled write must NOT snarf. Fresh entry; mark-commit it while
    # holding the drain (cm_rd_ready=0) so it stays valid+scheduled, then probe.
    dE = mkdata(0xE0)
    await tb.write_entry(bank=3, row=30, col=8, wid=0xE, data=dE)
    await tb.wait_clocks('aclk', 2)
    res = await tb.sched_query([(1, 3, 30)])
    assert res[0][0] == 1, "fresh entry should be sched-visible before commit"
    eE_slot = res[0][1]
    # confirm it snarfs BEFORE being scheduled
    hit, _ = await tb.snarf(3, 30, 8, rid=0xE)
    assert hit == 1, "unscheduled fresh write should snarf"
    tb.dut.cm_rd_ready_i.value = 0                 # freeze the drain
    while int(tb.dut.commit_ready_o.value) == 0:
        await tb.wait_clocks('aclk', 1)
    tb.dut.commit_slot_i.value = eE_slot
    tb.dut.commit_valid_i.value = 1
    await tb.wait_clocks('aclk', 1)
    tb.dut.commit_valid_i.value = 0
    await tb.wait_clocks('aclk', 2)                # r_sched set; entry still valid
    hit, _ = await tb.snarf(3, 30, 8, rid=0xE)
    assert hit == 0, "snarf must miss on a scheduled (committing) write"
    tb.dut.cm_rd_ready_i.value = 1                 # release; let it drain/evict
    for _ in range(200):
        await tb.wait_clocks('aclk', 1)
        if tb.cm_out:
            tb.cm_out.popleft()
            break

    tb.log.info("PASS: insert/fill, oldest port, snarf youngest (WAW), snarf "
                "limits (id/len/scheduled), sched oldest-match, commit+evict")


def test_pumice_wr_data_cam(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_wr_data_cam"
    test_name = "cocotb_test_pumice_wr_data_cam"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST
    )
    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
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
        "BL":            "4",
    }
    extra_env = {
        "DUT": dut_name,
        "LOG_PATH": log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        "SEED": str(random.randint(0, 100000)),
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
        testcase="cocotb_test_pumice_wr_data_cam",
        sim_build=sim_build,
        simulator="verilator",
        extra_env=extra_env,
        parameters=params,
        compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        timescale="1ns/1ps",
    )
