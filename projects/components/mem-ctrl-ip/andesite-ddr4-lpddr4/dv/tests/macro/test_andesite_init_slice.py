# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""P1 gate -- the andesite init slice walks the DFI 4.0 BFM at DDR4-1600.

The BFM (RTLDesignSherpa-DV, DFIVersion.V4_0, MemoryType.DDR4, the vendored
jedec/ddr4-1600.csv profile) is the counterparty; the DFI-pin monitor decodes
the command stream with the kmap truth table and the shared order checker
(HAS ch06 item 1) proves the anchored init order AT THE BOUNDARY. HARD
violations raise inside the sim; SOFT counts are asserted empty. The
gear-down configuration exercises the BFM's geardown behavior (G3-closed).

CSR waits use the fixed JEDEC command-table constants in nCK converted to
MC clocks at the TB's 1:1 clock ratio (tMRD=8, tMOD=24, tDLLK=768,
tZQinit=1024); the AC timing profile itself is the CSV's. tINIT* waits are
test-scaled -- the DRAM state model polices the command stream, not the
reset-duration windows (Q1 covers the cold-storage confirmation of every
value).
"""

import os
import random
import sys

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.andesite_init_tb import AndesiteInitTb  # noqa: E402

# Fixed JEDEC DDR4 command-table constants (nCK) at the TB's 1 MC clock
# = 4 nCK framing; Q1 records the formal cold-storage confirmation.
CSRS = dict(tinit1=4, tinit3=4, tinit4=2, tmrd=2, tmod=6, tdllk=192, tzqinit=256)
MR_IMAGES = [0x10 + m for m in range(7)]


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_andesite_init_slice(dut):
    tb = AndesiteInitTb(dut)
    await tb.setup()

    # Harness-observability proof: init cannot be done before it starts.
    dut.reset_n.value = 0
    for _ in range(4):
        await cocotb.triggers.RisingEdge(dut.clk)
    assert int(dut.init_done.value) == 0, "init_done high during reset"

    # Reference configuration: walk init at the design point.
    done = await tb.run_init(CSRS, MR_IMAGES)
    assert done is not None, "init_done never asserted at DDR4-1600"
    tb.check_order(CSRS)
    assert tb.violations() == {}, f"SOFT violations: {tb.violations()}"
    assert int(dut.init_err.value) == 0

    # Gear-down configuration: the entry pulse must assert exactly once and
    # the BFM's geardown behavior (G3) must see no violation.
    csrs_gd = dict(CSRS, geardown=1)
    done = await tb.run_init(csrs_gd, MR_IMAGES)
    assert done is not None, "gear-down configuration must reach READY"
    assert tb.geardown_cycles == 1, \
        f"gear-down entry must pulse exactly once, saw {tb.geardown_cycles}"
    tb.check_order(csrs_gd)
    assert tb.violations() == {}, f"SOFT violations (gear-down): {tb.violations()}"


@pytest.mark.parametrize("seed", [None])
def test_andesite_init_slice(seed):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "andesite_init_tb"
    test_name = "test_andesite_init_slice"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/"
                       "dv/filelists/andesite_init_tb.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_init_slice",
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": dut_name,
                   "RDS_DV_SRC": os.path.join(
                       os.path.dirname(repo_root), "RTLDesignSherpa-DV", "src"),
                   "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
