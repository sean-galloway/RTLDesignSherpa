# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""
Integration test for granite's Ocelus observability plane (HAS_MON = 1):
the MON_* CSRs -> mc_ocelus_plane -> m_axil_mon writes into two memory
windows, decoded with the shared harness and parser.

Same A7 geometry as test_granite_top_geared; the bench is the family's
shared McOcelusTB (pumice dv/tbclasses/mc_ocelus_tb.py). Two cells:

  on   every source enabled, completions on, Debug routed to the error
       window next to Error / Timeout. N write+read round trips, then:
         - the trace window holds exactly N read and N write completion
           packets (PROTOCOL_AXI, the configured agents), and no Error or
           Timeout packet appears anywhere (the traffic is clean);
         - the error window holds whole 3-beat records, every one a
           PROTOCOL_CORE packet from mc_monlite, a direction flip among them
           (write then read always turns the bus);
         - mon_irq pulses == records parsed == MON_ERR_STATUS.REC_COUNT;
         - MON_RD_STATS / MON_WR_STATS completions == N, errors == 0.
  off  the plane built but every source left at its reset (off): the same
       traffic writes nothing on m_axil_mon and every count stays 0. The
       parameter's OFF state (HAS_MON = 0) is every other granite test.
"""

import os

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402

import test_granite_top_geared as base   # noqa: E402  (geometry + clocks; same directory)
from tbclasses.mc_ocelus_tb import McOcelusTB  # noqa: E402  (pumice dv on sys.path via base)

_REGMAP = ("projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/"
           "regs/generated/granite_csr_regmap.py")


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_granite_ocelus(dut):
    tb = McOcelusTB(dut, regmap_path=os.path.join(os.environ["REPO_ROOT_FOR_TEST"], _REGMAP),
                    aclk_ns=base._ACLK_NS, dfi_ns=base._DFI_NS, dw=base.DW,
                    dfi_rate=base.DFI_RATE, bl_words=base.BL_WORDS,
                    burst_words=base.BURST_WORDS)
    await tb.run(cell=os.environ.get("OCELUS_CELL", "on"),
                 rounds=int(os.environ.get("OCELUS_ROUNDS", "4")),
                 seed=int(os.environ.get("SEED", "1")))


def _cells():
    lvl = reg_level_grid()
    return [(l, c) for l in lvl for c in ("on", "off")]


@pytest.mark.parametrize("test_level,cell", _cells())
def test_granite_ocelus(request, test_level, cell):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "granite_top_geared"
    test_name = f"cocotb_test_granite_ocelus_{test_level}_{cell}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=base._FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    rounds = {"gate": 2, "func": 4, "full": 8}[test_level]
    params = {"AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32",
              "HOST_AXI_DATA_WIDTH": str(base.DW),
              "NUM_RANKS": "1", "NUM_BANKS": "8", "ROW_WIDTH": "14", "COL_WIDTH": "10",
              "DFI_RATE": str(base.DFI_RATE), "DRAM_BEAT_WIDTH": str(base.DRAM_BEAT),
              "DRAM_DEVICE_WIDTH": str(base.DRAM_DEV), "DRAM_BL": str(base.BL),
              "NUM_ENTRIES": "8", "RD_RET_DEPTH": "32", "CSR_ADDR_W": "16",
              "HAS_MON": "1", "MON_ACLK_MHZ": "100"}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                 "OCELUS_CELL": cell, "OCELUS_ROUNDS": str(rounds),
                 "REPO_ROOT_FOR_TEST": repo_root,
                 **level_env(test_level)}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_granite_ocelus",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert", "--public-flat-rw",
                      FIELD_COMBO_VLT, "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
