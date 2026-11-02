# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""
Integration test for pumice's Ocelus observability plane (HAS_MON = 1) at
pumice_top_geared (through pumice_top_geared_tb_top): the MON_* CSRs ->
mc_ocelus_plane -> m_axil_mon writes into two memory windows.

Setup and traffic are pumice's own bench (PumiceTopCsrTB: DFISlavePHY golden
DRAM, program_defaults, the AXI4 master BFMs), exactly as
test_pumice_top_geared runs them, at GEAR-1 (host 128 = DW) so one host
burst is one burst at the core's port. The Ocelus part is the family's
shared McOcelusTB (dv/tbclasses/mc_ocelus_tb.py) -- the same checks
granite's test_granite_ocelus runs:

  on   every source enabled (programmed after init, before traffic): the
       trace window holds one read and one write completion per burst, no
       Error or Timeout packet appears, the error window holds mc_monlite
       Debug records with a direction flip among them, irq == records ==
       MON_ERR_STATUS.REC_COUNT, and the MON_* stats agree.
  off  the plane built, every source at reset: nothing written, counts 0.

The parameter's OFF state (HAS_MON = 0) is every other pumice test. pumice's
pick core here is BANK_PICK (pumice_top_geared's default), the core whose
direction register the flip event taps.
"""

import os
import sys

import pytest
import cocotb
from cocotb.triggers import ClockCycles
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.mc_ocelus_tb import McOcelusTB                       # noqa: E402
from tbclasses.pumice_top_csr_tb import PumiceTopCsrTB              # noqa: E402
from tbclasses.pumice_sequences import build_b2b_wr_rd_sequences    # noqa: E402

_FILELIST = ("projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/"
             "dv/filelists/pumice_top_geared_tb_top.f")
_REGMAP = ("projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/"
           "regs/generated/pumice_csr_regmap.py")

DFI_RATE, DRAM_BEAT, BL = 2, 64, 8
DW = DRAM_BEAT * DFI_RATE                       # 128: GEAR-1 host width
NUM_BANKS, ROW_WIDTH, COL_WIDTH = 8, 14, 10
BASE = 0x10000


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_ocelus(dut):
    cell = os.environ.get("OCELUS_CELL", "on")
    n_bursts = int(os.environ.get("OCELUS_ROUNDS", "4"))

    tb = PumiceTopCsrTB(dut, dram_beat_width=DRAM_BEAT, dfi_rate=DFI_RATE, dram_bl=BL,
                        num_ranks=1, num_banks=NUM_BANKS, row_width=ROW_WIDTH,
                        col_width=COL_WIDTH, mem_type="DDR2", host_axi_data_width=DW)
    # the Ocelus writer's slave side idles until the harness takes it
    for s in ("m_axil_mon_awready", "m_axil_mon_wready", "m_axil_mon_bvalid",
              "m_axil_mon_bresp"):
        getattr(dut, s).value = 0
    await tb.reset()
    tb.init_dfi_slave()
    await tb.program_defaults(mem_type="DDR2")
    await tb.wait_for_init_done()

    oc = McOcelusTB(dut, regmap_path=os.path.join(os.environ["REPO_ROOT_FOR_TEST"], _REGMAP))
    oc.start_harness()
    if cell == "on":
        await oc.program_monitors()

    tb.init_axi_masters()
    tb.set_axi_timing_profile("backtoback")
    host_beats = (BL * DRAM_BEAT) // DW
    wr, rd, _ = build_b2b_wr_rd_sequences(
        n_bursts=n_bursts, burst_len=host_beats, base_addr=BASE, data_width=DW)
    await tb.run_writes(wr, drain_cycles=75 * n_bursts)
    rd_dicts = await tb.run_sequence(rd)
    assert len(rd_dicts) == n_bursts and all(d.get("data") is not None for d in rd_dicts), \
        f"reads: {len(rd_dicts)} of {n_bursts}"
    await ClockCycles(dut.aclk, 10)
    await oc.finish(cell=cell, rounds=n_bursts)


def _cells():
    return [(l, c) for l in reg_level_grid() for c in ("on", "off")]


@pytest.mark.parametrize("test_level,cell", _cells())
def test_pumice_ocelus(request, test_level, cell):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_top_geared_tb_top"
    test_name = f"cocotb_test_pumice_ocelus_{test_level}_{cell}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    rounds = {"gate": 2, "func": 4, "full": 8}[test_level]
    params = {"HOST_AXI_DATA_WIDTH": str(DW), "AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32",
              "NUM_RANKS": "1", "NUM_BANKS": str(NUM_BANKS), "ROW_WIDTH": str(ROW_WIDTH),
              "COL_WIDTH": str(COL_WIDTH), "DFI_RATE": str(DFI_RATE),
              "DRAM_BEAT_WIDTH": str(DRAM_BEAT), "DRAM_BL": str(BL),
              "NUM_ENTRIES": "8", "N_SRAM_SLOTS": "8", "HAS_MON": "1"}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                 "OCELUS_CELL": cell, "OCELUS_ROUNDS": str(rounds),
                 "REPO_ROOT_FOR_TEST": repo_root, "HOST_AXI_DATA_WIDTH": str(DW),
                 **level_env(test_level)}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_pumice_ocelus",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--public-flat-rw", FIELD_COMBO_VLT,
                      "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
