# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Macro test: mc_init_plane (common-ip).

Pins the plane boundary per
docs/superpowers/specs/2026-10-15-mc-init-plane-design.md:
  1. DDR2 JEDEC chain at the plane's init_cmd port + MR-shadow set, and the
     live CL/BL decode from the plane's mode-register shadow (MR0=0x433 ->
     CL3, BL8; CWL=CL-1=2).
  2. LPDDR2 MRW chain with default OP ports (0x23/0x01/0x02); MR1 BL8 decode.
  3. init_state_o telemetry: 0->1 early, 13 (S_WAIT) between commands, 14
     at DONE.

Production change that makes each test fail: drop the mode-register child
from the plane (decode outputs dangle), rename an init_cmd port (Task 3's
core wiring breaks), or gate the state telemetry.
Op codes mirror mc_common_pkg.sv dram_op_e (5'h07/08/0A).
"""

import os

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, with_timeout

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_FILELIST = ("projects/components/mem-ctrl-ip/common-ip/dv/filelists/"
             "mc_init_plane_macro.f")

OP_PREA = 0x07
OP_REF  = 0x08
OP_MRS  = 0x0A

MEMTYPE_DDR2   = 0x0
MEMTYPE_LPDDR2 = 0x4

S_RESET    = 0
S_DFI_INIT = 1
S_WAIT     = 13
S_DONE     = 14

T_INIT, T_DLL, T_MRD, T_RP, T_RFC = 4, 4, 2, 2, 2
MR0_DEFAULT = 0x433
PHASE_TIMEOUT_NS = 200_000


def _mrw_row(ma, op):
    return (ma << 8) | op


async def _drive_defaults(dut, memtype=MEMTYPE_DDR2):
    dut.memtype.value = memtype
    dut.t_init_wait.value = T_INIT
    dut.t_dll_wait.value = T_DLL
    dut.t_mrd_wait.value = T_MRD
    dut.t_rp_wait.value = T_RP
    dut.t_rfc_wait.value = T_RFC
    dut.mr0.value = MR0_DEFAULT
    dut.mr1.value = 0
    dut.mr2.value = 0
    dut.mr3.value = 0
    dut.lp_mr1_op.value = 0x23
    dut.lp_mr2_op.value = 0x01
    dut.lp_mr3_op.value = 0x02
    dut.init_restart.value = 0
    dut.dfi_init_complete.value = 1


async def _reset(dut):
    dut.mc_rst_n.value = 0
    for _ in range(5):
        await RisingEdge(dut.mc_clk)
    dut.mc_rst_n.value = 1
    await RisingEdge(dut.mc_clk)


async def _collect_chain(dut):
    """Record (op,bank,row) per init_cmd_valid until DONE (which must follow
    at least one command). The MR-shadow write port is INTERNAL to the plane
    (sequencer -> mode register), so shadows are verified indirectly here
    through the cl/cwl/bl decode outputs; the direct shadow check lives in
    the fub test."""
    cmds = []
    while True:
        await with_timeout(RisingEdge(dut.mc_clk), PHASE_TIMEOUT_NS, "ns")
        if int(dut.init_cmd_valid.value):
            cmds.append((int(dut.init_cmd_op.value),
                         int(dut.init_cmd_bank.value),
                         int(dut.init_cmd_row.value)))
        if int(dut.init_done.value) and cmds:
            return cmds


@cocotb.test()
async def cocotb_test_ddr2_chain_at_plane_boundary(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    await _drive_defaults(dut, MEMTYPE_DDR2)
    await _reset(dut)

    cmds = await _collect_chain(dut)

    mr0 = MR0_DEFAULT
    exp_cmds = [
        (OP_PREA, 0, 0),
        (OP_MRS, 2, 0),
        (OP_MRS, 3, 0),
        (OP_MRS, 1, 0),
        (OP_MRS, 0, mr0 | 0x100),
        (OP_PREA, 0, 0),
        (OP_REF, 0, 0),
        (OP_REF, 0, 0),
        (OP_MRS, 0, mr0),
        (OP_MRS, 1, 0x380),
        (OP_MRS, 1, 0),
    ]
    assert cmds == exp_cmds, f"DDR2 chain mismatch:\n got {cmds}\n exp {exp_cmds}"

    # Mode-register shadow decode (MR0=0x433 -> CL3/BL8; CWL = CL-1).
    for _ in range(4):
        await RisingEdge(dut.mc_clk)
    assert int(dut.cl_o.value) == 3, f"cl_o={int(dut.cl_o.value)}"
    assert int(dut.bl_o.value) == 8, f"bl_o={int(dut.bl_o.value)}"
    assert int(dut.cwl_o.value) == 2, f"cwl_o={int(dut.cwl_o.value)}"
    assert int(dut.init_state.value) == S_DONE


@cocotb.test()
async def cocotb_test_lpddr2_chain_at_plane_boundary(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    await _drive_defaults(dut, MEMTYPE_LPDDR2)
    await _reset(dut)

    cmds = await _collect_chain(dut)

    exp_cmds = [
        (OP_MRS, 0, _mrw_row(63, 0x00)),
        (OP_MRS, 0, _mrw_row(10, 0xFF)),
        (OP_MRS, 0, _mrw_row(1, 0x23)),
        (OP_MRS, 0, _mrw_row(2, 0x01)),
        (OP_MRS, 0, _mrw_row(3, 0x02)),
    ]
    assert cmds == exp_cmds, f"LPDDR2 chain mismatch:\n got {cmds}\n exp {exp_cmds}"

    for _ in range(4):
        await RisingEdge(dut.mc_clk)
    # MR1=0x23 -> BL8; MR2=0x01 -> RL3/WL1.
    assert int(dut.bl_o.value) == 8, f"bl_o={int(dut.bl_o.value)}"
    assert int(dut.cl_o.value) == 3, f"cl_o={int(dut.cl_o.value)}"
    assert int(dut.cwl_o.value) == 1, f"cwl_o={int(dut.cwl_o.value)}"


@cocotb.test()
async def cocotb_test_state_telemetry(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    await _drive_defaults(dut, MEMTYPE_DDR2)
    await _reset(dut)

    # Out of reset: S_RESET(0) then S_DFI_INIT(1).
    assert int(dut.init_state.value) in (S_RESET, S_DFI_INIT)
    saw_dfi_init = False
    saw_wait = False
    while True:
        await with_timeout(RisingEdge(dut.mc_clk), PHASE_TIMEOUT_NS, "ns")
        st = int(dut.init_state.value)
        if st == S_DFI_INIT:
            saw_dfi_init = True
        if saw_dfi_init and st == S_WAIT:
            saw_wait = True
        if int(dut.init_done.value):
            break
    assert saw_dfi_init, "never observed S_DFI_INIT"
    assert saw_wait, "never observed S_WAIT between commands"
    assert st == S_DONE, f"final state {st}"


TESTS = [
    "cocotb_test_ddr2_chain_at_plane_boundary",
    "cocotb_test_lpddr2_chain_at_plane_boundary",
    "cocotb_test_state_telemetry",
]


@pytest.mark.parametrize("testcase", TESTS)
def test_mc_init_plane(request, testcase):
    from cocotb_test.simulator import run
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "mc_init_plane_tb_top"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, testcase)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"NUM_RANKS": "1", "NUM_BANKS": "8", "ROW_WIDTH": "14"}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{testcase}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{testcase}.xml")}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase=testcase,
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert", "--public-flat-rw",
                      "-Wno-MULTIDRIVEN", "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
