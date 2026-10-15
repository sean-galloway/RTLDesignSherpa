# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
FUB directed test: mc_xddr2_init_sequencer (common-ip).

Pins, per docs/superpowers/specs/2026-10-15-mc-init-plane-design.md:
  1. Exact JEDEC DDR2 init command order + MR-shadow write set.
  2. LPDDR2 MRW chain with CSR-swept OP values ({MA[5:0],OP[7:0]} packing).
  3. init_restart is rising-edge detected: a held-high level re-runs once.
  4. memtype is sampled at restart: DDR2 -> LPDDR2 flip re-runs the other chain.
  5. Held-low dfi_init_complete parks the FSM in S_DFI_INIT, no commands.
  6. dfi_init_complete dropping mid-chain does not disturb the chain.

Production change that makes each test fail: remove a port (lp_mr*_op_i /
init_state_o), revert the edge-detect, or re-order/gate the FSM arms.
Op/memtype codes mirror mc_common_pkg.sv (dram_op_e 5'h00/07/08/0A,
memtype_e 3'b000/100).
"""

import os

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, with_timeout

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_FILELIST = ("projects/components/mem-ctrl-ip/common-ip/dv/filelists/"
             "mc_xddr2_init_sequencer_fub.f")

OP_NOP  = 0x00
OP_PREA = 0x07
OP_REF  = 0x08
OP_MRS  = 0x0A

MEMTYPE_DDR2   = 0x0
MEMTYPE_LPDDR2 = 0x4

S_DFI_INIT = 1
S_WAIT     = 13
S_DONE     = 14

# Short JEDEC waits (mc_clk cycles): chain completes in a few dozen cycles.
T_INIT = 4
T_DLL  = 4
T_MRD  = 2
T_RP   = 2
T_RFC  = 2

MR0_DEFAULT = 0x433          # BL8/CL3/tWR3 (JEDEC default the RDL carries)
DDR2_N_CMDS = 11
LP2_N_CMDS  = 5
PHASE_TIMEOUT_NS = 200_000   # 200 us is ~15000 cycles at 100 MHz -- generous


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
    """Record (op,bank,row) per init_cmd_valid and (index,data) per mr_seq_we
    until init_done. Returns (cmds, shadows)."""
    cmds, shadows = [], []
    while True:
        await with_timeout(RisingEdge(dut.mc_clk), PHASE_TIMEOUT_NS, "ns")
        if int(dut.init_cmd_valid.value):
            cmds.append((int(dut.init_cmd_op.value),
                         int(dut.init_cmd_bank.value),
                         int(dut.init_cmd_row.value)))
        if int(dut.mr_seq_we.value):
            shadows.append((int(dut.mr_seq_index.value),
                            int(dut.mr_seq_data.value)))
        # DONE only counts once the chain has produced at least one command:
        # init_done_o lags the restart edge by a cycle (registered off the
        # pre-restart S_DONE state), so a collector entered right after a
        # restart would otherwise exit on the stale flag with zero commands.
        if int(dut.init_done.value) and cmds:
            return cmds, shadows


@cocotb.test()
async def cocotb_test_ddr2_chain_order_shadows(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    await _drive_defaults(dut, MEMTYPE_DDR2)
    await _reset(dut)

    cmds, shadows = await _collect_chain(dut)

    mr0 = MR0_DEFAULT
    exp_cmds = [
        (OP_PREA, 0, 0),
        (OP_MRS, 2, 0),              # EMR2
        (OP_MRS, 3, 0),              # EMR3
        (OP_MRS, 1, 0),              # EMR1
        (OP_MRS, 0, mr0 | 0x100),    # MR0 + DLL reset
        (OP_PREA, 0, 0),
        (OP_REF, 0, 0),
        (OP_REF, 0, 0),
        (OP_MRS, 0, mr0),            # MR0, DLL reset cleared
        (OP_MRS, 1, 0 | 0x380),      # EMR + OCD default (no shadow)
        (OP_MRS, 1, 0),              # EMR + OCD exit
    ]
    assert cmds == exp_cmds, f"DDR2 chain mismatch:\n got {cmds}\n exp {exp_cmds}"
    exp_shadows = [(2, 0), (3, 0), (1, 0), (0, mr0 | 0x100), (0, mr0), (1, 0)]
    assert shadows == exp_shadows, (f"shadow mismatch: got {shadows} "
                                    f"exp {exp_shadows}")
    assert int(dut.init_state.value) == S_DONE
    assert int(dut.init_busy.value) == 0


@cocotb.test()
async def cocotb_test_lpddr2_chain_op_sweep(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    await _drive_defaults(dut, MEMTYPE_LPDDR2)
    dut.lp_mr1_op.value = 0x5A
    dut.lp_mr2_op.value = 0xC3
    dut.lp_mr3_op.value = 0x3C
    await _reset(dut)

    cmds, shadows = await _collect_chain(dut)

    exp_cmds = [
        (OP_MRS, 0, _mrw_row(63, 0x00)),
        (OP_MRS, 0, _mrw_row(10, 0xFF)),
        (OP_MRS, 0, _mrw_row(1, 0x5A)),
        (OP_MRS, 0, _mrw_row(2, 0xC3)),
        (OP_MRS, 0, _mrw_row(3, 0x3C)),
    ]
    assert cmds == exp_cmds, f"LPDDR2 chain mismatch:\n got {cmds}\n exp {exp_cmds}"
    exp_shadows = [(1, 0x5A), (2, 0xC3), (3, 0x3C)]
    assert shadows == exp_shadows, (f"shadow mismatch: got {shadows} "
                                    f"exp {exp_shadows}")
    assert int(dut.init_state.value) == S_DONE


@cocotb.test()
async def cocotb_test_restart_level_held(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    await _drive_defaults(dut, MEMTYPE_DDR2)
    await _reset(dut)
    cmds0, _ = await _collect_chain(dut)
    assert len(cmds0) == DDR2_N_CMDS

    # Level (not pulse): held high must restart exactly once.
    dut.init_restart.value = 1
    await RisingEdge(dut.mc_clk)
    cmds1, _ = await _collect_chain(dut)
    assert len(cmds1) == DDR2_N_CMDS, f"restart chain len {len(cmds1)}"

    # Still held: no further re-run over 500 cycles.
    for _ in range(500):
        await RisingEdge(dut.mc_clk)
        assert int(dut.init_cmd_valid.value) == 0, "held restart re-triggered"
    dut.init_restart.value = 0


@cocotb.test()
async def cocotb_test_restart_other_memtype(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    await _drive_defaults(dut, MEMTYPE_DDR2)
    await _reset(dut)
    cmds0, _ = await _collect_chain(dut)
    assert len(cmds0) == DDR2_N_CMDS

    dut.memtype.value = MEMTYPE_LPDDR2
    dut.init_restart.value = 1
    await RisingEdge(dut.mc_clk)
    dut.init_restart.value = 0
    cmds1, shadows1 = await _collect_chain(dut)
    assert len(cmds1) == LP2_N_CMDS, f"expected LPDDR2 chain, got {cmds1}"
    assert all(c[0] == OP_MRS for c in cmds1)
    assert shadows1 == [(1, 0x23), (2, 0x01), (3, 0x02)]


@cocotb.test()
async def cocotb_test_init_complete_never(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    await _drive_defaults(dut, MEMTYPE_DDR2)
    dut.dfi_init_complete.value = 0
    await _reset(dut)

    for _ in range(200):
        await RisingEdge(dut.mc_clk)
        assert int(dut.init_cmd_valid.value) == 0, "command before PHY init"
    assert int(dut.init_state.value) == S_DFI_INIT
    assert int(dut.init_done.value) == 0
    assert int(dut.init_busy.value) == 1


@cocotb.test()
async def cocotb_test_init_complete_glitch(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    await _drive_defaults(dut, MEMTYPE_DDR2)
    await _reset(dut)

    # Let PHY init complete, then withdraw it after the first PREA. That
    # first command is consumed here (not by the collector), so the
    # collector must see the remaining DDR2_N_CMDS-1 commands.
    while True:
        await with_timeout(RisingEdge(dut.mc_clk), PHASE_TIMEOUT_NS, "ns")
        if int(dut.init_cmd_valid.value):
            assert int(dut.init_cmd_op.value) == OP_PREA
            break
    dut.dfi_init_complete.value = 0

    cmds, _ = await _collect_chain(dut)
    assert len(cmds) == DDR2_N_CMDS - 1, f"glitch truncated the chain: {cmds}"
    assert int(dut.init_state.value) == S_DONE


TESTS = [
    "cocotb_test_ddr2_chain_order_shadows",
    "cocotb_test_lpddr2_chain_op_sweep",
    "cocotb_test_restart_level_held",
    "cocotb_test_restart_other_memtype",
    "cocotb_test_init_complete_never",
    "cocotb_test_init_complete_glitch",
]


@pytest.mark.parametrize("testcase", TESTS)
def test_mc_xddr2_init_sequencer(request, testcase):
    from cocotb_test.simulator import run
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "mc_xddr2_init_sequencer_tb_top"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, testcase)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"ROW_WIDTH": "14", "NUM_BANKS": "8"}
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
