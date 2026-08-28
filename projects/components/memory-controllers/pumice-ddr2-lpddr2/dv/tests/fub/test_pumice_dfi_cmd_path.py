# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Pattern-B runner for `pumice_dfi_cmd_path` (DFI command path)."""

import os
import sys
import random
import subprocess

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)
from tbclasses.pumice_fub_bfm import fub_producer      # noqa: E402

_repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).decode().strip()

# dram_op_e
OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA, OP_PRE = 0, 1, 2, 3, 4, 5, 6

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/fub/pumice_dfi_cmd_path.f")

RKW, BKW, RW, CW = 1, 3, 14, 10


def pack(op, rank, bank, row, col, ap):
    # {ap, col, row, bank, rank, op}
    v = op & 0xF
    v |= (rank & ((1 << RKW) - 1)) << 4
    v |= (bank & ((1 << BKW) - 1)) << (4 + RKW)
    v |= (row & ((1 << RW) - 1)) << (4 + RKW + BKW)
    v |= (col & ((1 << CW) - 1)) << (4 + RKW + BKW + RW)
    v |= (ap & 1) << (4 + RKW + BKW + RW + CW)
    return v


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_pumice_dfi_cmd_path(dut):
    cocotb.start_soon(Clock(dut.dfi_clk, 10, units='ns').start())
    dut.dfi_rstn.value = 0
    dut.memtype_i.value = 0
    dut.rd_phase_i.value = 0
    dut.wr_phase_i.value = 0
    # Read-aligner backpressure: keep a free slot so RD commands are not gated.
    dut.rd_op_ready_i.value = 1
    # Sub-DFI-word framing (task #146): single-command per group (n_subcmd=1) for
    # this smoke — the packing case is covered by cocotb_test_pumice_dfi_cmd_path_pack.
    dut.n_subcmd_i.value = 1
    dut.sub_col_stride_i.value = 0
    dut.sub_phase_stride_i.value = 0
    # cmd_* is BFM-owned. rd_op_ready_i above is NOT a handshake -- it has no
    # matching valid, it is a credit ("rd aligner has a free slot"), same
    # class as the arbiter's bank permission vectors -- so it stays set here.
    cmd_bfm = fub_producer(dut, "cmd", dut.dfi_clk, log=dut._log,
                           valid="cmd_valid_i", ready="cmd_ready_o",
                           fields={'data': ("cmd_data_i",
                                            max(1, len(dut.cmd_data_i)))})
    for _ in range(4):
        await RisingEdge(dut.dfi_clk)
    dut.dfi_rstn.value = 1
    for _ in range(3):
        await RisingEdge(dut.dfi_clk)

    # capture fire strobes
    wr_fires, rd_fires = [], []

    async def mon():
        while True:
            await RisingEdge(dut.dfi_clk)
            if int(dut.wr_fire_o.value):
                wr_fires.append(1)
            if int(dut.rd_fire_o.value):
                rd_fires.append(1)
    cocotb.start_soon(mon())

    seq = [(OP_ACT, 3, 0x123, 0), (OP_WR, 3, 0, 0x40), (OP_RD, 3, 0, 0x80),
           (OP_WRA, 2, 0, 0x10), (OP_RDA, 2, 0, 0x20), (OP_PRE, 3, 0, 0)]
    exp_wr = sum(1 for s in seq if s[0] in (OP_WR, OP_WRA))
    exp_rd = sum(1 for s in seq if s[0] in (OP_RD, OP_RDA))

    for op, bank, row, col in seq:
        ap = 1 if op in (OP_RDA, OP_WRA) else 0
        await cmd_bfm.send(cmd_bfm.create_packet(
            data=pack(op, 0, bank, row, col, ap)))
    for _ in range(6):
        await RisingEdge(dut.dfi_clk)

    assert len(wr_fires) == exp_wr, f"wr_fire count {len(wr_fires)} != {exp_wr}"
    assert len(rd_fires) == exp_rd, f"rd_fire count {len(rd_fires)} != {exp_rd}"
    # command bus is driven (non-idle) at some point — formatter proven elsewhere
    dut._log.info(f"PASS: {exp_wr} wr_fire, {exp_rd} rd_fire; commands formatted to DFI bus")


def _decode_rd_phases(dut, dfi_rate, ctrl_w=1, cs_w=1):
    """Return the set of DFI phases carrying a RD command this cycle (cs_n=0,
    ras_n=1, cas_n=0, we_n=1) — the packed multi-phase issue check."""
    cs = int(dut.dfi_cs_n_o.value)
    ras = int(dut.dfi_ras_n_o.value)
    cas = int(dut.dfi_cas_n_o.value)
    we = int(dut.dfi_we_n_o.value)
    phases = set()
    for p in range(dfi_rate):
        sel = ((cs >> (p * cs_w)) & 1) == 0
        rd = (((ras >> (p * ctrl_w)) & 1) == 1
              and ((cas >> (p * ctrl_w)) & 1) == 0
              and ((we >> (p * ctrl_w)) & 1) == 1)
        if sel and rd:
            phases.add(p)
    return phases


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_pumice_dfi_cmd_path_pack(dut):
    """Sub-DFI-word PACKING (task #146): with N_SUBCMD=2 / SUB_PHASE_STRIDE=2 /
    SUB_COL_STRIDE=4, ONE scheduled RD must be issued as TWO RD sub-commands in
    ONE DFI cycle at phases {0, 2} (the a7ddrphy anchors each sub's BL beats to
    its phase -> both anchored runs pack into ONE DFI word). Exactly ONE rd_fire
    is emitted for the whole packed group."""
    cocotb.start_soon(Clock(dut.dfi_clk, 10, units='ns').start())
    dut.dfi_rstn.value = 0
    dut.memtype_i.value = 0
    dut.rd_phase_i.value = 0
    dut.wr_phase_i.value = 0
    dut.rd_op_ready_i.value = 1
    dut.n_subcmd_i.value = 2
    dut.sub_col_stride_i.value = 4
    dut.sub_phase_stride_i.value = 2
    # cmd_* is BFM-owned. rd_op_ready_i above is NOT a handshake -- it has no
    # matching valid, it is a credit ("rd aligner has a free slot"), same
    # class as the arbiter's bank permission vectors -- so it stays set here.
    cmd_bfm = fub_producer(dut, "cmd", dut.dfi_clk, log=dut._log,
                           valid="cmd_valid_i", ready="cmd_ready_o",
                           fields={'data': ("cmd_data_i",
                                            max(1, len(dut.cmd_data_i)))})
    for _ in range(4):
        await RisingEdge(dut.dfi_clk)
    dut.dfi_rstn.value = 1
    for _ in range(3):
        await RisingEdge(dut.dfi_clk)

    rd_fires = []
    packed_cycles = []

    async def mon():
        while True:
            await RisingEdge(dut.dfi_clk)
            if int(dut.rd_fire_o.value):
                rd_fires.append(1)
            ph = _decode_rd_phases(dut, dfi_rate=4)
            if ph:
                packed_cycles.append(ph)
    cocotb.start_soon(mon())

    # One scheduled RD (bank 3, col 0x80).
    await cmd_bfm.send(cmd_bfm.create_packet(
        data=pack(OP_RD, 0, 3, 0, 0x80, 0)))
    for _ in range(8):
        await RisingEdge(dut.dfi_clk)

    assert len(rd_fires) == 1, f"expected exactly 1 rd_fire for the packed group, got {len(rd_fires)}"
    # Exactly one DFI cycle carried RD commands, and it carried BOTH phases {0,2}.
    assert len(packed_cycles) == 1, f"RD commands spread over {len(packed_cycles)} cycles, expected 1 packed cycle: {packed_cycles}"
    assert packed_cycles[0] == {0, 2}, f"packed RD phases {packed_cycles[0]} != {{0,2}}"
    dut._log.info("PASS: 2 RD sub-commands packed into one DFI cycle at phases {0,2}, 1 rd_fire")


def _run_cmd_path(testcase, params, extra_params=None):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_dfi_cmd_path"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, testcase)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    if extra_params:
        params = {**params, **extra_params}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{testcase}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{testcase}.xml"),
                 "SEED": os.environ.get('SEED', str(random.randint(0, 100000)))}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase=testcase,
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET"], waves=False, keep_files=True, timescale="1ns/1ps")


def test_pumice_dfi_cmd_path(request):
    params = {"NUM_RANKS": "1", "NUM_BANKS": "8", "ROW_WIDTH": "14", "COL_WIDTH": "10",
              "DFI_RATE": "4", "DFI_ADDR_WIDTH": "14", "DFI_BANK_WIDTH": "3"}
    _run_cmd_path("cocotb_test_pumice_dfi_cmd_path", params)


def test_pumice_dfi_cmd_path_pack(request):
    """Build for the sub-DFI-word regime (N_SUBCMD=2) and prove same-cycle packing."""
    params = {"NUM_RANKS": "1", "NUM_BANKS": "8", "ROW_WIDTH": "14", "COL_WIDTH": "10",
              "DFI_RATE": "4", "DFI_ADDR_WIDTH": "14", "DFI_BANK_WIDTH": "3",
              "N_SUBCMD": "2", "SUB_PHASE_STRIDE": "2", "SUB_COL_STRIDE": "4"}
    _run_cmd_path("cocotb_test_pumice_dfi_cmd_path_pack", params)
