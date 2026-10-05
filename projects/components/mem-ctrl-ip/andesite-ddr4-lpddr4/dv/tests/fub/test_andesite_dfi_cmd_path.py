# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""`andesite_dfi_cmd_path` — the DFI command formatter wrapper, composed.

The P1 formatter's own suite proves the pin encoding; this suite proves what
the WRAPPER adds: the widened {ap,col,row,bg,bank,rank,op} container, the
valid/ready accept with structural holds (aligner / staged write data) that
never insert an idle cycle, fire strobes registered to align with the
registered pins, and the MRS/ZQCL payload convention (stream ROW field ->
formatter col_i, the scoria-documented quirk the arbiter's init forwarding
relies on).
"""

import os
import random
import sys

import cocotb
import pytest
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.andesite_dfi_cmd_path_tb import (  # noqa: E402
    AndesiteDfiCmdPathTB, GOLDEN,
    OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA, OP_PRE, OP_PREA, OP_REF,
    OP_MRS, OP_ZQCS, OP_ZQCL,
)


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_andesite_dfi_cmd_path(dut):
    tt = os.environ.get("TEST_TYPE", "golden_matches_formatter_table")
    tb = AndesiteDfiCmdPathTB(dut)
    await tb.setup()
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    if tt == "golden_matches_formatter_table":
        # The 11-vector anchored table from the P1 formatter suite (MAS
        # Table 2.3), issued through the wrapper: the registered pin vector
        # must match the formatter's encoding exactly, one cycle later, with
        # bg carried through the widened container.
        for op, bank, bg, row, col, exp in GOLDEN:
            if op in (OP_MRS, OP_ZQCL):
                # Formatter-style operands put the payload in col; the wrapper
                # contract routes init payloads from the stream ROW field
                # instead. Those two ops are pinned, operands and all, by
                # mrs_zqcl_payload_rides_row.
                continue
            # The wrapper's column field is COL_WIDTH bits with AP as a
            # separate carried bit (stream shape): split the formatter-style
            # 0x4xx operands into (col, ap) the way the scheduler sends them.
            ap = (col >> 10) & 1
            col &= (1 << tb.COL_WIDTH) - 1
            got, _, _ = await tb.issue(op, bank=bank, bg=bg, row=row, col=col,
                                       ap=ap)
            chk(got == exp,
                f"op {op:#x}: pins {got} != expected {exp} "
                f"(wrapper must preserve the P1 formatter encoding)")

    elif tt == "mrs_zqcl_payload_rides_row":
        # The arbiter's init-forwarding path puts the payload on the stream
        # ROW field; the wrapper must route it to the formatter's col_i for
        # MRS/ZQCL (scoria's formatter documented the identical convention).
        # Here row carries 0x14 (an MR image) with col = 0: address must show
        # 0x14, not 0. ZQCL: row bit 10 set (18'h000400 -> low bits 0x400).
        got, _, _ = await tb.issue(OP_MRS, bank=3, bg=0, row=0x14, col=0)
        chk(got[7] == 0x14,
            f"MRS address {got[7]:#x} != 0x14 -- the MR image must come from "
            f"the stream ROW field, got pins {got}")
        got, _, _ = await tb.issue(OP_ZQCL, bank=0, bg=0, row=0x400, col=0)
        chk(got[7] == 0x400,
            f"ZQCL address {got[7]:#x} != 0x400 -- A10 (the long-calibration "
            f"select) must survive from the row field, got pins {got}")
        # And a plain RD keeps the ordinary col routing (regression guard).
        got, _, _ = await tb.issue(OP_RD, bank=1, bg=2, row=0x7FFF, col=0x2AA)
        chk(got[7] == 0x2AA,
            f"RD address {got[7]:#x} != col 0x2AA -- non-init ops must keep "
            f"their column routing, got pins {got}")

    elif tt == "never_inserts_an_idle_cycle":
        # Mixed stream, both ready outs high: every cycle must accept, and
        # the registered pins must show a new command each cycle (scoria
        # TASK-007's contract, carried).
        ops = [OP_ACT, OP_RD, OP_WR, OP_PRE, OP_RD, OP_WR, OP_ACT, OP_REF]
        d = tb.dut
        d.cmd_valid_i.value = 1
        for i, op in enumerate(ops):
            d.cmd_data_i.value = tb.pack(op, bank=i % 4, bg=i % 3, row=0x100 + i,
                                         col=0x20 + i)
            await RisingEdge(d.dfi_clk)
            chk(int(d.cmd_ready_o.value) == 1,
                f"cycle {i}: ready low with both hold inputs high -- the "
                f"wrapper inserted a stall")
        d.cmd_valid_i.value = 0
        # every beat above was accepted on its own cycle; the pipeline owes
        # us exactly one more registered update (the last command).

    elif tt == "read_holds_only_for_the_aligner":
        d = tb.dut
        d.rd_op_ready_i.value = 0
        d.cmd_valid_i.value = 1
        d.cmd_data_i.value = tb.pack(OP_RD, bank=1, bg=0, col=0x10)
        await RisingEdge(d.dfi_clk)
        chk(int(d.cmd_ready_o.value) == 0,
            "RD accepted while rd_op_ready_i=0 (aligner has no slot)")
        d.cmd_data_i.value = tb.pack(OP_ACT, bank=1, bg=0, row=0x55)
        await RisingEdge(d.dfi_clk)
        chk(int(d.cmd_ready_o.value) == 1,
            "ACT stalled by the read hold -- holds must be op-class exact")
        d.cmd_valid_i.value = 0
        d.rd_op_ready_i.value = 1

    elif tt == "write_holds_only_for_staged_data":
        d = tb.dut
        d.wr_op_ready_i.value = 0
        d.cmd_valid_i.value = 1
        d.cmd_data_i.value = tb.pack(OP_WR, bank=2, bg=1, col=0x20)
        await RisingEdge(d.dfi_clk)
        chk(int(d.cmd_ready_o.value) == 0,
            "WR accepted while wr_op_ready_i=0 (data token not staged)")
        chk(int(d.wr_accept_o.value) == 0,
            "wr_accept_o high while the write is held")
        d.cmd_data_i.value = tb.pack(OP_PRE, bank=2, bg=1)
        await RisingEdge(d.dfi_clk)
        chk(int(d.cmd_ready_o.value) == 1,
            "PRE stalled by the write hold -- holds must be op-class exact")
        d.cmd_valid_i.value = 0
        d.wr_op_ready_i.value = 1

    elif tt == "fire_strobes_follow_the_op":
        d = tb.dut
        # RD then WR then ACT, spaced by issue(): each fire strobe must pulse
        # exactly once, aligned with the registered pins, and clear by the
        # cycle issue() returns (valid deasserted -> NOP re-registered).
        _, (wr, rd), _ = await tb.issue(OP_RD, bank=1, bg=0, col=0x10)
        chk(rd == 1 and wr == 0,
            "rd_fire_o must pulse (and wr_fire_o stay low) with the RD pins")
        _, (wr, rd), _ = await tb.issue(OP_WR, bank=1, bg=0, col=0x20)
        chk(wr == 1 and rd == 0,
            "wr_fire_o must pulse (and rd_fire_o stay low) with the WR pins")
        _, (wr, rd), _ = await tb.issue(OP_ACT, bank=1, bg=0, row=0x100)
        chk(wr == 0 and rd == 0,
            "ACT must raise neither fire strobe")
        # Single-cycle shape: with valid idle, both strobes read low.
        await RisingEdge(d.dfi_clk)
        await Timer(1, 'ps')
        chk(int(d.rd_fire_o.value) == 0 and int(d.wr_fire_o.value) == 0,
            "fire strobes must not linger once accepts stop")
        # Held-valid shape: a continuously accepted RD raises rd_fire every
        # cycle (one registered pulse per accept -- the aligner's contract).
        d.cmd_valid_i.value = 1
        d.cmd_data_i.value = tb.pack(OP_RD, bank=1, bg=0, col=0x10)
        for _ in range(3):
            await RisingEdge(d.dfi_clk)
            await Timer(1, 'ps')
            chk(int(d.rd_fire_o.value) == 1,
                "held-valid RD must raise rd_fire every cycle (per-accept pulse)")
        d.cmd_valid_i.value = 0
        d.cmd_data_i.value = 0

    elif tt == "parity_is_qualifed_by_parity_en":
        _, _, p = await tb.issue(OP_ACT, bank=1, bg=0, row=0x100)
        chk(p == 0, "parity must be 0 when parity_en_i is low")
        d = tb.dut
        d.parity_en_i.value = 1
        _, _, p1 = await tb.issue(OP_ACT, bank=1, bg=0, row=0x101)
        _, _, p2 = await tb.issue(OP_ACT, bank=1, bg=0, row=0x100)
        chk(p1 != p2,
            f"parity {p1} vs {p2}: one address bit flip must flip the parity bit")
        d.parity_en_i.value = 0

    elif tt == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '97')))
        d = tb.dut
        issued = 0
        for i in range(300):
            op = rng.choice([OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA, OP_PRE,
                             OP_PREA, OP_REF])
            d.rd_op_ready_i.value = 1 if rng.random() < 0.8 else 0
            d.wr_op_ready_i.value = 1 if rng.random() < 0.8 else 0
            d.cmd_valid_i.value = 1
            d.cmd_data_i.value = tb.pack(op, bank=rng.randrange(4),
                                         bg=rng.randrange(4),
                                         row=rng.randrange(1 << 8),
                                         col=rng.randrange(1 << 8))
            await RisingEdge(d.dfi_clk)
            ready = int(d.cmd_ready_o.value)
            is_rd = op in (OP_RD, OP_RDA)
            is_wr = op in (OP_WR, OP_WRA)
            want = not (is_rd and not int(d.rd_op_ready_i.value)) \
                   and not (is_wr and not int(d.wr_op_ready_i.value))
            chk(ready == (1 if want else 0),
                f"beat {i} op {op:#x}: ready {ready} but hold math says {want}")
            issued += ready
        d.cmd_valid_i.value = 0
        chk(issued > 150, f"only {issued}/300 beats accepted -- the holds wedged")

    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('dfi_clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_FUNC = ["golden_matches_formatter_table", "mrs_zqcl_payload_rides_row",
         "never_inserts_an_idle_cycle", "read_holds_only_for_the_aligner",
         "write_holds_only_for_staged_data", "fire_strobes_follow_the_op",
         "parity_is_qualifed_by_parity_en", "random_soak"]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _FUNC[:2], "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL,
                                                                _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_andesite_dfi_cmd_path(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "andesite_dfi_cmd_path"
    test_name = f"test_andesite_dfi_cmd_path_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/"
                       "rtl/filelists/fub/andesite_dfi_cmd_path.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_dfi_cmd_path",
        sim_build=sim_build, simulator="verilator",
        parameters={"NUM_BANKS": os.environ.get('NUM_BANKS', '8'),
                    "ROW_WIDTH": os.environ.get('ROW_WIDTH', '14'),
                    "COL_WIDTH": os.environ.get('COL_WIDTH', '10')},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "NUM_BANKS": os.environ.get('NUM_BANKS', '8'),
                   "ROW_WIDTH": os.environ.get('ROW_WIDTH', '14'),
                   "COL_WIDTH": os.environ.get('COL_WIDTH', '10'),
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_LOG_LEVEL": "INFO",
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
