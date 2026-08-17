# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_axi_wr_splitter_defects
# Purpose: FUB-level checks for the axi_master_wr_splitter defect cluster.
#
# Documentation: docs/markdown/rtl-amba/shared/axi_master_wr_splitter.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-08-17

"""Directed FUB checks for TASK-063, items 1, 3 and 4.

Each check drives the ONE situation the existing splitter suite never creates,
which is why all three defects survived to be found by reading the RTL:

  1. BRESP CONSOLIDATION -- error on the LAST split.
     r_consolidated_resp_status folds each split's response one cycle AFTER
     that split's B handshake, but the final split is forwarded upstream in
     that SAME cycle. So the fold carried splits 1..N-1 and the last split's
     status was dropped: resp1=OKAY, resp2=SLVERR upstreamed as OKAY. An error
     on the last split read as SUCCESS -- silent corruption, not a visible
     failure. Nothing in the suite drove a non-OKAY response at all.

  4. CONSOLIDATION FENCING -- two split writes back to back.
     There is ONE set of consolidation registers. The IDLE accept had no
     !r_waiting_for_responses term, so a second transaction accepted while the
     first still had responses in flight OVERWROTE them: T1's responses then
     forwarded raw upstream, or folded into T2 and T1 was never answered.
     Nothing in the suite overlapped two transactions' response windows.

  3. SPLIT-FIFO OVERFLOW -- more splits in flight than the FIFO holds.
     wr_ready was unconnected and the push ungated, so a full FIFO dropped the
     record silently and the consumer read someone else's or none. Sizing is a
     correctness requirement; this makes the violation observable.

These are written to FAIL on the pre-fix RTL. Mutation-check them when
touching the splitter: remove the fix and the matching check must go red.
"""

import os

import cocotb
import pytest
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

RESP_OKAY, RESP_SLVERR = 0b00, 0b10


async def _clk(dut):
    dut.aclk.value = 0
    while True:
        await Timer(5, units="ns")
        dut.aclk.value = 1
        await Timer(5, units="ns")
        dut.aclk.value = 0


async def _reset(dut):
    dut.aresetn.value = 0
    dut.block_ready.value = 0
    dut.alignment_mask.value = 0xFFF          # 4 KB boundary
    for s in ("fub_awvalid", "fub_wvalid", "fub_bready",
              "m_axi_awready", "m_axi_wready", "m_axi_bvalid"):
        getattr(dut, s).value = 0
    dut.m_axi_bresp.value = RESP_OKAY
    cocotb.start_soon(_clk(dut))
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    for _ in range(5):
        await RisingEdge(dut.aclk)


async def _send_aw(dut, addr, length, awid=1):
    """Present one AW that CROSSES the 4 KB boundary, so it must split."""
    dut.fub_awid.value = awid
    dut.fub_awaddr.value = addr
    dut.fub_awlen.value = length
    dut.fub_awsize.value = 2
    dut.fub_awburst.value = 1
    dut.fub_awvalid.value = 1
    dut.m_axi_awready.value = 1
    # let the FSM issue every split
    for _ in range(40):
        await RisingEdge(dut.aclk)
        if int(dut.fub_awready.value) and int(dut.fub_awvalid.value):
            break
    dut.fub_awvalid.value = 0


async def _b_beat(dut, resp):
    """One downstream B response with the given status."""
    dut.m_axi_bresp.value = resp
    dut.m_axi_bvalid.value = 1
    while True:
        await RisingEdge(dut.aclk)
        if int(dut.m_axi_bready.value):
            break
    dut.m_axi_bvalid.value = 0
    await RisingEdge(dut.aclk)


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_bresp_final_split_error(dut):
    """An error on the FINAL split must reach the upstream BRESP."""
    await _reset(dut)
    dut.fub_bready.value = 1

    # MUST actually cross the 4 KB boundary at this awsize, or nothing splits
    # and consolidation never engages -- the first version of this used the
    # doc's 0x0FC0/LEN=7, which crosses only at 64-byte beats. At awsize=2
    # (4 B) that is 0x0FC0..0x0FDF, entirely below 0x1000, and the test then
    # 'failed' against correct RTL.
    # 0x0FF0 + 8 beats x 4 B = 0x1010 -> two splits.
    await _send_aw(dut, 0x0FF0, 7)

    seen = []

    async def watch_b():
        while True:
            await RisingEdge(dut.aclk)
            if int(dut.fub_bvalid.value) and int(dut.fub_bready.value):
                seen.append(int(dut.fub_bresp.value))

    w = cocotb.start_soon(watch_b())
    await _b_beat(dut, RESP_OKAY)      # split 1 -> OKAY
    await _b_beat(dut, RESP_SLVERR)    # split 2 (FINAL) -> SLVERR
    for _ in range(20):
        await RisingEdge(dut.aclk)
    w.kill()

    dut._log.info(f"upstream BRESP(s) seen: {[hex(s) for s in seen]}")
    assert seen, "no upstream B response at all after both splits answered"
    assert len(seen) == 1, (
        f"expected ONE consolidated upstream response, got {len(seen)} -- the "
        f"splitter is forwarding split responses raw")
    assert seen[0] == RESP_SLVERR, (
        f"upstream BRESP={seen[0]:#04b} but the FINAL split returned SLVERR. "
        f"The consolidation fold runs a cycle after each B handshake, so the "
        f"last split's status is dropped and an error reads as SUCCESS.")


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_consolidation_is_fenced(dut):
    """A second transaction must not be accepted while responses are in flight."""
    await _reset(dut)
    dut.fub_bready.value = 1

    await _send_aw(dut, 0x0FF0, 7, awid=1)     # T1: splits, responses outstanding

    # T2 presented immediately, while T1 still owes responses.
    dut.fub_awid.value = 2
    dut.fub_awaddr.value = 0x2FF0
    dut.fub_awlen.value = 7
    dut.fub_awsize.value = 2
    dut.fub_awburst.value = 1
    dut.fub_awvalid.value = 1
    dut.m_axi_awready.value = 1

    accepted_early = 0
    for _ in range(30):
        await RisingEdge(dut.aclk)
        if int(dut.fub_awvalid.value) and int(dut.fub_awready.value):
            accepted_early += 1
    dut.fub_awvalid.value = 0

    dut._log.info(f"T2 accepts while T1's responses outstanding: {accepted_early}")
    assert accepted_early == 0, (
        f"T2 was accepted {accepted_early} time(s) while T1 still had split "
        f"responses in flight. There is ONE consolidation state set, so this "
        f"overwrites T1's -- its responses then forward raw upstream, or fold "
        f"into T2 and T1 is never answered.")


@cocotb.test(timeout_time=4, timeout_unit="ms")
async def cocotb_test_split_fifo_overflow_is_visible(dut):
    """FORCE the split-info FIFO to overflow and require the sticky flag.

    An earlier version of this only checked the port existed and read a
    defined value -- which passes whether or not the FIFO ever filled, i.e. it
    asserted nothing. This never drains fub_split (fub_split_ready=0) and
    pushes far more split transactions than SPLIT_FIFO_DEPTH holds, so records
    MUST be dropped, and the flag must say so.
    """
    await _reset(dut)
    dut.fub_bready.value = 1
    dut.fub_split_ready.value = 0          # never drain: the FIFO must fill

    ovf = getattr(dut, "o_split_fifo_overflow", None)
    assert ovf is not None, (
        "no o_split_fifo_overflow port -- a full split-info FIFO drops the "
        "record with nothing to show for it")
    assert int(ovf.value) == 0, "overflow asserted before any traffic"

    # SPLIT_FIFO_DEPTH is 4 in this build; 12 split writes is 3x that.
    for i in range(12):
        await _send_aw(dut, 0x0FF0 + (i << 13), 7, awid=(i % 8))
        await _b_beat(dut, RESP_OKAY)      # split 1
        await _b_beat(dut, RESP_OKAY)      # split 2 -> transaction retires
    for _ in range(20):
        await RisingEdge(dut.aclk)

    dut._log.info(f"o_split_fifo_overflow after 12 undrained split writes = "
                  f"{int(ovf.value)}")
    assert int(ovf.value) == 1, (
        "12 split transactions were pushed into a 4-deep split-info FIFO that "
        "was never drained, so records were certainly dropped -- but the "
        "sticky overflow flag never asserted. The loss is invisible again, "
        "which is the whole defect.")


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_w_held_until_aw_issued(dut):
    """W must not reach the slave before its AW has been issued.

    W is pure pass-through while r_data_splitting arms only on the first split
    AW handshake, so a W beat arriving first took the non-split branch, carried
    the ORIGINAL wlast downstream and was never counted toward a split
    boundary -- WLAST regeneration silently defeated.

    W-before-AW is illegal traffic in this repo, so this does not ask the
    splitter to HANDLE it; it checks the guard that enforces the rule. The data
    is not dropped either -- fub_wready is held low, so the beat stays with the
    master until its AW goes out.
    """
    await _reset(dut)
    dut.fub_bready.value = 1

    # W presented with no AW at all.
    dut.fub_wdata.value = 0xDEADBEEF
    dut.fub_wstrb.value = 0xF
    dut.fub_wlast.value = 1
    dut.fub_wvalid.value = 1
    dut.m_axi_wready.value = 1

    leaked = 0
    accepted = 0
    for _ in range(40):
        await RisingEdge(dut.aclk)
        if int(dut.m_axi_wvalid.value) and int(dut.m_axi_wready.value):
            leaked += 1
        if int(dut.fub_wvalid.value) and int(dut.fub_wready.value):
            accepted += 1

    dut._log.info(f"with no AW issued: downstream W beats={leaked} "
                  f"upstream W accepts={accepted}")
    assert leaked == 0, (
        f"{leaked} W beat(s) reached the slave with no AW issued -- they carry "
        f"the original WLAST and are never counted toward a split boundary")
    assert accepted == 0, (
        f"{accepted} W beat(s) accepted upstream with no AW issued; the "
        f"handshake must be gated on BOTH ends or the beat is consumed and lost")

    # Now issue the AW: the held beat must flow.
    dut.fub_wvalid.value = 0
    await _send_aw(dut, 0x0FF0, 7)
    dut.fub_wvalid.value = 1
    flowed = 0
    for _ in range(40):
        await RisingEdge(dut.aclk)
        if int(dut.m_axi_wvalid.value) and int(dut.m_axi_wready.value):
            flowed += 1
    dut.fub_wvalid.value = 0
    dut._log.info(f"after AW issued: downstream W beats={flowed}")
    assert flowed > 0, (
        "W never flowed even after its AW was issued -- the gate does not "
        "release, which is a deadlock rather than ordering")


@pytest.mark.parametrize("testcase", [
    "cocotb_test_bresp_final_split_error",
    "cocotb_test_consolidation_is_fenced",
    "cocotb_test_split_fifo_overflow_is_visible",
    "cocotb_test_w_held_until_aw_issued",
])
def test_axi_wr_splitter_defects(testcase):
    """FUB-level defect checks for axi_master_wr_splitter (TASK-063)."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':         'rtl/common',
        'rtl_gaxi':        'rtl/amba/gaxi',
        'rtl_amba_shared': 'rtl/amba/shared',
        'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "axi_master_wr_splitter"
    test_name = f"test_{worker_id}_{dut_name}_defect_{testcase}"
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f"rtl/amba/filelists/{dut_name}.f")

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes + [rtl_dict['rtl_cmn'], sim_build],
        toplevel=dut_name,
        module="test_axi_wr_splitter_defects",
        testcase=testcase,
        parameters={'AXI_ID_WIDTH': '8', 'AXI_ADDR_WIDTH': '32',
                    'AXI_DATA_WIDTH': '32', 'AXI_USER_WIDTH': '1',
                    'SPLIT_FIFO_DEPTH': '4'},
        sim_build=sim_build,
        extra_env={'DUT': dut_name, 'COCOTB_LOG_LEVEL': 'INFO'},
        keep_files=True,
        compile_args=["-Wall", "-Wno-DECLFILENAME", "-Wno-UNUSED",
                      "-Wno-PINMISSING", "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND",
                      "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-TIMESCALEMOD",
                      "-Wno-SYNCASYNCNET", "-Wno-CASEINCOMPLETE"],
    )
