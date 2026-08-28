# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_axi4_to_apb4_rresp
# Purpose: PSLVERR from a non-final APB slice must reach RRESP (TASK-064).
#
# Documentation: docs/markdown/rtl-amba/index.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-08-17

"""RRESP must carry an error from ANY slice of a width-converted read.

A width-converted read assembles one AXI beat from several APB slices. RRESP
was driven from w_pslverr alone -- the IN-FLIGHT slice -- so a 2:1 read whose
FIRST slice errored returned RRESP=OKAY with partially bad data. Silent
corruption: the master sees success and keeps the half-bad beat.

The burst-wide r_pslverr could not simply be substituted; once set it would
over-mark every LATER beat of the same burst as an error. The fix accumulates
per AXI BEAT and restarts each beat.

WHY THIS IS A UNIT TEST, not an addition to the shim suite: injecting PSLVERR
on a SPECIFIC slice needs control of the APB response, and create_apb4_slave
has no error-injection hook -- the BFM owns m_apb_pslverr. axi4_to_apb4_convert
exposes its APB response as ports (r_rsp_valid / w_rsp_ready / r_rsp_data), so
driving them directly gives per-slice control with no framework change.

The converter's AXI interface is PACKED, so this builds/decodes the packets
the way the RTL does:
  r_rsp_data    = {last, first, pslverr, prdata}
  r_s_axi_ar_pkt= {arid, araddr, arlen, arsize, arburst, arlock, arcache,
                   arprot, arqos, arregion, aruser}
  r_s_axi_r_pkt = {rid, rdata, rresp, rlast, ruser}   (ruser is the LSB)
"""

import os

import cocotb
import pytest
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

APB_DW = 32
RESP_OKAY, RESP_SLVERR = 0b00, 0b10


def rsp_word(prdata: int, pslverr: int, first: int, last: int) -> int:
    """Pack {last, first, pslverr, prdata} exactly as the DUT unpacks it."""
    return ((last & 1) << (APB_DW + 2) | (first & 1) << (APB_DW + 1) |
            (pslverr & 1) << APB_DW | (prdata & ((1 << APB_DW) - 1)))


async def _clk(dut):
    dut.aclk.value = 0
    while True:
        await Timer(5, units="ns")
        dut.aclk.value = 1
        await Timer(5, units="ns")
        dut.aclk.value = 0


async def _reset(dut):
    dut.aresetn.value = 0
    # The APB COMMAND side must be drained or the converter stalls before it
    # ever produces a response: w_cmd_valid is an OUTPUT and r_cmd_ready an
    # INPUT, so the TB has to accept commands. Not driving it was why this
    # timed out in _slice() waiting on w_rsp_ready.
    dut.r_cmd_ready.value = 1
    for s in ("r_rsp_valid", "r_s_axi_arvalid", "r_s_axi_awvalid",
              "r_s_axi_wvalid", "r_s_axi_rready", "r_s_axi_bready"):
        sig = getattr(dut, s, None)
        if sig is not None:
            sig.value = 0
    dut.r_s_axi_rready.value = 1
    cocotb.start_soon(_clk(dut))
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    for _ in range(5):
        await RisingEdge(dut.aclk)


async def _slice(dut, prdata, pslverr, first, last):
    """Hand the converter one APB response slice."""
    dut.r_rsp_data.value = rsp_word(prdata, pslverr, first, last)
    dut.r_rsp_valid.value = 1
    # Bounded, so a stalled DUT names itself instead of hanging the run.
    for _ in range(200):
        await RisingEdge(dut.aclk)
        if int(dut.w_rsp_ready.value):
            break
    else:
        raise AssertionError(
            "w_rsp_ready never asserted: the converter is not accepting APB "
            "responses. Check that the command side is being drained "
            "(r_cmd_ready) and that the AR was accepted.")
    dut.r_rsp_valid.value = 0
    await RisingEdge(dut.aclk)


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_rresp_first_slice_error(dut):
    """An error on the FIRST slice must still mark the assembled beat."""
    await _reset(dut)

    # One AXI read beat = two APB slices (DW=64, APBDW=32).
    #
    # ARSize = IW + AW + 8+3+2+1+4+3+4+4 + UW, packed MSB..LSB as
    #   {arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot,
    #    arqos, arregion, aruser}
    # so the LSB offsets are derived from the field widths, NOT guessed --
    # the first version of this hand-counted them wrong and the read never
    # started, which looked like an RTL failure.
    IW, AW, UW = 8, 32, 1
    O_USER   = 0
    O_REGION = O_USER + UW
    O_QOS    = O_REGION + 4
    O_PROT   = O_QOS + 4
    O_CACHE  = O_PROT + 3
    O_LOCK   = O_CACHE + 4
    O_BURST  = O_LOCK + 1
    O_SIZE   = O_BURST + 2
    O_LEN    = O_SIZE + 3
    O_ADDR   = O_LEN + 8
    O_ID     = O_ADDR + AW
    ar = ((3 << O_ID) | (0x1000 << O_ADDR) | (0 << O_LEN) |
          (3 << O_SIZE) | (1 << O_BURST))      # size=8B, burst=INCR
    dut.r_s_axi_ar_pkt.value = ar
    dut.r_s_axi_arvalid.value = 1
    for _ in range(20):
        await RisingEdge(dut.aclk)
        if int(dut.w_s_axi_arready.value):
            break
    dut.r_s_axi_arvalid.value = 0

    seen = []

    async def watch_r():
        while True:
            await RisingEdge(dut.aclk)
            if int(dut.w_s_axi_rvalid.value) and int(dut.r_s_axi_rready.value):
                # r_s_axi_r_pkt = {rid, rdata, rresp, rlast, ruser}
                # ruser[0], rlast[1], rresp[3:2]
                seen.append((int(dut.r_s_axi_r_pkt.value) >> 2) & 0x3)

    w = cocotb.start_soon(watch_r())
    await _slice(dut, 0xAAAA0000, pslverr=1, first=1, last=0)   # FIRST slice errors
    await _slice(dut, 0xBBBB1111, pslverr=0, first=0, last=1)   # second is clean
    for _ in range(30):
        await RisingEdge(dut.aclk)
    w.kill()

    dut._log.info(f"RRESP seen: {[bin(s) for s in seen]}")
    assert seen, "no R beat returned after both slices were answered"
    assert seen[-1] == RESP_SLVERR, (
        f"RRESP={seen[-1]:#04b} but the FIRST APB slice of this beat returned "
        f"PSLVERR. RRESP is being driven from the in-flight slice alone, so an "
        f"error in any earlier slice is dropped and the master keeps a "
        f"partially bad beat believing it succeeded.")


@pytest.mark.parametrize("testcase", ["cocotb_test_rresp_first_slice_error"])
def test_axi4_to_apb4_rresp(testcase):
    """Per-slice RRESP error propagation (TASK-064 item 1)."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':  'rtl/common',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "axi4_to_apb4_convert"
    test_name = f"test_{worker_id}_{dut_name}_rresp"
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/converters/rtl/filelists/axi4_to_apb4_shim.f")

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes + [rtl_dict['rtl_cmn'], sim_build],
        toplevel=dut_name,
        module="test_axi4_to_apb4_rresp",
        testcase=testcase,
        parameters={'AXI_DATA_WIDTH': '64', 'APB_DATA_WIDTH': '32',
                    'AXI_ADDR_WIDTH': '32', 'APB_ADDR_WIDTH': '32',
                    'AXI_ID_WIDTH': '8'},
        sim_build=sim_build,
        extra_env={'DUT': dut_name, 'COCOTB_LOG_LEVEL': 'INFO'},
        keep_files=True,
        compile_args=["-Wall", "-Wno-DECLFILENAME", "-Wno-UNUSED",
                      "-Wno-PINMISSING", "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND",
                      "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-TIMESCALEMOD",
                      "-Wno-SYNCASYNCNET", "-Wno-CASEINCOMPLETE",
                      "-Wno-PINCONNECTEMPTY"],
    )
