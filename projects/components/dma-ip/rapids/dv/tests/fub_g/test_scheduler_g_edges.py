# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_scheduler_g_edges
# Purpose: rapids-g (rapids TASK-034): scheduler_g's edge table. Every command
#          in every state; the legal edges are taken, every other command is
#          ignored and counted (CMD_ERR), CH_ERROR is left only by a reset.
#
# Author: sean galloway
# Created: 2026-10-21

import os
import sys

import cocotb
import pytest
from cocotb.triggers import FallingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.dma_ip.rapids.dv.tbclasses.scheduler_g_edges_tb import (  # noqa: E402
    SchedulerGEdgesTB, ST, W_FW_ERROR, W_PKT_LO, W_FW_DEBUG)
from TBClasses.monbus import get_packet_type, get_event_code, get_event_data, get_channel_id  # noqa: E402

PKT_DEBUG, PKT_ERROR = 0xF, 0x0                 # ocelus_common_pkg PktTypeDebug / PktTypeError
EVT_FW_DEBUG, EVT_FW_ERROR = 0x09, 0x0A         # rapids_pkg RAPIDS_EVENT_FW_DEBUG / _FW_ERROR

ALL = ('FETCH', 'XFER', 'COMPLETE', 'IDLE', 'NEXT', 'ERROR')


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_edges(dut):
    tb = SchedulerGEdgesTB(dut)
    await tb.setup_clocks_and_reset()
    ok = True

    async def illegal(names, stay):
        nonlocal ok
        for n in names:
            ok &= await tb.command(n, False, stay)

    async def legal(name, expect=None):
        nonlocal ok
        ok &= await tb.command(name, True, expect or name)

    tb.log.info("IDLE, no descriptor at the head: every command is illegal")
    await illegal(ALL, 'IDLE')
    await tb.give_descriptor()
    await legal('FETCH')
    await illegal(('FETCH', 'COMPLETE', 'IDLE', 'NEXT'), 'FETCH')
    await legal('XFER')                     # pending, taken: zero length, the records go at once
    await illegal(('FETCH', 'XFER', 'IDLE', 'NEXT'), 'XFER')
    await legal('COMPLETE')
    await illegal(('FETCH', 'XFER', 'COMPLETE'), 'COMPLETE')
    await legal('NEXT')
    await illegal(('XFER', 'COMPLETE', 'IDLE', 'NEXT', 'FETCH'), 'NEXT')   # FETCH: no descriptor yet
    await tb.give_descriptor()
    await legal('FETCH')
    await legal('ERROR')
    await illegal(ALL, 'ERROR')             # sticky: only a reset leaves CH_ERROR

    tb.log.info("channel reset: back to IDLE, CMD_ERR cleared")
    await tb.channel_reset()
    st, n = await tb.state(), await tb.errs()
    if not (st == ST['IDLE'] and n == 0):
        tb.log.error(f"  after reset: state 0x{st:02x} CMD_ERR {n}")
        ok = False
    await tb.give_descriptor()
    await legal('FETCH')
    await legal('XFER')
    await legal('COMPLETE')
    await legal('IDLE')
    # an invalid descriptor: XFER is refused in FETCH, ERROR is the way out
    await tb.give_descriptor(valid=False)
    await legal('FETCH')
    await illegal(('XFER',), 'FETCH')
    await legal('ERROR')

    tb.log.info("pre-validation: ARM / STAGE / DECLINE / GEN_OK and the automatic edges")
    await tb.channel_reset()

    async def flag(names, legal, expect):
        nonlocal ok
        ok &= await tb.flag(names, legal, expect)

    await flag('ARM', False, 'IDLE')            # only in XFER_DATA
    await flag('GEN_OK', False, 'IDLE')         # only in FETCH / XFER
    await flag('STAGE', False, 'IDLE')          # no descriptor at the head
    await tb.give_descriptor()                  # A
    await legal('FETCH')
    await legal('XFER')                         # A runs (zero length: complete at once)
    await flag('STAGE', False, 'XFER')          # still no head
    await tb.give_descriptor()                  # B at the head
    await flag('STAGE', True, 'XFER')           # B validated and staged
    await flag('STAGE', False, 'XFER')          # B already judged
    await flag('ARM', True, 'XFER')             # A completes, IDLE, B taken and started: B's XFER
    await flag('GEN_OK', True, 'XFER')
    await tb.give_descriptor(valid=False)       # C, invalid
    await flag('DECLINE', True, 'XFER')
    await flag('ARM|ARM_NEXT', True, 'NEXT')    # B completes into NEXT_DESC; C is not taken
    await flag('ARM', False, 'NEXT')
    await legal('FETCH')                        # the hand path takes C ...
    await illegal(('XFER',), 'FETCH')           # ... which is invalid
    await legal('ERROR')

    tb.log.info("STAGE_ARM: a head staged with its chain outcome is taken armed and runs on its own")
    await tb.channel_reset()

    async def head_sum(want):
        nonlocal ok
        got = await tb.head_sum()
        good = got == want
        ok &= good
        (tb.log.info if good else tb.log.error)(f"  HEAD_SUM 0x{got:x} (want 0x{want:x}) {'ok' if good else 'FAIL'}")

    await head_sum(0)                                           # no head
    await flag('STAGE_ARM', False, 'IDLE')                      # needs STAGE
    await tb.give_descriptor(last=False, next_ptr=0x40)         # D: chained
    await head_sum(0b1101)                                      # open, chain, not last, valid
    await flag('STAGE|STAGE_ARM|STAGE_ARM_NEXT', True, 'NEXT')  # D taken armed, completes into NEXT_DESC
    await tb.give_descriptor()                                  # E: last
    await head_sum(0b1011)                                      # open, last, valid
    await flag('STAGE|STAGE_ARM', True, 'IDLE')                 # E taken armed from NEXT_DESC, completes to IDLE
    await tb.give_descriptor()                                  # F
    await flag('STAGE_ARM|STAGE_ARM_NEXT', False, 'IDLE')       # still needs STAGE: F stays at the head
    await flag('STAGE', True, 'XFER')                           # staged unarmed: taken, waits in XFER for an ARM
    await flag('ARM', True, 'IDLE')

    tb.log.info("firmware packets: FW_DEBUG / FW_ERROR on the MonBus port, one waiting at a time")

    def fw_pkts():
        return [m for m in tb.mon if get_event_code(m) in (EVT_FW_DEBUG, EVT_FW_ERROR)]

    def check_pkt(m, ptype, evt, data, what):
        nonlocal ok
        good = (get_packet_type(m) == ptype and get_event_code(m) == evt and
                get_event_data(m) == data and get_channel_id(m) == 0)
        ok &= good
        (tb.log.info if good else tb.log.error)(
            f"  {what}: type 0x{get_packet_type(m):x} event 0x{get_event_code(m):02x} "
            f"data 0x{get_event_data(m):016x} {'ok' if good else 'FAIL'}")

    await tb.write(W_PKT_LO, 0xDEAD_BEEF)
    await tb.write(W_FW_DEBUG, 0x1234_5678)
    await tb.wait_clocks('clk', 4)
    got = fw_pkts()
    if len(got) != 1:
        tb.log.error(f"  FW_DEBUG: {len(got)} firmware packets (want 1) FAIL")
        ok = False
    else:
        check_pkt(got[0], PKT_DEBUG, EVT_FW_DEBUG, 0x1234_5678_DEAD_BEEF, "FW_DEBUG")

    # downstream stalled: the error packet waits, a second send is dropped and counted
    await FallingEdge(dut.clk)
    dut.mon_ready.value = 0
    await tb.write(W_PKT_LO, 0x0000_0001)
    await tb.write(W_FW_ERROR, 0x0000_00E0)
    await tb.write(W_FW_DEBUG, 0x0BAD_0BAD)                    # dropped: one is waiting
    tb.expected_errs += 1
    pend, n = await tb.fw_pending(), await tb.errs()
    good = pend == 1 and n == tb.expected_errs and len(fw_pkts()) == 1
    ok &= good
    (tb.log.info if good else tb.log.error)(
        f"  stalled: pending {pend} (want 1), CMD_ERR {n} (want {tb.expected_errs}) {'ok' if good else 'FAIL'}")
    await FallingEdge(dut.clk)
    dut.mon_ready.value = 1
    await tb.wait_clocks('clk', 4)
    got = fw_pkts()
    pend = await tb.fw_pending()
    if len(got) != 2 or pend:
        tb.log.error(f"  FW_ERROR: {len(got)} firmware packets (want 2), pending {pend} FAIL")
        ok = False
    else:
        check_pkt(got[1], PKT_ERROR, EVT_FW_ERROR, 0x0000_00E0_0000_0001, "FW_ERROR")
    assert ok, "scheduler_g edge table: see the FAIL lines"


@pytest.mark.fub
@pytest.mark.rapids_g
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_scheduler_g_edges(request, test_level):
    """Every command in every state on scheduler_g."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut = 'scheduler_g'
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path='projects/components/dma-ip/rapids/rtl/filelists/fub_g/scheduler_g.f')
    name = f"test_scheduler_g_edges_{test_level}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        name = f"{name}_{worker_id}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(log_dir, exist_ok=True)
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut, module=module, testcase="cocotb_test_edges",
        parameters={'DATA_WIDTH': 256}, simulator="verilator", sim_build=sim_build,
        extra_env={'LOG_PATH': log_path, 'DUT': dut, 'COCOTB_LOG_LEVEL': 'INFO', **level_env(test_level),
                   'COCOTB_RESULTS_FILE': os.path.join(log_dir, f"results_{name}.xml")},
        keep_files=True,
        compile_args=["-Wno-TIMESCALEMOD", "-Wno-WIDTH", "-Wno-UNOPTFLAT", "-Wno-SELRANGE",
                      "-Wno-CASEINCOMPLETE", "-Wno-PINCONNECTEMPTY"])
