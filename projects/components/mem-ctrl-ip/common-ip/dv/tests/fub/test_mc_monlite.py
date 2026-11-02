# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""
FUB test: mc_monlite (common-ip) -- the controller's internal-event observer.

The taps are levels and pulses the controller already has, so the bench
drives them directly; the monitor bus is consumed by the shared MonbusSlave.
Every check is on decoded packets (type, protocol, event code, ids, payload):

  1. errors:   each error event, once per rising edge for the levels, the
               refresh-backlog payload; ids and PROTOCOL_CORE on every packet.
  2. debug:    init state / done payloads, the direction-flip payload layout,
               REF / ZQ ops, page-timeout PRE, store-full sides, ring full.
  3. gating:   cfg_enable = 0 emits nothing (the OFF state); cfg_ev_en masks
               one event; turning on while a level is already high reports
               nothing for it (the edge detectors keep running).
  4. priority: events in the same cycle come out lowest code first, so an
               error always leaves before a debug event.
  5. drops:    with the bus stalled the queue fills, repeats of a held event
               are lost and counted, and one DROPPED packet carries the count
               once the bus drains; the controller-side taps are never stalled.

Production change that makes each test fail: an edge detector turned into a
level, a payload field moved, the priority walk reversed, the drop counter
not counting coalesced repeats, or cfg_enable not gating.
"""

import os

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402
from TBClasses.monbus.monbus_slave import MonbusSlave
from TBClasses.monbus.monbus_types import PktType, ProtocolType
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

_FILELIST = "projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_monlite.f"

UNIT_ID, AGENT_ID = 0x20, 0x0012

# mc_event_e
EV = dict(CAL_ERR=0x00, ZQ_OVERDUE=0x01, REF_BACKLOG=0x02, AW_RAGGED=0x03,
          RD_BEAT_LOST=0x04, RET_ORPHAN=0x05, DROPPED=0x06,
          INIT_DONE=0x08, INIT_STATE=0x09, DIR_FLIP=0x0A, REFRESH=0x0B,
          ZQ=0x0C, PAGE_TO_PRE=0x0D, STORE_FULL=0x0E, RING_FULL=0x0F)
# dram_op_e
OP_REF, OP_REFPB, OP_ZQCS, OP_ZQCL, OP_RD = 0x08, 0x09, 0x0B, 0x0C, 0x02

_TAPS = ("cal_err_i", "zq_overdue_i", "ref_pending_i", "aw_ragged_i",
         "rd_beat_lost_i", "ret_orphan_i", "init_done_i", "init_state_i",
         "dir_flip_i", "dir_i", "dir_cause_i", "dir_batch_i", "cmd_accept_i",
         "cmd_accept_op_i", "accept_to_pre_i", "store_wr_full_i",
         "store_rd_full_i", "ring_full_i")


class MonliteTB:
    """Minimal bench: clocks, reset, taps idle, MonbusSlave on the output."""

    def __init__(self, dut):
        self.dut = dut
        self.log = dut._log
        self.mbus = None

    async def setup_clocks_and_reset(self):
        cocotb.start_soon(Clock(self.dut.aclk, 10, units="ns").start())
        for t in _TAPS:
            getattr(self.dut, t).value = 0
        self.dut.cfg_enable.value = 0
        self.dut.cfg_ev_en.value = 0xFFFF
        self.dut.i_mon_time.value = 0
        await self.assert_reset()
        await ClockCycles(self.dut.aclk, 5)
        await self.deassert_reset()
        self.mbus = MonbusSlave(dut=self.dut, title="MonBus", prefix="",
                                clock=self.dut.aclk, bus_name="monbus",
                                pkt_prefix="", log=self.log)
        self.fast()
        cocotb.start_soon(self._time())
        await ClockCycles(self.dut.aclk, 5)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def _time(self):
        t = 0
        while True:
            await RisingEdge(self.dut.aclk)
            t += 1
            self.dut.i_mon_time.value = t

    def fast(self):
        self.mbus.set_ready_randomizer(FlexRandomizer({'ready_delay': ([(0, 0)], [1])}))

    def stall(self, cycles):
        self.mbus.set_ready_randomizer(
            FlexRandomizer({'ready_delay': ([(cycles, cycles)], [1])}))

    async def pulse(self, sig, val=1):
        getattr(self.dut, sig).value = val
        await RisingEdge(self.dut.aclk)
        getattr(self.dut, sig).value = 0

    async def take(self, settle=40):
        await ClockCycles(self.dut.aclk, settle)
        got = list(self.mbus.received_packets)
        self.mbus.clear_received_packets()
        for p in got:
            assert p.protocol == ProtocolType.PROTOCOL_CORE, f"protocol {p.protocol}"
            assert p.unit_id == UNIT_ID and p.agent_id == AGENT_ID, \
                f"ids {p.unit_id:#x}/{p.agent_id:#x}"
            exp_t = PktType.PktTypeError if p.event_code < 0x08 else PktType.PktTypeDebug
            assert p.pkt_type == exp_t, f"code {p.event_code:#x}: type {p.pkt_type}"
        return [(p.event_code, p.data) for p in got]


async def _start(dut, enable=1):
    tb = MonliteTB(dut)
    await tb.setup_clocks_and_reset()
    dut.cfg_enable.value = enable
    await RisingEdge(dut.aclk)
    return tb


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_errors(dut):
    tb = await _start(dut)
    # levels report once per rising edge, however long they stay up
    dut.cal_err_i.value = 1
    dut.zq_overdue_i.value = 1
    got = await tb.take(60)
    assert got == [(EV["CAL_ERR"], 0), (EV["ZQ_OVERDUE"], 0)], got
    dut.cal_err_i.value = 0
    dut.zq_overdue_i.value = 0
    assert await tb.take(10) == []
    dut.cal_err_i.value = 1
    assert await tb.take() == [(EV["CAL_ERR"], 0)]
    dut.cal_err_i.value = 0

    # refresh backlog: trips at the max, payload = the backlog
    for n in range(0, 8):
        dut.ref_pending_i.value = n
        await RisingEdge(dut.aclk)
    assert await tb.take(5) == []
    dut.ref_pending_i.value = 8
    assert await tb.take() == [(EV["REF_BACKLOG"], 8)]
    dut.ref_pending_i.value = 0

    # pulses: one packet per pulse
    for sig, code in (("aw_ragged_i", "AW_RAGGED"), ("rd_beat_lost_i", "RD_BEAT_LOST"),
                      ("ret_orphan_i", "RET_ORPHAN")):
        await tb.pulse(sig)
        assert await tb.take() == [(EV[code], 0)], code
    assert int(dut.error_count.value) == 7, int(dut.error_count.value)
    tb.log.info("PASS errors")


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_debug(dut):
    tb = await _start(dut)
    dut.init_state_i.value = 0x3
    assert await tb.take() == [(EV["INIT_STATE"], 0x3)]
    dut.init_state_i.value = 0x7
    dut.init_done_i.value = 1
    # same cycle: INIT_DONE (0x08) before INIT_STATE (0x09)
    assert await tb.take() == [(EV["INIT_DONE"], 0x7), (EV["INIT_STATE"], 0x7)]

    dut.dir_i.value = 1
    dut.dir_cause_i.value = 2
    dut.dir_batch_i.value = 0x5A
    await tb.pulse("dir_flip_i")
    assert await tb.take() == [(EV["DIR_FLIP"], (2 << 9) | (1 << 8) | 0x5A)]

    for op, code in ((OP_REF, "REFRESH"), (OP_REFPB, "REFRESH"),
                     (OP_ZQCS, "ZQ"), (OP_ZQCL, "ZQ")):
        dut.cmd_accept_op_i.value = op
        await tb.pulse("cmd_accept_i")
        assert await tb.take() == [(EV[code], op)], (op, code)
    dut.cmd_accept_op_i.value = OP_RD          # a column op is not an event
    await tb.pulse("cmd_accept_i")
    assert await tb.take() == []
    await tb.pulse("accept_to_pre_i")
    assert await tb.take() == [(EV["PAGE_TO_PRE"], 0)]

    dut.store_rd_full_i.value = 1
    assert await tb.take() == [(EV["STORE_FULL"], 0b10)]
    dut.store_wr_full_i.value = 1               # still full: no new edge
    assert await tb.take() == []
    dut.store_rd_full_i.value = 0
    dut.store_wr_full_i.value = 0
    await ClockCycles(dut.aclk, 2)
    dut.store_wr_full_i.value = 1
    assert await tb.take() == [(EV["STORE_FULL"], 0b01)]
    dut.store_wr_full_i.value = 0
    dut.ring_full_i.value = 1
    assert await tb.take() == [(EV["RING_FULL"], 0)]
    dut.ring_full_i.value = 0
    assert int(dut.error_count.value) == 0
    tb.log.info("PASS debug")


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_gating(dut):
    tb = await _start(dut, enable=0)
    # OFF state: every tap fires, nothing comes out
    dut.cal_err_i.value = 1
    dut.ring_full_i.value = 1
    for sig in ("aw_ragged_i", "rd_beat_lost_i", "dir_flip_i", "accept_to_pre_i"):
        await tb.pulse(sig)
    assert await tb.take() == [], "packets with cfg_enable = 0"
    # turning on with the levels already up reports nothing for them
    dut.cfg_enable.value = 1
    assert await tb.take() == []
    dut.cal_err_i.value = 0
    dut.ring_full_i.value = 0
    # one event masked, its neighbour not
    dut.cfg_ev_en.value = 0xFFFF & ~(1 << EV["AW_RAGGED"])
    await tb.pulse("aw_ragged_i")
    await tb.pulse("ret_orphan_i")
    assert await tb.take() == [(EV["RET_ORPHAN"], 0)]
    tb.log.info("PASS gating")


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_priority(dut):
    tb = await _start(dut)
    # all in one cycle; out lowest code first
    dut.ret_orphan_i.value = 1
    dut.dir_flip_i.value = 1
    dut.aw_ragged_i.value = 1
    dut.accept_to_pre_i.value = 1
    await RisingEdge(dut.aclk)
    for s in ("ret_orphan_i", "dir_flip_i", "aw_ragged_i", "accept_to_pre_i"):
        getattr(dut, s).value = 0
    got = [c for c, _ in await tb.take()]
    assert got == [EV["AW_RAGGED"], EV["RET_ORPHAN"], EV["DIR_FLIP"], EV["PAGE_TO_PRE"]], got
    tb.log.info("PASS priority")


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_drops(dut):
    tb = await _start(dut)
    tb.stall(400)                     # first packet waits 400 cycles
    await tb.pulse("ret_orphan_i")    # -> the queue (stalled at the bus)
    await ClockCycles(dut.aclk, 2)
    # four more distinct events fill the 4-deep queue's remaining room
    for s in ("aw_ragged_i", "rd_beat_lost_i", "dir_flip_i", "accept_to_pre_i"):
        await tb.pulse(s)
    await ClockCycles(dut.aclk, 4)
    # the queue is full now; a held ring_full edge pends, its repeats are lost
    lost = 0
    for _ in range(5):
        dut.ring_full_i.value = 1
        await RisingEdge(dut.aclk)
        dut.ring_full_i.value = 0
        await RisingEdge(dut.aclk)
        lost += 1
    lost -= 1                          # the first one pends, the rest drop
    await RisingEdge(dut.aclk)
    assert int(dut.dropped_count.value) == lost, (int(dut.dropped_count.value), lost)
    tb.fast()
    got = await tb.take(800)
    codes = [c for c, _ in got]
    assert codes[-1] == EV["DROPPED"] and got[-1][1] == lost, got
    assert codes.count(EV["RING_FULL"]) == 1, got
    for c in ("RET_ORPHAN", "AW_RAGGED", "RD_BEAT_LOST", "DIR_FLIP", "PAGE_TO_PRE"):
        assert EV[c] in codes, (c, got)
    assert int(dut.dropped_count.value) == 0
    tb.log.info("PASS drops: %d lost, reported once", lost)


TESTS = ["cocotb_test_errors", "cocotb_test_debug", "cocotb_test_gating",
         "cocotb_test_priority", "cocotb_test_drops"]


@pytest.mark.parametrize("testcase", TESTS)
def test_mc_monlite(request, testcase):
    from cocotb_test.simulator import run
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "mc_monlite"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, testcase)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{testcase}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{testcase}.xml")}
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase=testcase,
        sim_build=sim_build, simulator="verilator", extra_env=extra_env,
        parameters={"OUT_DEPTH": "4"},
        compile_args=["+define+USE_ASYNC_RESET", "--assert", "--public-flat-rw",
                      FIELD_COMBO_VLT, "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
