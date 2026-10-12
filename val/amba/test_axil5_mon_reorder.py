# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_axil5_mon_reorder
# Purpose: AXI5-Lite monitors behind a Subordinate that reorders across IDs (amba #104).
#
# IHI 0022 Issue L B2.1.5: on AXI5-Lite "reordering of responses is permitted
# when requests have different IDs". Every axil5 monitor wrapper -- _mon,
# _mon_cg, _monlite, _monlite_cg, master and slave, read and write -- used to
# tie the monitor's command/data/response ID to 0. The monitor then paired
# each response with the OLDEST command outstanding, whichever one the
# response answered: the completion for the transaction answered first named
# the transaction issued first, every completion carried channel 0, and the
# latency/timeout bookkeeping ran against the wrong entry.
#
# Phase 1, reorder: N transactions on N distinct IDs, issued in an order that
# is NOT ID order, all outstanding at once; the Subordinate holds each
# response so they come back in REVERSE issue order. Checked:
#   - the bus really reordered (else the phase proves nothing and fails);
#   - exactly N completion packets and nothing else -- no orphan, no error;
#   - each completion names its own transaction: channel == the request ID,
#     address == the address issued on that ID;
#   - completions come out in the bus's response order;
#   - the table is empty once the bus is idle.
#
# Phase 2, W leads AW (write wrappers): W carries no ID on AXI5-Lite, write
# data follows AW order (A5.5) and may arrive BEFORE its AW (A2.6). The
# Subordinate's AWREADY is held so each W crosses the monitor's tap first;
# every completion must still name its own (address, ID), with no error and
# an empty table after. On a slave wrapper the tap is the Manager-facing port,
# where the Manager BFM always sends AW first, so the lead cannot be produced
# there; the phase logs that and checks only the attribution.

import os
import random

import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.axil5.axil5_reorder import install as install_reorder
from TBClasses.monbus.monbus_types import PktType, AXIErrorCode

PKT_COMPL = int(PktType.PktTypeCompletion)
PKT_ERROR = int(PktType.PktTypeError)
ERR_WRITE_BEFORE_ADDR = int(AXIErrorCode.AXI_ERR_WRITE_BEFORE_ADDR)
HOLD_STEP = 30          # cycles of extra response latency per position
DEPTH = {'gate': (4, 1), 'func': (6, 2), 'full': (6, 4)}   # (transactions per round, rounds)


class _BusLog:
    """Handshakes on the port the monitor taps, in cycle order."""

    def __init__(self, dut, tap, is_write):
        self.dut = dut
        c = 'aw' if is_write else 'ar'
        r = 'b' if is_write else 'r'
        self.cmd = [getattr(dut, f"{tap}{c}{s}") for s in ('valid', 'ready', 'id')]
        self.rsp = [getattr(dut, f"{tap}{r}{s}") for s in ('valid', 'ready', 'id')]
        self.w = ([getattr(dut, f"{tap}w{s}") for s in ('valid', 'ready')]
                  if is_write else None)
        self.reset()

    def reset(self):
        self.cmd_ids, self.rsp_ids = [], []
        self.n_aw = self.n_w = 0
        self.w_leads = 0            # W handshakes that came before their AW
        self.max_lead = 0           # most W bursts ever ahead of the AWs

    async def run(self):
        while True:
            await RisingEdge(self.dut.aclk)
            try:
                if int(self.cmd[0].value) and int(self.cmd[1].value):
                    self.cmd_ids.append(int(self.cmd[2].value))
                    self.n_aw += 1
                if int(self.rsp[0].value) and int(self.rsp[1].value):
                    self.rsp_ids.append(int(self.rsp[2].value))
                if self.w is not None and int(self.w[0].value) and int(self.w[1].value):
                    self.n_w += 1
                    if self.n_w > self.n_aw:
                        self.w_leads += 1
                    self.max_lead = max(self.max_lead, self.n_w - self.n_aw)
            except ValueError:
                continue


def _monitor_tb(dut_name):
    from TBClasses.axil5.monitor.axil5_master_monitor_tb import AXIL5MasterMonitorTB
    from TBClasses.axil5.monitor.axil5_slave_monitor_tb import AXIL5SlaveMonitorTB
    return AXIL5SlaveMonitorTB if "_slave_" in dut_name else AXIL5MasterMonitorTB


async def _issue(tb, is_write, addr, tid, errors):
    m = tb.master_components['interface']
    try:
        if is_write:
            await m.write_transaction(addr, 0x5A000000 | (addr & 0xFFFF), awid=tid)
        else:
            await m.read_transaction(addr, arid=tid)
    except (TypeError, AttributeError, NameError):
        raise
    except Exception as e:          # a stalled transaction is a finding, recorded below
        errors.append(f"id {tid} @0x{addr:08X}: {e}")


async def _round(tb, bus, sub, is_write, ids, base, hold, sequential, where):
    """Issue one round, wait for it, return the list of failures."""
    fails, errors = [], []
    addr_of = {tid: base + 0x40 * k for k, tid in enumerate(ids)}
    n = len(ids)
    sub.hold({tid: (n - 1 - k) * HOLD_STEP for k, tid in enumerate(ids)} if hold else {})
    tb.mon_slave.clear_received_packets()
    bus.reset()
    if sequential:
        for tid in ids:
            await _issue(tb, is_write, addr_of[tid], tid, errors)
    else:
        tasks = [cocotb.start_soon(_issue(tb, is_write, addr_of[t], t, errors)) for t in ids]
        for _ in range(4000):
            if all(t.done() for t in tasks):
                break
            await RisingEdge(tb.dut.aclk)
    for _ in range(300):
        await RisingEdge(tb.dut.aclk)

    fails += [f"{where}: transaction failed on the bus: {e}" for e in errors]
    if bus.cmd_ids != list(ids) or sorted(bus.rsp_ids) != sorted(ids):
        fails.append(f"{where}: bus saw commands {bus.cmd_ids} / responses {bus.rsp_ids} "
                     f"for issued ids {list(ids)}")
    if hold and bus.rsp_ids == bus.cmd_ids:
        fails.append(f"{where}: the Subordinate did not reorder (responses {bus.rsp_ids}) "
                     "-- this round proves nothing")
    pkts = list(tb.mon_slave.received_packets)
    compl = [p for p in pkts if int(p.pkt_type) == PKT_COMPL]
    other = [p for p in pkts if int(p.pkt_type) != PKT_COMPL]
    # The lite keeps ONE write burst that arrives ahead of its AW; a second
    # one is reported as WRITE_BEFORE_ADDR (its documented limit) and, since
    # amba #105, still counted so attribution stays aligned. Legal only when
    # the bus really ran W two or more bursts ahead.
    if "_monlite" in os.environ["DUT"] and bus.max_lead >= 2:
        early = [p for p in other if int(p.pkt_type) == PKT_ERROR and
                 int(p.event_code) == ERR_WRITE_BEFORE_ADDR]
        if early:
            tb.log.info(f"{where}: {len(early)} WRITE_BEFORE_ADDR report(s) -- W ran "
                        f"{bus.max_lead} bursts ahead of AW at the tap")
        other = [p for p in other if p not in early]
    if other:
        fails.append(f"{where}: unexpected packets (type, code, channel) "
                     f"{[(int(p.pkt_type), int(p.event_code), int(p.channel_id)) for p in other[:6]]}")
    if len(compl) != n:
        fails.append(f"{where}: {len(compl)} completion packets for {n} transactions")
    named = []
    for p in compl:
        ch, addr = int(p.channel_id), int(p.data) & 0xFFFF_FFFF
        named.append(ch)
        if ch not in addr_of:
            fails.append(f"{where}: completion on channel {ch} (address 0x{addr:08X}) -- "
                         f"no transaction used that ID (issued {list(ids)})")
        elif addr != addr_of[ch]:
            fails.append(f"{where}: completion for ID {ch} names 0x{addr:08X}, but ID {ch} "
                         f"was issued to 0x{addr_of[ch]:08X} -- response paired with the wrong command")
    if not fails and named != bus.rsp_ids:
        fails.append(f"{where}: completions in ID order {named}, but the bus answered {bus.rsp_ids}")
    live = int(tb.dut.active_transactions.value)
    if live != 0:
        fails.append(f"{where}: bus idle but the monitor table still holds {live} entries")
    tb.log.info(f"{where}: issued {list(ids)}, answered {bus.rsp_ids}, completions {named}, "
                f"W-before-AW {bus.w_leads} (max lead {bus.max_lead}), table {live}, {len(fails)} failure(s)")
    return fails


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_reorder(dut):
    dut_name = os.environ["DUT"]
    level = os.environ.get("TEST_LEVEL", "func").lower()
    n, rounds = DEPTH.get(level, DEPTH['func'])
    is_write = "_wr_" in dut_name
    is_slave = "_slave_" in dut_name
    rng = random.Random(int(os.environ.get("SEED", "1")))

    tb = _monitor_tb(dut_name)(dut, is_write=is_write, aclk=dut.aclk, aresetn=dut.aresetn)
    await tb.initialize()
    tb.mon_slave.set_ready_randomizer(FlexRandomizer({'ready_delay': ([(0, 0)], [1])}))
    sub = install_reorder(tb.slave_components['interface'], dut.aclk, tb.log)
    bus = _BusLog(dut, 's_axil_' if is_slave else 'm_axil_', is_write)
    cocotb.start_soon(bus.run())

    fails = []
    for r in range(rounds):
        ids = rng.sample(range(1, 16), n)
        while ids == sorted(ids):
            rng.shuffle(ids)                    # AW order must not be ID order
        fails += await _round(tb, bus, sub, is_write, ids, 0x1000 + 0x400 * r,
                              hold=True, sequential=False, where=f"reorder[{r}]")

    if is_write:
        aw = tb.slave_components['AW']
        saved = getattr(aw, 'randomizer', None)
        aw.randomizer = FlexRandomizer({'ready_delay': ([(20, 20)], [1])})
        ids = rng.sample(range(1, 16), n)
        fails += await _round(tb, bus, sub, is_write, ids, 0x3000,
                              hold=False, sequential=True, where="w_leads")
        if bus.w_leads == 0:
            if is_slave:
                tb.log.info("w_leads: no W crossed the s_axil tap before its AW (the "
                            "Manager BFM sends AW first); attribution checked only")
            else:
                fails.append("w_leads: no W crossed the tap before its AW -- the phase "
                             "proves nothing")
        if saved is not None:
            aw.randomizer = saved

    for f in fails:
        tb.log.error(f)
    assert not fails, f"{len(fails)} failure(s):\n  " + "\n  ".join(fails[:20])


WRAPPERS = [f"axil5_{role}_{d}_{kind}"
            for kind in ("mon", "mon_cg", "monlite", "monlite_cg")
            for role in ("master", "slave") for d in ("rd", "wr")]


def _cases():
    reg = os.environ.get("REG_LEVEL", "FUNC").upper()
    if reg == "GATE":
        return [("axil5_master_wr_mon", "gate"), ("axil5_slave_rd_mon_cg", "gate"),
                ("axil5_master_rd_monlite", "gate"), ("axil5_slave_wr_monlite_cg", "gate")]
    lvl = "full" if reg == "FULL" else "func"
    return [(w, lvl) for w in WRAPPERS]


@pytest.mark.parametrize("dut_name,test_level", _cases())
def test_axil5_mon_reorder(dut_name, test_level):
    """Responses reordered across IDs must reach their own transactions."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({"rtl_amba": "rtl/amba"})
    worker_id = os.environ.get("PYTEST_XDIST_WORKER", "gw0")
    test_name = f"test_{worker_id}_{dut_name}_reorder_{test_level}"
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=f"rtl/amba/filelists/{dut_name}.f")

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=os.path.splitext(os.path.basename(__file__))[0],
        testcase="cocotb_test_reorder",
        parameters={"AXIL_ADDR_WIDTH": "32", "AXIL_DATA_WIDTH": "32",
                    "MAX_TRANSACTIONS": "16"},
        sim_build=sim_build,
        extra_env={
            "DUT": dut_name,
            "TEST_LEVEL": test_level,
            "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
            "COCOTB_LOG_LEVEL": "INFO",
            "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
            "SEED": os.environ.get("SEED", str(random.randint(0, 1_000_000))),
        },
        keep_files=True,
        compile_args=["--public-flat-rw", "-Wno-fatal", "--timescale", "1ns/1ps"],
    )
