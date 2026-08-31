# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_axi_monitor_addr_filter
# Purpose: turn the address packet filter ON and prove all three of its claims.
#
# The filter (TASK-015) suppresses monitor packets for transactions whose
# command address falls outside cfg_addr_filter_[low, high]. Three things must
# hold at once, and a test that checks only the first is worthless:
#
#   1. an in-range transaction still reports          (the filter is not a mute)
#   2. an out-of-range transaction reports NOTHING    (the filter filters)
#   3. an out-of-range transaction still RETIRES      (the filter does not leak)
#
# (3) is the one that matters. The monitor frees a table slot only when
# event_reported is set, and the sole producer of that flag is an accepted
# monbus write. Suppress a packet without also retiring the entry and the slot
# leaks: active_count climbs monotonically, block_ready goes low for ever and
# the monitored datapath wedges -- a filter meant to CUT congestion causing it.
# So this test asserts active_count returns to zero, not just that packets
# vanish.
#
# Filtering happens at REPORT time, not at admission, because address exists
# only on the command channel: refusing the allocation would leave the data and
# resp beats with no entry to match, and those land in the deliberately-ungated
# unmatched-data path as ORPHAN ERRORS. Hence check (1)'s companion below --
# a filtered transaction must produce no error packets either, which is what
# distinguishes "filtered" from "never tracked".

import os
import random

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.monbus.monbus_slave import MonbusSlave
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master
from CocoTBFramework.components.shared.field_config import FieldConfig
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

BURST_INCR = 0b01

# The filter window. IN_ADDR sits inside it, OUT_ADDR outside.
FILTER_LOW  = 0x0000_1000
FILTER_HIGH = 0x0000_1FFF
IN_ADDR     = 0x0000_1400
OUT_ADDR    = 0x0000_8000


class AddrFilterTB(TBBase):
    """Drives axi_monitor_base directly -- the filter cfg is not yet exposed
    on the axi4_*_mon wrappers, so the base is the lowest level that has it."""

    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)
        self.mon_slave = None
        self.cmd_master = None
        self.data_master = None

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', 10, 'ns')
        await self.assert_reset()
        for _ in range(10):
            await RisingEdge(self.dut.aclk)
        await self.deassert_reset()
        for _ in range(5):
            await RisingEdge(self.dut.aclk)
        await self.initialize_inputs()

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def initialize_inputs(self):
        d = self.dut
        # cmd_valid/cmd_ready are BOTH inputs here: axi_monitor_base snoops a
        # handshake rather than terminating one, so there is no slave to source
        # ready on these taps. Holding them asserted is an observed-bus tie,
        # not transaction stimulus -- the transactions come from the gaxi
        # masters built at the end of this method.
        d.cmd_ready.value = 1
        d.data_ready.value = 1

        d.monbus_ready.value = 1
        d.clear.value = 0

        d.cfg_error_enable.value = 1
        d.cfg_compl_enable.value = 1
        d.cfg_threshold_enable.value = 0
        d.cfg_timeout_enable.value = 1
        d.cfg_perf_enable.value = 0
        d.cfg_debug_enable.value = 0

        d.cfg_freq_sel.value = 0
        d.cfg_addr_cnt.value = 10
        d.cfg_data_cnt.value = 10
        d.cfg_resp_cnt.value = 10
        d.cfg_active_trans_threshold.value = 1000
        d.cfg_latency_threshold.value = 10000
        d.cfg_debug_level.value = 0
        d.cfg_debug_mask.value = 0

        # The filter under test.
        d.cfg_addr_filter_enable.value = 1
        d.cfg_addr_filter_low.value = FILTER_LOW
        d.cfg_addr_filter_high.value = FILTER_HIGH

        await RisingEdge(self.dut.aclk)

        # Hold monbus_ready asserted. GAXISlave otherwise drives ready from its
        # own randomizer, which would throttle packet acceptance and make a
        # "no packets" assertion pass for the wrong reason.
        self.mon_slave = MonbusSlave(
            dut=self.dut, title="MonBus", prefix="", clock=self.dut.aclk,
            bus_name="monbus", pkt_prefix="", log=self.log,
            randomizer=FlexRandomizer({'ready_delay': ([(0, 0)], [1])}),
        )

        # Stimulus through the BFMs. bus_name gives the valid/ready pair
        # (cmd_valid/cmd_ready) and multi_sig maps each field to its own
        # signal (cmd_addr, cmd_id, ...) -- the shape the AXI4 BFMs use
        # internally for AW/W. Every custom interface here is valid/ready, so
        # gaxi binds even though several signals form the packet.
        cmd_fields = FieldConfig.from_dict({
            'addr':  {'bits': 32, 'format': 'hex'},
            'id':    {'bits': 8,  'format': 'hex'},
            'len':   {'bits': 8,  'format': 'dec'},
            'size':  {'bits': 3,  'format': 'dec'},
            'burst': {'bits': 2,  'format': 'dec'},
        })
        data_fields = FieldConfig.from_dict({
            'id':   {'bits': 8, 'format': 'hex'},
            'last': {'bits': 1, 'format': 'dec'},
            'resp': {'bits': 2, 'format': 'dec'},
        })
        self.cmd_master = create_gaxi_master(
            dut=self.dut, title="CmdMaster", prefix="", clock=self.dut.aclk,
            field_config=cmd_fields, bus_name="cmd", pkt_prefix="",
            multi_sig=True, log=self.log)
        self.data_master = create_gaxi_master(
            dut=self.dut, title="DataMaster", prefix="", clock=self.dut.aclk,
            field_config=data_fields, bus_name="data", pkt_prefix="",
            multi_sig=True, log=self.log)

    async def send_read(self, addr, txn_id):
        """One complete single-beat read: command then its data beat, both
        driven through the gaxi masters rather than by poking signals."""
        cmd = self.cmd_master.create_packet(
            addr=addr, id=txn_id, len=0, size=2, burst=BURST_INCR)
        await self.cmd_master.send(cmd)
        dat = self.data_master.create_packet(id=txn_id, last=1, resp=0)
        await self.data_master.send(dat)

    async def settle(self, cycles=80):
        for _ in range(cycles):
            await RisingEdge(self.dut.aclk)

    def packets(self):
        return list(self.mon_slave.received_packets)


@cocotb.test(timeout_time=60, timeout_unit="sec")
async def addr_filter_test(dut):
    tb = AddrFilterTB(dut)
    await tb.setup_clocks_and_reset()

    n = 8

    # ---- 1. IN-RANGE: the filter must not be a mute --------------------------
    before = len(tb.packets())
    for i in range(n):
        await tb.send_read(IN_ADDR + i * 0x10, i)
    await tb.settle()
    in_pkts = len(tb.packets()) - before
    assert in_pkts > 0, (
        f"in-range addresses produced {in_pkts} packets -- the filter is "
        f"suppressing everything, so the rest of this test would pass "
        f"vacuously")
    tb.log.info(f"PASS in-range reported: {in_pkts} packets")

    # Table must be empty again before the out-of-range leg, so the leak check
    # below measures only what that leg did.
    active_mid = int(dut.active_count.value)
    assert active_mid == 0, (
        f"active_count={active_mid} after the in-range leg; the table did not "
        f"drain and the leak check would be attributed to the wrong leg")

    # ---- 2 + 3. OUT-OF-RANGE: no packets, and no leak -----------------------
    before = len(tb.packets())
    for i in range(n):
        await tb.send_read(OUT_ADDR + i * 0x10, i)
    await tb.settle()
    out_pkts = len(tb.packets()) - before

    assert out_pkts == 0, (
        f"out-of-range addresses produced {out_pkts} packets, expected 0 "
        f"(filtered transactions must emit nothing -- including the orphan "
        f"errors that an admission-time filter would have caused)")

    active_end = int(dut.active_count.value)
    assert active_end == 0, (
        f"active_count={active_end} after {n} filtered transactions, expected "
        f"0. The filtered entries were suppressed but never retired, so they "
        f"leaked their table slots -- this is the failure that wedges "
        f"block_ready and the monitored datapath")

    tb.log.info(f"PASS filtered: 0 packets, active_count back to 0")
    tb.log.info("RESULTS: 3/3 checks passed")


@pytest.mark.parametrize("addr_width, id_width", [(32, 8)])
def test_axi_monitor_addr_filter(request, addr_width, id_width):
    """Address packet filter ON: reports in-range, drops out-of-range, no leak."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba',
    })

    dut_name = "axi_monitor_base"
    test_name = f"test_{worker_id}_axi_monitor_addr_filter_aw{addr_width}_iw{id_width}"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi_monitor_base.f")

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=os.path.splitext(os.path.basename(__file__))[0],
        parameters={
            'ID_WIDTH': str(id_width),
            'ADDR_WIDTH': str(addr_width),
            'UNIT_ID': '1',
            'AGENT_ID': '10',
            'MAX_TRANSACTIONS': '16',
            'IS_READ': '1',
            'IS_AXI': '1',
            'ENABLE_PERF_PACKETS': '0',
            'ENABLE_DEBUG_MODULE': '0',
            # The knob under test. Default is 0; this is the only place in
            # val/ that turns it on.
            'ADDR_FILTER_ENABLE': '1',
        },
        sim_build=sim_build,
        extra_env={
            'DUT': dut_name,
            'LOG_PATH': log_path,
            'COCOTB_LOG_LEVEL': 'INFO',
            'SEED': os.environ.get('SEED', '12345'),
        },
        keep_files=True,
        compile_args=[
            "-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED", "-Wno-DECLFILENAME",
            "-Wno-PINMISSING", "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND",
            "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE",
            "-Wno-TIMESCALEMOD",
        ],
    )
