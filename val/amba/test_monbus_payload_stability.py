# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_monbus_payload_stability
# Purpose: monbus_packet must not change while monbus_valid && !monbus_ready.
#
# axi_monitor_base drives monbus from a COMBINATIONAL priority mux
# (reporter > debug > addr_check). Before AMBA-MONBUS-STABILITY an addr_check
# packet presented into a stalled bus was replaced in that mux the moment the
# reporter's registered valid rose -- the payload changing underneath a held
# valid. Nothing was lost (a sink sampling on valid && ready never sees it),
# but a sink that latches on valid alone captures a torn packet.
#
# The assertion is the protocol rule itself rather than the specific scenario:
# whenever valid is high and ready is low, the packet must equal what it was
# the cycle before. That catches the addr_check case and any future source
# added to the mux with the same mistake.
#
# EVERYTHING IS DRIVEN THROUGH BFMs. An earlier version of this file drove
# monbus_ready and cmd_valid/data_valid by hand, on the reasoning that "the
# stall IS the stimulus so a BFM will not build it". That was wrong: every
# custom interface in this repo is valid/ready by construction, so GAXI binds
# to them even when several signals form the packet, and MonbusSlave's
# FlexRandomizer produces the stall through a long ready_delay profile -- the
# same knob used with a zero-delay profile elsewhere to hold ready asserted.
# Hand-driven stimulus is precisely what misses timing and protocol faults.
#
# One tie is NOT stimulus and is deliberate: axi_monitor_base takes cmd_valid
# AND cmd_ready as INPUTS -- it snoops a handshake rather than terminating one
# -- so there is no slave to source ready on that tap. It is held asserted
# while the GAXI master drives valid and the payload fields.

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

# Range 0 is a DEBUG range: a hit emits an AddrMatch packet from addr_check,
# which is the source that used to be displaced in the mux.
RANGE0_LOW = 0x0000_1000
RANGE0_HIGH = 0x0000_1FFF

# Long ready_delay: monbus is stalled most of the time, which is what lets a
# second source go valid underneath a beat that is already being presented.
STALL_PROFILE = FlexRandomizer({'ready_delay': ([(8, 20), (0, 2)], [8, 1])})


class StabilityTB(TBBase):

    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)
        self.violations = []
        self.stall_cycles = 0
        self.valid_cycles = 0
        self.cmd_master = None
        self.data_master = None
        self.mon_slave = None

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

        # Snooped-handshake ties. See the header: these are observed-bus
        # signals with no slave behind them, not transaction stimulus.
        d.cmd_ready.value = 1
        d.data_ready.value = 1
        d.clear.value = 0

        d.cfg_error_enable.value = 1
        d.cfg_compl_enable.value = 1
        d.cfg_threshold_enable.value = 0
        d.cfg_timeout_enable.value = 1
        d.cfg_perf_enable.value = 0
        # Gates the addr_check MATCH path -- without it there is no second
        # source to contend for the mux and the test proves nothing.
        d.cfg_debug_enable.value = 1

        d.cfg_freq_sel.value = 0
        d.cfg_addr_cnt.value = 10
        d.cfg_data_cnt.value = 10
        d.cfg_resp_cnt.value = 10
        d.cfg_active_trans_threshold.value = 1000
        d.cfg_latency_threshold.value = 10000
        d.cfg_debug_level.value = 0
        d.cfg_debug_mask.value = 0

        d.cfg_addr_check_enable.value = 1
        d.cfg_addr_range_enable.value = 0b01
        d.cfg_addr_range_low.value = RANGE0_LOW
        d.cfg_addr_range_high.value = RANGE0_HIGH

        d.cfg_addr_filter_enable.value = 0
        d.cfg_addr_filter_low.value = 0
        d.cfg_addr_filter_high.value = 0
        d.cfg_id_filter_enable.value = 0
        d.cfg_id_match_base.value = 0
        d.cfg_id_match_count.value = 0

        await RisingEdge(self.dut.aclk)

        # GAXI masters on the two taps. bus_name gives the valid/ready pair
        # (cmd_valid/cmd_ready), and multi_sig maps each field to its own
        # signal (cmd_addr, cmd_id, ...) -- the same shape the AXI4 BFMs use
        # internally for AW/W.
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

        # The consumer, and the source of the stall.
        self.mon_slave = MonbusSlave(
            dut=self.dut, title="MonBus", prefix="", clock=self.dut.aclk,
            bus_name="monbus", pkt_prefix="", log=self.log,
            randomizer=STALL_PROFILE)

    async def watch_stability(self):
        """The whole assertion: payload frozen across a held beat."""
        prev_valid = prev_ready = 0
        prev_pkt = None
        while True:
            await RisingEdge(self.dut.aclk)
            v = int(self.dut.monbus_valid.value)
            r = int(self.dut.monbus_ready.value)
            try:
                pkt = int(self.dut.monbus_packet.value)
            except ValueError:
                pkt = None                       # X during early reset

            if v:
                self.valid_cycles += 1
            if v and not r:
                self.stall_cycles += 1

            # The previous cycle presented a beat that was NOT accepted, and
            # valid is still high: same beat, so the payload must match.
            if prev_valid and not prev_ready and v \
                    and pkt is not None and prev_pkt is not None \
                    and pkt != prev_pkt:
                self.violations.append(
                    f"0x{prev_pkt:032x} -> 0x{pkt:032x}")

            prev_valid, prev_ready, prev_pkt = v, r, pkt

    async def send_read(self, addr, txn_id):
        """One snooped read: command beat then its data beat, both via BFM."""
        cmd = self.cmd_master.create_packet(
            addr=addr, id=txn_id, len=0, size=2, burst=1)
        await self.cmd_master.send(cmd)
        dat = self.data_master.create_packet(id=txn_id, last=1, resp=0)
        await self.data_master.send(dat)


@cocotb.test(timeout_time=120, timeout_unit="sec")
async def monbus_payload_stability_test(dut):
    tb = StabilityTB(dut)
    await tb.setup_clocks_and_reset()
    cocotb.start_soon(tb.watch_stability())

    # Alternate addresses inside range 0 (addr_check emits AddrMatch) with
    # addresses outside it, so addr_check and the reporter both contend for
    # the stalled output. Contention under backpressure is the condition.
    for i in range(48):
        inside = (i % 2 == 0)
        addr = (RANGE0_LOW + i * 0x10) if inside else (0x8000 + i * 0x10)
        await tb.send_read(addr, i % 16)

    for _ in range(600):
        await RisingEdge(dut.aclk)

    # Anti-vacuity: the run must actually have held beats under backpressure,
    # or "no violations" is a statement about nothing.
    assert tb.valid_cycles > 0, "monbus never asserted valid -- no traffic reached the bus"
    assert tb.stall_cycles > 20, (
        f"only {tb.stall_cycles} stalled-valid cycles; the ready_delay profile "
        f"did not build the condition under test")

    assert not tb.violations, (
        f"{len(tb.violations)} payload change(s) while valid && !ready; "
        f"first: {tb.violations[0]}")

    tb.log.info(f"PASS: {tb.valid_cycles} valid cycles, {tb.stall_cycles} "
                f"stalled, 0 payload changes under held valid")


@pytest.mark.parametrize("max_trans", [16])
def test_monbus_payload_stability(request, max_trans):
    """monbus_packet is stable while valid && !ready (AMBA-MONBUS-STABILITY)."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_amba': 'rtl/amba'})

    dut_name = "axi_monitor_base"
    test_name = f"test_{worker_id}_monbus_payload_stability_mt{max_trans}"
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
            'ID_WIDTH': '8', 'ADDR_WIDTH': '32',
            'UNIT_ID': '1', 'AGENT_ID': '10',
            'MAX_TRANSACTIONS': str(max_trans),
            'IS_READ': '1', 'IS_AXI': '1',
            'ENABLE_PERF_PACKETS': '0', 'ENABLE_DEBUG_MODULE': '0',
            # addr_check must be built, or the displaceable source is absent.
            'N_ADDR_RANGES': '2',
        },
        sim_build=sim_build,
        extra_env={
            'DUT': dut_name, 'LOG_PATH': log_path,
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
