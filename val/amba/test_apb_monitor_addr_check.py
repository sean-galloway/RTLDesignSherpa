# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_apb_monitor_addr_check
# Purpose: addr_pkt_data must not change while addr_pkt_valid && !addr_pkt_ready.
#
# apb_monitor_addr_check is documented as a "deliberate mirror" of
# axi_monitor_addr_check, and it mirrored the AMBA-MONBUS-STABILITY defect too:
# a fresh hit on a range overwrote that range's latched address unconditionally,
# including while that range's beat was already presented on a stalled bus. The
# payload then changed under a held valid, which the valid/ready contract
# forbids -- and the older violation's address was lost entirely, so the page's
# "a violation is not lost while the MonBus is backpressured" claim was false in
# exactly the case it named.
#
# The AXI sibling was fixed (per-range shadow slot) and its commit called that
# the "second and last instance". It was the second of three; this module is the
# third, and it had no test of its own at all, which is why it survived.
#
# The assertion is the protocol rule itself, not the scenario: whenever valid is
# high and ready is low, the packet must equal what it was the cycle before.
#
# Stimulus is BFM-driven. cmd_valid/cmd_ready are a SNOOPED handshake -- the
# module observes a bus rather than terminating one -- so cmd_ready is tied
# asserted while a GAXI master drives valid and the payload fields, exactly as
# test_monbus_payload_stability does. The stall comes from the consuming BFM's
# ready_delay profile, not from hand-poking ready.

import os
import random

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

from CocoTBFramework.components.gaxi.gaxi_factories import (
    create_gaxi_master, create_gaxi_slave)
from CocoTBFramework.components.shared.field_config import FieldConfig
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# TWO ranges, and the second is a HIGH index. That is deliberate: it makes the
# test cover both stability defects this module had.
#   - repeat hits on ONE range   -> the per-range payload overwrite (shadow slot)
#   - a LOW-index hit landing while a HIGH-index beat is stalled -> the emit
#     selection swapping under a held valid (first-match pick)
# A single-range version passes against the second defect and proves nothing.
RANGE0_LOW = 0x0000_1000
RANGE0_HIGH = 0x0000_1FFF
RANGE3_LOW = 0x0000_9000
RANGE3_HIGH = 0x0000_9FFF

# Long ready_delay: the bus is stalled most of the time, so a second hit on the
# SAME range lands while that range's beat is still being presented. That is the
# condition under test; without the stall the defect is unreachable.
STALL_PROFILE = FlexRandomizer({'ready_delay': ([(10, 24), (0, 2)], [9, 1])})


class ApbAddrCheckTB(TBBase):

    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)
        self.violations = []
        self.valid_cycles = 0
        self.stall_cycles = 0
        self.cmd_master = None
        self.pkt_slave = None

    async def setup_clocks_and_reset(self):
        await self.start_clock('clk', 10, 'ns')
        await self.assert_reset()
        for _ in range(10):
            await RisingEdge(self.dut.clk)
        await self.deassert_reset()
        for _ in range(5):
            await RisingEdge(self.dut.clk)
        await self.initialize_inputs()

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def initialize_inputs(self):
        d = self.dut

        # Snooped handshake: no slave behind it, so ready is a tie, not stimulus.
        d.cmd_ready.value = 1
        d.i_mon_time.value = 0

        d.cfg_addr_check_enable.value = 1
        # Ranges 0 and 3 enabled. cfg_addr_range_low/high are packed
        # [N_ADDR_RANGES-1:0][ADDR_WIDTH-1:0], so range i sits at bit i*32.
        d.cfg_addr_range_enable.value = (1 << 3) | (1 << 0)
        d.cfg_addr_range_low.value = (RANGE3_LOW << (3 * 32)) | RANGE0_LOW
        d.cfg_addr_range_high.value = (RANGE3_HIGH << (3 * 32)) | RANGE0_HIGH

        await RisingEdge(self.dut.clk)

        cmd_fields = FieldConfig.from_dict({
            'paddr':  {'bits': 32, 'format': 'hex'},
            'pwrite': {'bits': 1,  'format': 'dec'},
        })
        self.cmd_master = create_gaxi_master(
            dut=self.dut, title="CmdMaster", prefix="", clock=self.dut.clk,
            field_config=cmd_fields, bus_name="cmd", pkt_prefix="",
            multi_sig=True, log=self.log)

        # The consumer, and the source of the stall.
        pkt_fields = FieldConfig.from_dict({'data': {'bits': 128, 'format': 'hex'}})
        self.pkt_slave = create_gaxi_slave(
            dut=self.dut, title="PktSlave", prefix="", clock=self.dut.clk,
            field_config=pkt_fields, bus_name="addr_pkt", pkt_prefix="",
            multi_sig=True, log=self.log, randomizer=STALL_PROFILE)

    async def watch_stability(self):
        """The whole assertion: payload frozen across a held beat."""
        prev_valid = prev_ready = 0
        prev_pkt = None
        while True:
            await RisingEdge(self.dut.clk)
            v = int(self.dut.addr_pkt_valid.value)
            r = int(self.dut.addr_pkt_ready.value)
            try:
                pkt = int(self.dut.addr_pkt_data.value)
            except ValueError:
                pkt = None                        # X during early reset

            if v:
                self.valid_cycles += 1
            if v and not r:
                self.stall_cycles += 1

            if prev_valid and not prev_ready and v \
                    and pkt is not None and prev_pkt is not None \
                    and pkt != prev_pkt:
                self.violations.append(f"0x{prev_pkt:032x} -> 0x{pkt:032x}")

            prev_valid, prev_ready, prev_pkt = v, r, pkt

    async def send_cmd(self, addr, is_write):
        pkt = self.cmd_master.create_packet(paddr=addr, pwrite=1 if is_write else 0)
        await self.cmd_master.send(pkt)


@cocotb.test(timeout_time=120, timeout_unit="sec")
async def apb_addr_check_payload_stability_test(dut):
    tb = ApbAddrCheckTB(dut)
    await tb.setup_clocks_and_reset()
    cocotb.start_soon(tb.watch_stability())

    # Alternate range 3 and range 0. Consecutive same-range hits exercise the
    # payload overwrite; a range-0 hit landing while a range-3 beat is stalled
    # exercises the selection swap. Addresses differ every time, so either
    # defect shows up as a packet change under a held valid.
    for i in range(64):
        base = RANGE3_LOW if (i % 2 == 0) else RANGE0_LOW
        await tb.send_cmd(base + (i * 0x10), is_write=(i % 2 == 0))

    for _ in range(800):
        await RisingEdge(dut.clk)

    # Anti-vacuity: without held beats, "no violations" says nothing.
    assert tb.valid_cycles > 0, "addr_pkt never asserted valid -- no hits reached the bus"
    assert tb.stall_cycles > 20, (
        f"only {tb.stall_cycles} stalled-valid cycles; the ready_delay profile "
        f"did not build the condition under test")

    assert not tb.violations, (
        f"{len(tb.violations)} payload change(s) while valid && !ready; "
        f"first: {tb.violations[0]}")

    tb.log.info(f"PASS: {tb.valid_cycles} valid cycles, {tb.stall_cycles} "
                f"stalled, 0 payload changes under held valid")


@pytest.mark.parametrize("n_ranges", [4])
def test_apb_monitor_addr_check(request, n_ranges):
    """addr_pkt_data is stable while valid && !ready (AMBA-MONBUS-STABILITY)."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_amba': 'rtl/amba'})

    dut_name = "apb_monitor_addr_check"
    test_name = f"test_{worker_id}_apb_monitor_addr_check_n{n_ranges}"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/apb_monitor_addr_check.f")

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=os.path.splitext(os.path.basename(__file__))[0],
        parameters={
            'N_ADDR_RANGES': str(n_ranges),
            'ADDR_WIDTH': '32',
            'UNIT_ID': '1',
            'AGENT_ID': '10',
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
            "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC",
            "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE", "-Wno-TIMESCALEMOD",
        ],
    )
