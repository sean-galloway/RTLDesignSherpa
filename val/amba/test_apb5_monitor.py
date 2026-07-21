# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb5_monitor
# Purpose: Test runner for APB5 monitor with AMBA5 extensions
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-12-21

"""
APB5 Monitor Test Runner

Tests APB5 monitor functionality with AMBA5 extensions:
- User signal capture
- Wake-up event detection
- Parity error detection
- Transaction timing monitoring
"""
import os
import random

import pytest
import cocotb
from cocotb.triggers import Timer, RisingEdge, FallingEdge
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist


class APB5MonitorTB(TBBase):
    """APB5 monitor testbench for RTL verification."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '12'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.AUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_AUSER_WIDTH', '4'))
        self.WUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_WUSER_WIDTH', '4'))
        self.RUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_RUSER_WIDTH', '4'))
        self.BUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_BUSER_WIDTH', '4'))

        self.log.info("="*60)
        self.log.info(" APB5 Monitor Testbench Configuration")
        self.log.info("-"*60)
        self.log.info(f" ADDR_WIDTH:  {self.ADDR_WIDTH}")
        self.log.info(f" DATA_WIDTH:  {self.DATA_WIDTH}")
        self.log.info(f" AUSER_WIDTH: {self.AUSER_WIDTH}")
        self.log.info(f" WUSER_WIDTH: {self.WUSER_WIDTH}")
        self.log.info(f" RUSER_WIDTH: {self.RUSER_WIDTH}")
        self.log.info(f" BUSER_WIDTH: {self.BUSER_WIDTH}")
        self.log.info("="*60)

        # Track monitor packets
        self.monitor_packets = []

    # ------------------------------------------------------------------
    # 128-bit monitor packet decode (monitor_package_spec.md)
    #   [127:124] packet_type   [123:109] reserved   [108:105] protocol
    #   [104: 97] event_code    [ 96: 88] channel_id [ 87: 72] agent_id
    #   [ 71: 64] unit_id       [ 63:  0] event_data
    # ------------------------------------------------------------------
    @staticmethod
    def decode_packet(pkt: int) -> dict:
        """Decode a 128-bit monbus packet into its named fields."""
        return {
            'packet_type': (pkt >> 124) & 0xF,
            'protocol':    (pkt >> 105) & 0xF,
            'event_code':  (pkt >> 97) & 0xFF,
            'channel_id':  (pkt >> 88) & 0x1FF,
            'agent_id':    (pkt >> 72) & 0xFFFF,
            'unit_id':     (pkt >> 64) & 0xFF,
            'event_data':  pkt & ((1 << 64) - 1),
        }

    async def drive_mon_time(self):
        """Free-running monitor-time broadcast (normally from monbus_group)."""
        self.dut.i_mon_time.value = 0
        count = 0
        while True:
            await RisingEdge(self.dut.aclk)
            count = (count + 1) & ((1 << 64) - 1)
            self.dut.i_mon_time.value = count

    async def assert_reset(self):
        """Assert reset."""
        self.dut.aresetn.value = 0
        await self.wait_clocks('aclk', 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset."""
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 5)
        self.log.info("Reset deasserted")

    async def setup_clocks_and_reset(self):
        """Setup clocks and reset sequence."""
        await self.start_clock('aclk', 10, 'ns')
        await self.assert_reset()
        await self.deassert_reset()

    async def drive_cmd_write(self, paddr, pwdata, pstrb=0xF, pprot=0, pauser=0, pwuser=0):
        """Drive a write command through the command interface."""
        # Wait for ready
        while not self.dut.cmd_ready.value:
            await RisingEdge(self.dut.aclk)

        # Drive command
        self.dut.cmd_valid.value = 1
        self.dut.cmd_pwrite.value = 1
        self.dut.cmd_paddr.value = paddr
        self.dut.cmd_pwdata.value = pwdata
        self.dut.cmd_pstrb.value = pstrb
        self.dut.cmd_pprot.value = pprot
        self.dut.cmd_pauser.value = pauser
        self.dut.cmd_pwuser.value = pwuser

        await RisingEdge(self.dut.aclk)
        self.dut.cmd_valid.value = 0

        self.log.info(f"CMD Write: addr=0x{paddr:04X} data=0x{pwdata:08X}")

    async def drive_cmd_read(self, paddr, pprot=0, pauser=0):
        """Drive a read command through the command interface."""
        # Wait for ready
        while not self.dut.cmd_ready.value:
            await RisingEdge(self.dut.aclk)

        # Drive command
        self.dut.cmd_valid.value = 1
        self.dut.cmd_pwrite.value = 0
        self.dut.cmd_paddr.value = paddr
        self.dut.cmd_pwdata.value = 0
        self.dut.cmd_pstrb.value = 0
        self.dut.cmd_pprot.value = pprot
        self.dut.cmd_pauser.value = pauser
        self.dut.cmd_pwuser.value = 0

        await RisingEdge(self.dut.aclk)
        self.dut.cmd_valid.value = 0

        self.log.info(f"CMD Read: addr=0x{paddr:04X}")

    async def drive_rsp(self, prdata, pslverr=0, pruser=0, pbuser=0):
        """Drive a response through the response interface."""
        # Wait for ready
        while not self.dut.rsp_ready.value:
            await RisingEdge(self.dut.aclk)

        # Drive response
        self.dut.rsp_valid.value = 1
        self.dut.rsp_prdata.value = prdata
        self.dut.rsp_pslverr.value = pslverr
        self.dut.rsp_pruser.value = pruser
        self.dut.rsp_pbuser.value = pbuser

        await RisingEdge(self.dut.aclk)
        self.dut.rsp_valid.value = 0

        self.log.info(f"RSP: data=0x{prdata:08X} err={pslverr}")

    async def drive_wakeup(self, cycles=3):
        """Drive PWAKEUP signal."""
        self.dut.apb5_pwakeup.value = 1
        self.log.info("PWAKEUP asserted")
        await self.wait_clocks('aclk', cycles)
        self.dut.apb5_pwakeup.value = 0
        self.log.info("PWAKEUP deasserted")

    async def capture_monitor_output(self, timeout_cycles=10):
        """Capture monitor packet output."""
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.aclk)
            if self.dut.monbus_valid.value:
                packet = int(self.dut.monbus_packet.value)
                self.monitor_packets.append(packet)
                self.log.info(f"Monitor packet captured: 0x{packet:016X}")


@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_apb5_monitor_basic(dut):
    """Basic APB5 monitor test - verifies transaction capture and event detection."""
    tb = APB5MonitorTB(dut)

    # Broadcast monitor time must be driven before reset releases
    dut.i_mon_time.value = 0

    # Setup
    await tb.setup_clocks_and_reset()
    cocotb.start_soon(tb.drive_mon_time())

    # Initialize command interface signals
    dut.cmd_valid.value = 0
    dut.cmd_pwrite.value = 0
    dut.cmd_paddr.value = 0
    dut.cmd_pwdata.value = 0
    dut.cmd_pstrb.value = 0
    dut.cmd_pprot.value = 0
    dut.cmd_pauser.value = 0
    dut.cmd_pwuser.value = 0

    # Initialize response interface signals
    dut.rsp_valid.value = 0
    dut.rsp_prdata.value = 0
    dut.rsp_pslverr.value = 0
    dut.rsp_pruser.value = 0
    dut.rsp_pbuser.value = 0

    # Initialize APB5-specific signals
    dut.apb5_pwakeup.value = 0
    dut.parity_error_wdata.value = 0
    dut.parity_error_rdata.value = 0
    dut.parity_error_ctrl.value = 0

    # Initialize configuration signals
    dut.cfg_error_enable.value = 1
    dut.cfg_timeout_enable.value = 1
    dut.cfg_protocol_enable.value = 1
    dut.cfg_slverr_enable.value = 1
    dut.cfg_parity_enable.value = 0
    dut.cfg_wakeup_enable.value = 1
    dut.cfg_user_enable.value = 1
    dut.cfg_perf_enable.value = 1
    dut.cfg_latency_enable.value = 1
    dut.cfg_cmd_timeout_cnt.value = 100
    dut.cfg_rsp_timeout_cnt.value = 100
    dut.cfg_latency_threshold.value = 50
    dut.cfg_wakeup_timeout_cnt.value = 100

    # Initialize monitor bus ready (as consumer)
    dut.monbus_ready.value = 1

    # Note: cmd_ready and rsp_ready are outputs from monitor, not inputs
    # The monitor observes these signals but doesn't control them

    await tb.wait_clocks('aclk', 5)

    # Test 1: Monitor write transaction
    tb.log.info("=== Test 1: Monitor Write Transaction ===")
    # Simulate a command being accepted
    dut.cmd_valid.value = 1
    dut.cmd_ready.value = 1  # Simulating the observed ready signal
    dut.cmd_pwrite.value = 1
    dut.cmd_paddr.value = 0x100
    dut.cmd_pwdata.value = 0x12345678
    dut.cmd_pstrb.value = 0xF
    dut.cmd_pauser.value = 0x5
    dut.cmd_pwuser.value = 0x3
    await RisingEdge(dut.aclk)
    dut.cmd_valid.value = 0
    await RisingEdge(dut.aclk)

    # Simulate response
    dut.rsp_valid.value = 1
    dut.rsp_ready.value = 1  # Simulating observed ready
    dut.rsp_prdata.value = 0
    dut.rsp_pslverr.value = 0
    dut.rsp_pbuser.value = 0x4
    await RisingEdge(dut.aclk)
    dut.rsp_valid.value = 0
    await tb.capture_monitor_output()
    await tb.wait_clocks('aclk', 5)

    # Test 2: Monitor read transaction
    tb.log.info("=== Test 2: Monitor Read Transaction ===")
    dut.cmd_valid.value = 1
    dut.cmd_ready.value = 1
    dut.cmd_pwrite.value = 0
    dut.cmd_paddr.value = 0x100
    dut.cmd_pauser.value = 0x7
    await RisingEdge(dut.aclk)
    dut.cmd_valid.value = 0
    await RisingEdge(dut.aclk)

    dut.rsp_valid.value = 1
    dut.rsp_ready.value = 1
    dut.rsp_prdata.value = 0xDEADBEEF
    dut.rsp_pslverr.value = 0
    dut.rsp_pruser.value = 0xA
    await RisingEdge(dut.aclk)
    dut.rsp_valid.value = 0
    await tb.capture_monitor_output()
    await tb.wait_clocks('aclk', 5)

    # Test 3: Monitor error transaction
    tb.log.info("=== Test 3: Monitor Error Transaction ===")
    dut.cmd_valid.value = 1
    dut.cmd_ready.value = 1
    dut.cmd_pwrite.value = 0
    dut.cmd_paddr.value = 0x200
    dut.cmd_pauser.value = 0xB
    await RisingEdge(dut.aclk)
    dut.cmd_valid.value = 0
    await RisingEdge(dut.aclk)

    dut.rsp_valid.value = 1
    dut.rsp_ready.value = 1
    dut.rsp_prdata.value = 0
    dut.rsp_pslverr.value = 1  # Error response
    dut.rsp_pruser.value = 0xC
    await RisingEdge(dut.aclk)
    dut.rsp_valid.value = 0
    await tb.capture_monitor_output()
    await tb.wait_clocks('aclk', 5)

    # Test 4: Monitor wakeup event
    tb.log.info("=== Test 4: Monitor Wakeup Event ===")
    await tb.drive_wakeup(cycles=3)
    await tb.capture_monitor_output()
    await tb.wait_clocks('aclk', 5)

    # Test 5: Multiple transactions
    tb.log.info("=== Test 5: Multiple Transactions ===")
    for i in range(5):
        dut.cmd_valid.value = 1
        dut.cmd_ready.value = 1
        dut.cmd_pwrite.value = i % 2
        dut.cmd_paddr.value = 0x300 + (i * 4)
        dut.cmd_pwdata.value = 0xABCD0000 + i if (i % 2) else 0
        dut.cmd_pauser.value = i & 0xF
        dut.cmd_pwuser.value = (i + 1) & 0xF
        await RisingEdge(dut.aclk)
        dut.cmd_valid.value = 0
        await RisingEdge(dut.aclk)

        dut.rsp_valid.value = 1
        dut.rsp_ready.value = 1
        dut.rsp_prdata.value = 0x55AA0000 + i
        dut.rsp_pslverr.value = 0
        dut.rsp_pruser.value = (i + 2) & 0xF
        await RisingEdge(dut.aclk)
        dut.rsp_valid.value = 0
        await tb.capture_monitor_output()

    # Report captured packets
    tb.log.info(f"=== Captured {len(tb.monitor_packets)} monitor packets ===")
    for i, pkt in enumerate(tb.monitor_packets):
        tb.log.info(f"  Packet {i}: 0x{pkt:016X}")

    tb.log.info("=== APB5 Monitor Basic Test PASSED ===")


@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_apb5_monitor_addr_range(dut):
    """Address-range violation packets must carry correct 128-bit header fields.

    Regression for issue #41: apb5_monitor connected the 128-bit addr_pkt_data
    output of apb_monitor_addr_check to a 64-bit net, discarding every header
    field. A hit on range 3 decoded as packet_type=3 (PktTypeTimeout) with
    protocol=AXI, event_code=0x00 and the address shifted right by 3.

    Requires N_ADDR_RANGES > 0 -- the default of 0 elides the checker entirely,
    which is why this path was previously uncovered.
    """
    tb = APB5MonitorTB(dut)

    dut.i_mon_time.value = 0
    await tb.setup_clocks_and_reset()
    cocotb.start_soon(tb.drive_mon_time())

    # Quiesce every other event source so only range violations reach the bus
    for sig in ('cmd_valid', 'cmd_ready', 'cmd_pwrite', 'cmd_paddr', 'cmd_pwdata',
                'cmd_pstrb', 'cmd_pprot', 'cmd_pauser', 'cmd_pwuser',
                'rsp_valid', 'rsp_ready', 'rsp_prdata', 'rsp_pslverr',
                'rsp_pruser', 'rsp_pbuser', 'apb5_pwakeup',
                'parity_error_wdata', 'parity_error_rdata', 'parity_error_ctrl',
                'cfg_error_enable', 'cfg_timeout_enable', 'cfg_protocol_enable',
                'cfg_slverr_enable', 'cfg_parity_enable', 'cfg_wakeup_enable',
                'cfg_user_enable', 'cfg_perf_enable', 'cfg_latency_enable',
                'cfg_cmd_timeout_cnt', 'cfg_rsp_timeout_cnt',
                'cfg_latency_threshold', 'cfg_wakeup_timeout_cnt'):
        getattr(dut, sig).value = 0

    dut.monbus_ready.value = 1

    # Exercise every configured range. Range index 3 is the case that
    # previously aliased onto the packet_type field.
    n_ranges = int(os.environ.get('TEST_N_ADDR_RANGES', '4'))
    aw = tb.ADDR_WIDTH
    ranges = [(0x100 * (i + 1), 0x100 * (i + 1) + 0xFF) for i in range(n_ranges)]

    def pack(values):
        """Pack a list into a SystemVerilog packed array (index 0 = LSBs)."""
        word = 0
        for i, v in enumerate(values):
            word |= (v & ((1 << aw) - 1)) << (i * aw)
        return word

    dut.cfg_addr_check_enable.value = 1
    dut.cfg_addr_range_enable.value = (1 << n_ranges) - 1
    dut.cfg_addr_range_low.value = pack([lo for lo, _ in ranges])
    dut.cfg_addr_range_high.value = pack([hi for _, hi in ranges])

    await tb.wait_clocks('aclk', 5)

    async def issue_cmd(addr, is_write):
        """Drive one accepted command and collect any emitted packet."""
        dut.cmd_paddr.value = addr
        dut.cmd_pwrite.value = 1 if is_write else 0
        dut.cmd_valid.value = 1
        dut.cmd_ready.value = 1
        await RisingEdge(dut.aclk)
        dut.cmd_valid.value = 0
        dut.cmd_ready.value = 0

        captured = []
        for _ in range(12):
            await RisingEdge(dut.aclk)
            if dut.monbus_valid.value:
                captured.append((int(dut.monbus_packet.value),
                                 int(dut.monbus_timestamp.value)))
        return captured

    # --- every configured range, both directions ---
    for idx, (lo, hi) in enumerate(ranges):
        for is_write in (True, False):
            addr = lo + 0x23
            pkts = await issue_cmd(addr, is_write)

            assert len(pkts) == 1, \
                f"range {idx} addr 0x{addr:X}: expected 1 packet, got {len(pkts)}"

            raw, ts = pkts[0]
            f = tb.decode_packet(raw)
            tb.log.info(f"range {idx} {'WR' if is_write else 'RD'} "
                        f"addr=0x{addr:X} raw=0x{raw:032X} ts={ts} -> {f}")

            # The three fields the truncation destroyed
            assert f['packet_type'] == 0x0, \
                f"packet_type: got 0x{f['packet_type']:X}, expected 0x0 (PktTypeError)"
            assert f['protocol'] == 0x2, \
                f"protocol: got 0x{f['protocol']:X}, expected 0x2 (PROTOCOL_APB)"
            assert f['event_code'] == 0x08, \
                f"event_code: got 0x{f['event_code']:02X}, expected 0x08 (APB_ERR_ADDR_RANGE)"

            # Identity fields, also lost with the header
            assert f['unit_id'] == 0x01, f"unit_id: got 0x{f['unit_id']:X}"
            assert f['agent_id'] == 0x000A, f"agent_id: got 0x{f['agent_id']:X}"
            assert f['channel_id'] == 0, f"channel_id: got 0x{f['channel_id']:X}"

            # event_data[63:60]=range_index, [59]=is_read, [58:0]=address
            ev = f['event_data']
            assert (ev >> 60) & 0xF == idx, \
                f"range index: got {(ev >> 60) & 0xF}, expected {idx}"
            assert (ev >> 59) & 0x1 == (0 if is_write else 1), "is_read bit wrong"
            assert ev & ((1 << 59) - 1) == addr, \
                f"address: got 0x{ev & ((1 << 59) - 1):X}, expected 0x{addr:X}"

            # i_mon_time is plumbed through to the side-band timestamp
            assert ts != 0, "monbus_timestamp is zero - i_mon_time not connected"

    # --- address outside every range emits nothing ---
    outside = await issue_cmd(ranges[-1][1] + 0x100, True)
    assert not outside, f"out-of-range address emitted {len(outside)} packet(s)"

    # --- checker disabled emits nothing ---
    dut.cfg_addr_check_enable.value = 0
    await tb.wait_clocks('aclk', 2)
    disabled = await issue_cmd(ranges[0][0] + 0x23, True)
    assert not disabled, f"disabled checker emitted {len(disabled)} packet(s)"

    tb.log.info("=== APB5 Monitor Address-Range Test PASSED ===")


@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_apb5_monitor_timeout_edge(dut):
    """A stuck command must produce ONE timeout packet, not one per cycle.

    Regression for issue #41: the timeout/protocol/parity/latency event
    conditions are levels, and were fed straight into the FIFO write. A single
    stuck command held the condition true for many cycles and emitted an
    identical packet every cycle (the audit observed 21). Every level condition
    is now edge-qualified.
    """
    tb = APB5MonitorTB(dut)

    dut.i_mon_time.value = 0
    await tb.setup_clocks_and_reset()
    cocotb.start_soon(tb.drive_mon_time())

    for sig in ('cmd_valid', 'cmd_ready', 'cmd_pwrite', 'cmd_paddr', 'cmd_pwdata',
                'cmd_pstrb', 'cmd_pprot', 'cmd_pauser', 'cmd_pwuser',
                'rsp_valid', 'rsp_ready', 'rsp_prdata', 'rsp_pslverr',
                'rsp_pruser', 'rsp_pbuser', 'apb5_pwakeup',
                'parity_error_wdata', 'parity_error_rdata', 'parity_error_ctrl',
                'cfg_error_enable', 'cfg_protocol_enable', 'cfg_slverr_enable',
                'cfg_parity_enable', 'cfg_wakeup_enable', 'cfg_user_enable',
                'cfg_perf_enable', 'cfg_latency_enable', 'cfg_latency_threshold',
                'cfg_wakeup_timeout_cnt', 'cfg_addr_check_enable',
                'cfg_addr_range_enable', 'cfg_addr_range_low',
                'cfg_addr_range_high'):
        getattr(dut, sig).value = 0

    dut.monbus_ready.value = 1

    # Short timeout so the stuck condition trips quickly, then holds
    timeout_cycles = 8
    dut.cfg_timeout_enable.value = 1
    dut.cfg_cmd_timeout_cnt.value = timeout_cycles
    dut.cfg_rsp_timeout_cnt.value = timeout_cycles
    await tb.wait_clocks('aclk', 5)

    # Stick a command: cmd_valid high, cmd_ready never asserted.
    # The command-timeout condition goes true and STAYS true.
    dut.cmd_paddr.value = 0x40
    dut.cmd_pwrite.value = 1
    dut.cmd_valid.value = 1
    dut.cmd_ready.value = 0

    packets = []
    hold_cycles = 40  # far longer than the timeout threshold
    for _ in range(hold_cycles):
        await RisingEdge(dut.aclk)
        if dut.monbus_valid.value:
            packets.append(int(dut.monbus_packet.value))

    dut.cmd_valid.value = 0

    for pkt in packets:
        f = tb.decode_packet(pkt)
        tb.log.info(f"timeout packet: {f}")

    timeouts = [p for p in packets if tb.decode_packet(p)['packet_type'] == 0x3]

    tb.log.info(f"stuck for {hold_cycles} cycles (threshold {timeout_cycles}): "
                f"{len(timeouts)} timeout packet(s)")

    assert len(timeouts) == 1, (
        f"expected exactly 1 timeout packet from one stuck command, got "
        f"{len(timeouts)} - level-sensitive condition is not edge-qualified")

    f = tb.decode_packet(timeouts[0])
    assert f['protocol'] == 0x2, f"protocol 0x{f['protocol']:X} != 0x2 (APB)"

    tb.log.info("=== APB5 Monitor Timeout Edge-Detect Test PASSED ===")


def generate_apb5_monitor_params():
    """Generate test parameters for APB5 monitor."""
    return [
        # addr_width, data_width, auser_width, wuser_width, ruser_width, buser_width
        (12, 32, 4, 4, 4, 4),
        (16, 32, 8, 8, 8, 8),
    ]


@pytest.mark.parametrize(
    "addr_width, data_width, auser_width, wuser_width, ruser_width, buser_width",
    generate_apb5_monitor_params()
)
def test_apb5_monitor(request, addr_width, data_width, auser_width, wuser_width,
                      ruser_width, buser_width):
    """APB5 monitor test runner."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_apb5': 'rtl/amba/apb5',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    toplevel = "apb5_monitor"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/apb5_monitor.f")

    # Test identifier
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    au_str = TBBase.format_dec(auser_width, 1)
    test_name_plus_params = f"test_{worker_id}_apb5_monitor_aw{aw_str}_dw{dw_str}_au{au_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    includes=includes

    # RTL parameters
    rtl_parameters = {
        'ADDR_WIDTH': str(addr_width),
        'DATA_WIDTH': str(data_width),
        'AUSER_WIDTH': str(auser_width),
        'WUSER_WIDTH': str(wuser_width),
        'RUSER_WIDTH': str(ruser_width),
        'BUSER_WIDTH': str(buser_width),
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': toplevel,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_AUSER_WIDTH': str(auser_width),
        'TEST_WUSER_WIDTH': str(wuser_width),
        'TEST_RUSER_WIDTH': str(ruser_width),
        'TEST_BUSER_WIDTH': str(buser_width),
    }

    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "-Wno-TIMESCALEMOD",
        "-Wno-WIDTHTRUNC",
        "-Wno-WIDTHEXPAND",
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend([])

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            plus_args=(['--trace'] if enable_waves else []),
            keep_files=True,
            compile_args=compile_args,
            testcase="cocotb_test_apb5_monitor_basic",
            simulator="verilator",
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise


def test_apb5_monitor_timeout_edge(request):
    """APB5 monitor timeout edge-detection test runner (issue #41 regression)."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_apb5': 'rtl/amba/apb5',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    toplevel = "apb5_monitor"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/apb5_monitor.f")

    test_name_plus_params = f"test_{worker_id}_apb5_monitor_timeout_edge"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        'ADDR_WIDTH': '12',
        'DATA_WIDTH': '32',
        'N_ADDR_RANGES': '1',
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': toplevel,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_ADDR_WIDTH': '12',
        'TEST_DATA_WIDTH': '32',
    }

    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "-Wno-TIMESCALEMOD",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            plus_args=(['--trace'] if enable_waves else []),
            keep_files=True,
            compile_args=compile_args,
            testcase="cocotb_test_apb5_monitor_timeout_edge",
            simulator="verilator",
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise


@pytest.mark.parametrize("addr_width, n_addr_ranges", [(12, 4), (16, 8)])
def test_apb5_monitor_addr_range(request, addr_width, n_addr_ranges):
    """APB5 monitor address-range violation test runner (issue #41 regression).

    N_ADDR_RANGES must be > 0 or the checker is elided by its generate guard,
    which is how the 128-bit packet truncation escaped every existing harness.
    """
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_apb5': 'rtl/amba/apb5',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    toplevel = "apb5_monitor"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/apb5_monitor.f")

    aw_str = TBBase.format_dec(addr_width, 2)
    nr_str = TBBase.format_dec(n_addr_ranges, 2)
    test_name_plus_params = f"test_{worker_id}_apb5_monitor_addr_range_aw{aw_str}_nr{nr_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        'ADDR_WIDTH': str(addr_width),
        'DATA_WIDTH': '32',
        'N_ADDR_RANGES': str(n_addr_ranges),
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': toplevel,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': '32',
        'TEST_N_ADDR_RANGES': str(n_addr_ranges),
    }

    # NOTE: no -Wno-WIDTHEXPAND / -Wno-WIDTHTRUNC here. Those suppressions are
    # what let the 128-bit-into-64-bit port truncation compile silently.
    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "-Wno-TIMESCALEMOD",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            plus_args=(['--trace'] if enable_waves else []),
            keep_files=True,
            compile_args=compile_args,
            testcase="cocotb_test_apb5_monitor_addr_range",
            simulator="verilator",
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
