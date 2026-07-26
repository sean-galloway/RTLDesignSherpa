# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_monbus_axil_axil_group_serializer
# Purpose: Regression coverage for the 32-bit err-drain 2:1 read serializer
#          against differently-shaped but equally legal AXI4-Lite read
#          masters (GitHub issue #41, defect 1).
#
# Documentation: docs/markdown/rtl-amba/index.md
# Subsystem: amba (shared)
#
# Author: sean galloway
# Created: 2026-07-20

"""
MonBus AXIL/AXIL Group -- 32-bit Err-Drain Serializer, Master-Shape Regression

Targets the `g_drain_2to1` block in
`rtl/amba/monitor/monbus_axil_axil_group.sv` (the identical construct in
`monbus_axil_axi4_group.sv` is exercised by the same drivers when
TEST_DUT=axil_axi4).

WHY THIS TEST EXISTS
--------------------
With S_AXIL_DATA_WIDTH=32 the wrapper splits each 64-bit err-FIFO slice into
a low then a high 32-bit external read, so one monbus record (3 slices) costs
6 external reads but must cost exactly 3 SIXTY-FOUR-bit reads at the leaf.

The original AR router keyed off the R-side phase bit::

    assign drv_arvalid    = (r_phase == PH_LOW) && s_axil_arvalid;
    assign s_axil_arready = (r_phase == PH_LOW) ? drv_arready : !r_hi_ar;

`r_phase` only advances on the low-phase R handshake. A master that asserts
ARVALID for the *high* read before that handshake -- which AXI4-Lite fully
permits, since nothing orders AR(n+1) after R(n) -- had that AR routed to the
leaf as an extra 64-bit core read. The serializer then entered PH_HIGH with
r_hi_ar=0 and waited forever for an AR the master had already issued.

The pre-existing suite never saw this because its only drain master
(`MonbusGroupHarness.drain_read_beat`) is strictly serialized: it waits for
the R beat before issuing the next AR. That master is preserved here as the
CONTROL CASE so the difference between the two shapes is recorded in the
suite, not just in a bug report.

Test Types (all read the same records; only the master's AR/R shape differs):
- 'strict':      ARVALID and RREADY raised together; AR(n+1) after R(n).
                 Mirrors MonbusGroupHarness.drain_read_beat. Control case --
                 this one passed even with the defect present.
- 'late_rready': single-outstanding, but RREADY raised only after this read's
                 AR was accepted. Also passed with the defect present.
- 'pipelined':   ARVALID for read n+1 asserted as soon as AR(n) was accepted,
                 without waiting for R(n). This is the shape that hung.

STRUCTURE FOLLOWS REPOSITORY STANDARD:
  - Single CocoTB test function (dispatches based on TEST_TYPE)
  - Single parameter generator (includes test_type as first parameter)
  - Single pytest wrapper (fully parametrized)
"""

import os
import sys

import pytest
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)


# Number of 32-bit external beats that make up one monbus record:
# 3 x 64-bit slices ({tag,ts}, packet[127:64], packet[63:0]) x 2 halves.
BEATS_PER_RECORD_32 = 6

# Per-handshake patience, in clock cycles. Generous enough to absorb FIFO
# latency, tight enough that a hang is reported as a precise assertion rather
# than as an opaque cocotb test timeout.
HANDSHAKE_TIMEOUT = 400


class SerializerDrainTB(TBBase):
    """Drives the 32-bit err-drain port with several legal AXI4-Lite read
    master shapes and reassembles the monbus records that come back.

    Signals are poked directly rather than through an AXI BFM on purpose:
    the property under test is the precise interleaving of AR and R, which no
    BFM exposes as a knob. The shared MonbusGroupHarness drain (the strict
    shape) is reproduced here as the control case so all three shapes sit
    side by side in one file.
    """

    def __init__(self, dut):
        super().__init__(dut)
        self.clk_name = 'axi_aclk'
        self.axi_aclk = dut.axi_aclk
        self.rst_n = dut.axi_aresetn
        self.beats = []
        self.ar_accepted = 0

    # ---- MANDATORY three methods -----------------------------------------

    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    # ---- configuration ----------------------------------------------------

    async def initialize(self):
        """Route ERROR packets into the err FIFO and idle every interface."""
        dut = self.dut
        dut.monbus_valid.value = 0
        dut.monbus_packet.value = 0
        dut.monbus_timestamp.value = 0
        dut.cam_clear.value = 0

        dut.s_axil_arvalid.value = 0
        dut.s_axil_araddr.value = 0
        dut.s_axil_arprot.value = 0
        dut.s_axil_rready.value = 0

        # Master-write side: accept and discard, so the bulk path never
        # backpressures the core while we are draining the err FIFO.
        dut.m_axil_awready.value = 1
        dut.m_axil_wready.value = 1
        dut.m_axil_bvalid.value = 0
        dut.m_axil_bresp.value = 0

        dut.cfg_base_addr.value = 0x0000_1000
        dut.cfg_limit_addr.value = 0x0000_5000 - 1
        dut.cfg_flush_watermark.value = 0xFFFF     # never watermark-flush
        dut.cfg_compress_en.value = 0

        # Route ERROR packets to the err FIFO; drop nothing.
        dut.cfg_axi_pkt_mask.value = 0x0000
        dut.cfg_axi_err_select.value = 0xFFFF
        for name in ('cfg_axi_error_mask', 'cfg_axi_timeout_mask',
                     'cfg_axi_compl_mask', 'cfg_axi_thresh_mask',
                     'cfg_axi_perf_mask', 'cfg_axi_addr_mask',
                     'cfg_axi_debug_mask',
                     'cfg_axis_pkt_mask', 'cfg_axis_err_select',
                     'cfg_axis_error_mask', 'cfg_axis_timeout_mask',
                     'cfg_axis_compl_mask', 'cfg_axis_credit_mask',
                     'cfg_axis_channel_mask', 'cfg_axis_stream_mask',
                     'cfg_core_pkt_mask', 'cfg_core_err_select',
                     'cfg_core_error_mask', 'cfg_core_timeout_mask',
                     'cfg_core_compl_mask', 'cfg_core_thresh_mask',
                     'cfg_core_perf_mask', 'cfg_core_debug_mask'):
            getattr(dut, name).value = 0

        await self.wait_clocks(self.clk_name, 2)

    # ---- monbus injection -------------------------------------------------

    async def push_record(self, packet: int, timestamp: int):
        """Push one monbus packet + timestamp into the group."""
        dut = self.dut
        await FallingEdge(self.axi_aclk)
        dut.monbus_packet.value = packet
        dut.monbus_timestamp.value = timestamp
        dut.monbus_valid.value = 1
        for _ in range(HANDSHAKE_TIMEOUT):
            await RisingEdge(self.axi_aclk)
            if int(dut.monbus_ready.value) == 1:
                break
        else:
            raise AssertionError("monbus_valid/ready handshake never completed")
        await FallingEdge(self.axi_aclk)
        dut.monbus_valid.value = 0

    # ---- drain masters ----------------------------------------------------

    async def _accept_one_ar(self, hold_arvalid: bool):
        """Assert ARVALID and wait for its handshake. If hold_arvalid, leave
        ARVALID asserted afterwards so the next AR follows back-to-back."""
        dut = self.dut
        await FallingEdge(self.axi_aclk)
        dut.s_axil_arvalid.value = 1
        for _ in range(HANDSHAKE_TIMEOUT):
            await RisingEdge(self.axi_aclk)
            if int(dut.s_axil_arready.value) == 1:
                break
        else:
            raise AssertionError(
                f"AR handshake never completed (ARs accepted so far="
                f"{self.ar_accepted}, beats so far={len(self.beats)}). "
                f"The serializer is not accepting an AR it must accept.")
        self.ar_accepted += 1
        if not hold_arvalid:
            await FallingEdge(self.axi_aclk)
            dut.s_axil_arvalid.value = 0

    async def _collect_one_beat(self):
        dut = self.dut
        for _ in range(HANDSHAKE_TIMEOUT):
            await RisingEdge(self.axi_aclk)
            if int(dut.s_axil_rvalid.value) == 1:
                self.beats.append(int(dut.s_axil_rdata.value))
                return
        raise AssertionError(
            f"R beat never arrived (beats so far={len(self.beats)}, ARs "
            f"accepted={self.ar_accepted}). The 2:1 read serializer is "
            f"deadlocked: it is waiting for an AR the master already issued.")

    async def drain_strict(self, nbeats: int):
        """ARVALID and RREADY raised together; AR(n+1) strictly after R(n).
        This mirrors MonbusGroupHarness.drain_read_beat() -- the control
        case, and the only shape the pre-existing suite ever produced."""
        dut = self.dut
        for _ in range(nbeats):
            await FallingEdge(self.axi_aclk)
            dut.s_axil_arvalid.value = 1
            dut.s_axil_rready.value = 1
            for _ in range(HANDSHAKE_TIMEOUT):
                await RisingEdge(self.axi_aclk)
                if int(dut.s_axil_arready.value) == 1:
                    break
            else:
                raise AssertionError("AR handshake never completed (strict)")
            self.ar_accepted += 1
            await FallingEdge(self.axi_aclk)
            dut.s_axil_arvalid.value = 0
            await self._collect_one_beat()
            await FallingEdge(self.axi_aclk)
            dut.s_axil_rready.value = 0
            await FallingEdge(self.axi_aclk)   # turn-around

    async def drain_late_rready(self, nbeats: int):
        """Single-outstanding, but RREADY only raised after the AR handshake."""
        dut = self.dut
        for _ in range(nbeats):
            await self._accept_one_ar(hold_arvalid=False)
            await FallingEdge(self.axi_aclk)
            dut.s_axil_rready.value = 1
            await self._collect_one_beat()
            await FallingEdge(self.axi_aclk)
            dut.s_axil_rready.value = 0
            await FallingEdge(self.axi_aclk)

    async def drain_pipelined(self, nbeats: int):
        """AR(n+1) asserted as soon as AR(n) was accepted -- no wait for R.

        Legal AXI4-Lite. This is the shape that exposed the defect: the AR for
        the HIGH half of a pair arrives before the LOW half's R handshake has
        advanced the phase bit.
        """
        dut = self.dut

        async def ar_stream():
            for i in range(nbeats):
                # hold ARVALID high between ARs so they go back-to-back
                await self._accept_one_ar(hold_arvalid=(i < nbeats - 1))
            await FallingEdge(self.axi_aclk)
            dut.s_axil_arvalid.value = 0

        async def r_stream():
            await FallingEdge(self.axi_aclk)
            dut.s_axil_rready.value = 1
            for _ in range(nbeats):
                await self._collect_one_beat()
            await FallingEdge(self.axi_aclk)
            dut.s_axil_rready.value = 0

        ar_task = cocotb.start_soon(ar_stream())
        r_task = cocotb.start_soon(r_stream())
        await ar_task
        await r_task

    # ---- reassembly -------------------------------------------------------

    def reassemble_records(self, nrecords: int):
        """Fold the collected 32-bit beats back into 64-bit slices, then into
        (tag_ts, packet_hi, packet_lo) tuples -- one per record."""
        assert len(self.beats) == nrecords * BEATS_PER_RECORD_32, (
            f"expected {nrecords * BEATS_PER_RECORD_32} beats, "
            f"collected {len(self.beats)}")
        slices = []
        for i in range(0, len(self.beats), 2):
            lo = self.beats[i] & 0xFFFF_FFFF
            hi = self.beats[i + 1] & 0xFFFF_FFFF
            slices.append((hi << 32) | lo)
        return [tuple(slices[r * 3:(r * 3) + 3]) for r in range(nrecords)]


# ===========================================================================
# COCOTB TEST FUNCTION - Single test that handles all variants
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_monbus_axil_axil_group_serializer(dut):
    """32-bit err-drain serializer vs. differently-shaped legal AXIL masters."""
    test_type = os.environ.get('TEST_TYPE', 'strict')
    nrecords = int(os.environ.get('TEST_NRECORDS', '2'))

    tb = SerializerDrainTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize()

    # Build `nrecords` distinguishable ERROR packets. Packet layout per
    # docs/markdown/rtl-amba/includes/monitor_package_spec.md; the exact field
    # split does not matter here -- what matters is that every record is
    # unique so a desynchronized drain is detectable.
    records = []
    for i in range(nrecords):
        packet = (0x1 << 124) | (0xBEEF0000 + i) << 64 | (0x0123456700000000 + i)
        ts = 0x0BADF00D + i
        records.append((packet, ts))

    for packet, ts in records:
        await tb.push_record(packet, ts)

    await tb.wait_clocks(tb.clk_name, 10)

    err_count = int(dut.err_fifo_count.value)
    tb.log.info(f"err_fifo_count after {nrecords} records = {err_count}")
    assert err_count > 0, "no records landed in the err FIFO"

    nbeats = nrecords * BEATS_PER_RECORD_32

    drains = {
        'strict':      tb.drain_strict,
        'late_rready': tb.drain_late_rready,
        'pipelined':   tb.drain_pipelined,
    }
    assert test_type in drains, f"Unknown TEST_TYPE: {test_type}"

    tb.log.info(f"draining {nbeats} x 32-bit beats using the "
                f"'{test_type}' master shape")
    await drains[test_type](nbeats)

    tb.log.info(f"collected {len(tb.beats)} beats, "
                f"{tb.ar_accepted} ARs accepted")

    got = tb.reassemble_records(nrecords)

    # Slice 0 is {tag[3:0], timestamp[59:0]}; slices 1/2 are the packet halves.
    for i, (packet, ts) in enumerate(records):
        exp_ts_slice = ts & ((1 << 60) - 1)
        exp_hi = (packet >> 64) & ((1 << 64) - 1)
        exp_lo = packet & ((1 << 64) - 1)
        got_ts_slice = got[i][0] & ((1 << 60) - 1)

        tb.log.info(f"record {i}: ts=0x{got[i][0]:016x} "
                    f"hi=0x{got[i][1]:016x} lo=0x{got[i][2]:016x}")

        assert got_ts_slice == exp_ts_slice, (
            f"record {i} timestamp slice mismatch under the '{test_type}' "
            f"master: got 0x{got_ts_slice:015x}, expected 0x{exp_ts_slice:015x}. "
            f"An external AR leaked to the leaf and popped an extra 64-bit "
            f"core read, desynchronizing the drain stream.")
        assert got[i][1] == exp_hi, (
            f"record {i} packet[127:64] mismatch under the '{test_type}' "
            f"master: got 0x{got[i][1]:016x}, expected 0x{exp_hi:016x}")
        assert got[i][2] == exp_lo, (
            f"record {i} packet[63:0] mismatch under the '{test_type}' "
            f"master: got 0x{got[i][2]:016x}, expected 0x{exp_lo:016x}")

    # Exactly two external reads per 64-bit slice, no more, no fewer.
    assert tb.ar_accepted == nbeats, (
        f"expected {nbeats} external AR handshakes, saw {tb.ar_accepted}")

    tb.log.info(f"PASS: '{test_type}' master drained {nrecords} records "
                f"intact over {nbeats} 32-bit beats")


# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_serializer_test_params():
    """Generate parameters for the 32-bit drain serializer regression.

    Parameters:
        (test_type, fifo_depth_err, fifo_depth_write, addr_width,
         num_protocols, s_axil_data_width)

    S_AXIL_DATA_WIDTH is pinned at 32 -- the 2:1 serializer only exists in
    that configuration (the 64-bit drain is a straight passthrough). All
    three master shapes run against it.
    """
    base = (64, 96, 32, 3)
    return [(t,) + base + (32,)
            for t in ('strict', 'late_rready', 'pipelined')]


serializer_params = generate_serializer_test_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTION - Single wrapper for all test types
# ===========================================================================

@pytest.mark.parametrize(
    "test_type, fifo_depth_err, fifo_depth_write, addr_width, "
    "num_protocols, s_axil_data_width",
    serializer_params)
def test_monbus_axil_axil_group_serializer(request, test_type, fifo_depth_err,
                                           fifo_depth_write, addr_width,
                                           num_protocols, s_axil_data_width):
    """Pytest wrapper for the 32-bit err-drain serializer regression."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_includes': 'rtl/amba/includes',
        'rtl_shared':   'rtl/amba/shared',
        'rtl_monitor':  'rtl/amba/monitor',
        'rtl_axil4':    'rtl/amba/axil4',
        'rtl_gaxi':     'rtl/amba/gaxi',
        'rtl_common':   'rtl/common',
    })

    dut_name = "monbus_axil_axil_group"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/monbus_axil_axil_group.f")
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    fde_str = TBBase.format_dec(fifo_depth_err, 3)
    sdw_str = TBBase.format_dec(s_axil_data_width, 2)
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name_plus_params = (
        f"test_{worker_id}_{dut_name}_ser_{test_type}_"
        f"fde{fde_str}_sdw{sdw_str}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    includes = includes + [rtl_dict['rtl_common'], sim_build]

    rtl_parameters = {
        'FIFO_DEPTH_ERR':    fifo_depth_err,
        'FIFO_DEPTH_WRITE':  fifo_depth_write,
        'ADDR_WIDTH':        addr_width,
        'NUM_PROTOCOLS':     num_protocols,
        'S_AXIL_DATA_WIDTH': s_axil_data_width,
    }

    extra_env = {
        'LOG_PATH':               log_path,
        'TEST_TYPE':              test_type,
        'TEST_NRECORDS':          '2',
        'TEST_S_AXIL_DATA_WIDTH': str(s_axil_data_width),
    }

    create_view_cmd(log_dir, log_path, sim_build,
                    'test_monbus_axil_axil_group_serializer',
                    test_name_plus_params)

    compile_args = ["-Wno-TIMESCALEMOD", "-Wno-SELRANGE",
                    "-Wno-WIDTHEXPAND", "-Wno-WIDTH"]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module='test_monbus_axil_axil_group_serializer',
        testcase="cocotb_test_monbus_axil_axil_group_serializer",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        simulator="verilator",
        waves=enable_waves,
        keep_files=True,
        compile_args=compile_args,
        sim_args=[],
        plus_args=['--trace'] if enable_waves else [],
    )
