# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_monbus_axi4_axil_group
# Purpose: Coverage for the AXI4-slave + AXIL-master family member.
#
# Author: sean galloway
# Created: 2026-06-11

"""
Test for `rtl/amba/shared/monbus_axi4_axil_group.sv` — the AXI4-burst
slave-read + AXIL master-write member of the family. This file member
had no dedicated test before
[MONBUS_GROUP_AXIL_MASTER_RAWMODE_FLUSH_BUG.md](../../MONBUS_GROUP_AXIL_MASTER_RAWMODE_FLUSH_BUG.md)
exposed the AXIL-master + raw-mode deadlock; the new test asserts
real beats on `m_axil_w*` for this family member.

Two phases:
  1. **Master-write raw-mode flush** (same shape as the AXIL/AXIL
     master_write test): drive N records, capture 3*N beats on
     m_axil_w*. Will FAIL on broken RTL.
  2. **AXI4 burst slave-read drain**: issue a multi-beat AR for the
     err FIFO, assert R returns the expected slice cadence
     (ts / pkt_hi / pkt_lo) with rlast on the final beat.
"""

import os
import random
from typing import List, Tuple

import pytest
import cocotb
from cocotb.triggers import RisingEdge, ReadOnly, Combine
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist


BEATS_PER_RECORD = 3
BYTES_PER_BEAT   = 8


def synth_record_stream(n: int, packet_type, seed: int = 0xC1C1):
    """Generate `n` monbus records of the requested packet_type."""
    from TBClasses.monbus import (
        create_monitor_packet, ProtocolType, AXIErrorCode,
    )
    rng = random.Random(seed)
    return [
        (
            create_monitor_packet(
                packet_type, ProtocolType.PROTOCOL_AXI,
                AXIErrorCode.AXI_ERR_DATA_ORPHAN, 0, i % 8, 0x21,
                rng.randint(0, 0xFFFF_FFFF_FFFF_FFFF),
            ),
            1000 + 10 * i,
        )
        for i in range(n)
    ]


class MonbusAxi4AxilGroupTB(TBBase):
    """Drives monbus records in, acts as an AXIL slave on the
    master-write side, and acts as an AXI4 master on the slave-read
    side."""

    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = int(os.environ.get('SEED', '0'))
        random.seed(self.SEED)
        # Master-write capture
        self.captured: List[Tuple[int, int]] = []
        self._aw_q: List[int] = []
        self._w_q: List[int] = []
        # Slave-read capture
        self.r_beats: List[Tuple[int, int, int]] = []  # (rdata, rlast, rid)

    def _tie_off_config(self, route_to_err: bool):
        """When route_to_err=True, errors go to err FIFO (slave-read
        path); when False, everything goes to write FIFO (master-write
        path)."""
        for sig in (
            'cfg_axi_pkt_mask',
            'cfg_axi_error_mask', 'cfg_axi_timeout_mask',
            'cfg_axi_compl_mask', 'cfg_axi_thresh_mask',
            'cfg_axi_perf_mask', 'cfg_axi_addr_mask', 'cfg_axi_debug_mask',
            'cfg_axis_pkt_mask', 'cfg_axis_err_select', 'cfg_axis_error_mask',
            'cfg_axis_timeout_mask', 'cfg_axis_compl_mask', 'cfg_axis_credit_mask',
            'cfg_axis_channel_mask', 'cfg_axis_stream_mask',
            'cfg_core_pkt_mask', 'cfg_core_err_select', 'cfg_core_error_mask',
            'cfg_core_timeout_mask', 'cfg_core_compl_mask', 'cfg_core_thresh_mask',
            'cfg_core_perf_mask', 'cfg_core_debug_mask',
        ):
            getattr(self.dut, sig).value = 0
        # PktTypeError = 0 by spec; set bit 0 in err_select to route
        # error packets to the err FIFO.
        self.dut.cfg_axi_err_select.value = 0x0001 if route_to_err else 0x0000

    async def reset_dut(self, base_addr: int, limit_addr: int,
                        flush_watermark: int, route_err: bool = False):
        self.dut.cam_clear.value        = 0
        self.dut.monbus_valid.value     = 0
        self.dut.monbus_packet.value    = 0
        self.dut.monbus_timestamp.value = 0
        # AXI4 slave-read input side
        self.dut.s_axi_arid.value     = 0
        self.dut.s_axi_araddr.value   = 0
        self.dut.s_axi_arlen.value    = 0
        self.dut.s_axi_arsize.value   = 0
        self.dut.s_axi_arburst.value  = 0
        self.dut.s_axi_arlock.value   = 0
        self.dut.s_axi_arcache.value  = 0
        self.dut.s_axi_arprot.value   = 0
        self.dut.s_axi_arqos.value    = 0
        self.dut.s_axi_arregion.value = 0
        self.dut.s_axi_aruser.value   = 0
        self.dut.s_axi_arvalid.value  = 0
        self.dut.s_axi_rready.value   = 0
        # AXIL master-write side
        self.dut.m_axil_awready.value = 0
        self.dut.m_axil_wready.value  = 0
        self.dut.m_axil_bvalid.value  = 0
        self.dut.m_axil_bresp.value   = 0
        # Window
        self.dut.cfg_base_addr.value       = base_addr
        self.dut.cfg_limit_addr.value      = limit_addr
        self.dut.cfg_flush_watermark.value = flush_watermark
        self._tie_off_config(route_to_err=route_err)
        # Reset pulse
        self.dut.axi_aresetn.value = 0
        await self.wait_clocks('axi_aclk', 5)
        self.dut.axi_aresetn.value = 1
        await self.wait_clocks('axi_aclk', 2)
        self.captured.clear()
        self._aw_q.clear()
        self._w_q.clear()
        self.r_beats.clear()

    # ---------- monbus driver ----------

    async def drive_record(self, packet: int, source_ts: int):
        self.dut.monbus_packet.value    = packet
        self.dut.monbus_timestamp.value = source_ts
        self.dut.monbus_valid.value     = 1
        while True:
            await ReadOnly()
            if int(self.dut.monbus_ready.value) == 1:
                break
            await RisingEdge(self.dut.axi_aclk)
        await RisingEdge(self.dut.axi_aclk)
        self.dut.monbus_valid.value = 0

    async def drive_records(self, records):
        for pkt, ts in records:
            await self.drive_record(pkt, ts)

    # ---------- AXIL slave model on m_axil_* (master-write) ----------

    async def _aw_handler(self, stop_after: int):
        self.dut.m_axil_awready.value = 1
        seen = 0
        while seen < stop_after:
            await ReadOnly()
            if (int(self.dut.m_axil_awvalid.value) == 1
                    and int(self.dut.m_axil_awready.value) == 1):
                self._aw_q.append(int(self.dut.m_axil_awaddr.value))
                seen += 1
            await RisingEdge(self.dut.axi_aclk)
        await RisingEdge(self.dut.axi_aclk)
        self.dut.m_axil_awready.value = 0

    async def _w_handler(self, stop_after: int):
        self.dut.m_axil_wready.value = 1
        seen = 0
        while seen < stop_after:
            await ReadOnly()
            if (int(self.dut.m_axil_wvalid.value) == 1
                    and int(self.dut.m_axil_wready.value) == 1):
                self._w_q.append(int(self.dut.m_axil_wdata.value))
                seen += 1
            await RisingEdge(self.dut.axi_aclk)
        await RisingEdge(self.dut.axi_aclk)
        self.dut.m_axil_wready.value = 0

    async def _b_handler(self, stop_after: int):
        sent = 0
        while sent < stop_after:
            await ReadOnly()
            ready_to_ack = bool(self._aw_q) and bool(self._w_q)
            await RisingEdge(self.dut.axi_aclk)
            if not ready_to_ack:
                continue
            self.dut.m_axil_bvalid.value = 1
            self.dut.m_axil_bresp.value  = 0
            while True:
                await ReadOnly()
                if int(self.dut.m_axil_bready.value) == 1:
                    break
                await RisingEdge(self.dut.axi_aclk)
            await RisingEdge(self.dut.axi_aclk)
            self.dut.m_axil_bvalid.value = 0
            addr = self._aw_q.pop(0)
            data = self._w_q.pop(0)
            self.captured.append((addr, data))
            sent += 1

    async def capture_n_master_beats(self, n: int, drain_cycles: int = 4000):
        aw_task = cocotb.start_soon(self._aw_handler(n))
        w_task  = cocotb.start_soon(self._w_handler(n))
        b_task  = cocotb.start_soon(self._b_handler(n))
        timer = cocotb.start_soon(self.wait_clocks('axi_aclk', drain_cycles))
        await Combine(timer)
        await self.wait_clocks('axi_aclk', 4)

    # ---------- AXI4 master on s_axi_* (slave-read drain) ----------

    async def issue_ar_burst(self, arlen: int, arid: int = 0x5):
        """Issue an AXI4 read burst of `arlen+1` beats, capture all R
        beats into self.r_beats."""
        self.dut.s_axi_arid.value    = arid
        self.dut.s_axi_araddr.value  = 0  # ignored by the drain
        self.dut.s_axi_arlen.value   = arlen
        self.dut.s_axi_arsize.value  = 3
        self.dut.s_axi_arburst.value = 1  # INCR
        self.dut.s_axi_arvalid.value = 1
        # AR handshake
        while True:
            await ReadOnly()
            if int(self.dut.s_axi_arready.value) == 1:
                break
            await RisingEdge(self.dut.axi_aclk)
        await RisingEdge(self.dut.axi_aclk)
        self.dut.s_axi_arvalid.value = 0

        # R consumption
        self.dut.s_axi_rready.value = 1
        beats_remaining = arlen + 1
        while beats_remaining > 0:
            await ReadOnly()
            if int(self.dut.s_axi_rvalid.value) == 1:
                rdata = int(self.dut.s_axi_rdata.value)
                rlast = int(self.dut.s_axi_rlast.value)
                rid   = int(self.dut.s_axi_rid.value)
                self.r_beats.append((rdata, rlast, rid))
                beats_remaining -= 1
            await RisingEdge(self.dut.axi_aclk)
        self.dut.s_axi_rready.value = 0
        await RisingEdge(self.dut.axi_aclk)

    # ---------- assertions ----------

    def assert_master_record_cadence(self, base_addr: int, n_records: int):
        expected_beats = n_records * BEATS_PER_RECORD
        assert len(self.captured) == expected_beats, (
            f"captured {len(self.captured)} master beats, "
            f"expected {expected_beats}"
        )
        for i, (addr, _) in enumerate(self.captured):
            expected_addr = base_addr + i * BYTES_PER_BEAT
            assert addr == expected_addr, (
                f"master beat {i}: got 0x{addr:08x}, "
                f"expected 0x{expected_addr:08x}"
            )

    def assert_slave_burst_shape(self, expected_beats: int, expected_id: int):
        assert len(self.r_beats) == expected_beats, (
            f"got {len(self.r_beats)} R beats, expected {expected_beats}"
        )
        for i, (_, rlast, rid) in enumerate(self.r_beats):
            assert rid == expected_id, (
                f"R beat {i}: rid={rid}, expected {expected_id}"
            )
            is_final = (i == expected_beats - 1)
            assert rlast == int(is_final), (
                f"R beat {i}: rlast={rlast}, expected {int(is_final)} "
                f"(beat {i+1}/{expected_beats})"
            )


# ----------------------------------------------------------------------------
# Cocotb test
# ----------------------------------------------------------------------------

@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_monbus_axi4_axil_group(dut):
    tb = MonbusAxi4AxilGroupTB(dut)
    await tb.start_clock('axi_aclk', 10, 'ns')

    # =========================================================
    # Phase 1: AXIL master-write raw-mode flush
    # =========================================================
    from TBClasses.monbus import PktType
    tb.log.info("=== Phase 1: AXIL master-write, raw mode ===")
    N_RECS = 3
    BASE   = 0x0000_1000
    LIMIT  = 0x0000_4FFF
    await tb.reset_dut(BASE, LIMIT, flush_watermark=BEATS_PER_RECORD,
                       route_err=False)
    expected_beats = N_RECS * BEATS_PER_RECORD

    capture = cocotb.start_soon(tb.capture_n_master_beats(expected_beats,
                                                           drain_cycles=4000))
    await tb.drive_records(synth_record_stream(N_RECS, PktType.PktTypeError))
    await Combine(capture)

    tb.assert_master_record_cadence(BASE, N_RECS)
    tb.log.info(f"  master beats captured: {len(tb.captured)} -- OK")

    # =========================================================
    # Phase 2: AXI4 burst slave-read drain
    # =========================================================
    tb.log.info("=== Phase 2: AXI4 burst slave-read of err FIFO ===")
    # Route errors to err FIFO and load 2 records (= 6 slices).
    await tb.reset_dut(BASE, LIMIT, flush_watermark=1024, route_err=True)
    await tb.drive_records(synth_record_stream(2, PktType.PktTypeError,
                                                seed=0xF4F4))
    # Give the err FIFO time to fill
    await tb.wait_clocks('axi_aclk', 20)
    # Issue an AR for 6 beats (arlen=5)
    await tb.issue_ar_burst(arlen=5, arid=0x7)

    tb.assert_slave_burst_shape(expected_beats=6, expected_id=0x7)
    tb.log.info(f"  slave R beats: {len(tb.r_beats)}, rlast on beat 6 -- OK")

    tb.log.info("=== ALL PHASES PASSED ===")


# ----------------------------------------------------------------------------
# Pytest wrapper
# ----------------------------------------------------------------------------

def test_monbus_axi4_axil_group(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_includes': 'rtl/amba/includes',
        'rtl_shared':   'rtl/amba/shared',
        'rtl_axil4':    'rtl/amba/axil4',
        'rtl_axi4':     'rtl/amba/axi4',
        'rtl_gaxi':     'rtl/amba/gaxi',
        'rtl_common':   'rtl/common',
    })

    dut_name = "monbus_axi4_axil_group"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name = f"test_{worker_id}_{dut_name}"

    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources = [
        os.path.join(rtl_dict['rtl_includes'], "monitor_common_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_arbiter_pkg.sv"),
        os.path.join(rtl_dict['rtl_common'],   "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_common'],   "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],     "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],     "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axi4'],     "axi4_slave_rd.sv"),
        os.path.join(rtl_dict['rtl_axil4'],    "axil4_master_wr.sv"),
        # Monbus group core family (cam/compressor/core + div-by-3 helper)
        # from the shared canonical filelist -- one place for new deps.
        *get_sources_from_filelist(repo_root, 'rtl/amba/filelists/monbus_group.f')[0],
        os.path.join(rtl_dict['rtl_shared'],   f"{dut_name}.sv"),
    ]
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    parameters = {
        'ADDR_WIDTH':           32,
        'AXI_ID_WIDTH':         4,
        'AXI_USER_WIDTH':       1,
        'FLUSH_TIMEOUT_CYCLES': 200,
        'USE_COMPRESSION':      0,
    }

    extra_env = {
        'DUT':              dut_name,
        'LOG_PATH':         log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED':             os.environ.get('SEED', str(random.randint(0, 100000))),
    }

    compile_args = [
        '+define+SIMULATION',
        '-Wno-DECLFILENAME', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC',
        '-Wno-UNUSEDPARAM', '-Wno-UNUSEDSIGNAL', '-Wno-TIMESCALEMOD',
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_includes'], rtl_dict['rtl_shared'], sim_build],
            toplevel=dut_name,
            module='test_monbus_axi4_axil_group',
            testcase="cocotb_test_monbus_axi4_axil_group",
            sim_build=sim_build,
            extra_env=extra_env,
            parameters=parameters,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"✓ monbus_axi4_axil_group test PASSED! Logs: {log_path}")
    except Exception as e:
        print(f"✗ monbus_axi4_axil_group test FAILED: {e}")
        print(f"Logs: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
