# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi_monitor_addr_check
# Purpose: Cocotb smoke test for the new address-range checker, exercised
#          through axi4_master_rd_mon (the wrapper carries the new params
#          and config inputs through to the addr_check module).
#
# The standalone addr_check module is formally verified (see
# formal/amba/axi_monitor_addr_check/). This test verifies wrapper
# integration: that with N_ADDR_RANGES=2 the parameters and config inputs
# reach the comparator, and an AR address that lands in a configured
# range produces a PktTypeError + AXI_ERR_ADDR_RANGE (8'h0D) packet on
# monbus with the correct range_index and address fields. (is_read was
# dropped from the AXI variant — implied by the IS_READ build param.)

import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ReadOnly

from TBClasses.shared.utilities import get_paths


# ============================================================================
# Packet decoder
# ============================================================================
def decode_monbus(pkt):
    """Decode a 128-bit monbus packet into a dict per the new layout.

    AXI addr_check encoding inside event_data[63:0]:
      [63:60] range_index (4 bits, 16 ranges)
      [59: 0] full cmd_addr (zero-padded if address narrower)
    The is_read flag is no longer encoded in the AXI variant — it's
    implied by the IS_READ parameter on the monitor instance.
    """
    return {
        'packet_type': (pkt >> 124) & 0xF,
        'protocol':    (pkt >> 105) & 0xF,
        'event_code':  (pkt >>  97) & 0xFF,
        'channel_id':  (pkt >>  88) & 0x1FF,
        'agent_id':    (pkt >>  72) & 0xFFFF,
        'unit_id':     (pkt >>  64) & 0xFF,
        'range_index': (pkt >>  60) & 0xF,
        'addr':         pkt         & ((1 << 60) - 1),
        'raw':          pkt,
    }


# ============================================================================
# Cocotb test
# ============================================================================
@cocotb.test(timeout_time=30, timeout_unit="ms")
async def axi_monitor_addr_check_test(dut):
    """Smoke test: drive ARs that hit/miss configured ranges, check monbus."""

    # --- Clock + reset -----------------------------------------------------
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    dut.aresetn.value = 0

    # Default all config inputs to "quiet" before reset releases.
    dut.fub_axi_arid.value     = 0
    dut.fub_axi_araddr.value   = 0
    dut.fub_axi_arlen.value    = 0
    dut.fub_axi_arsize.value   = 2
    dut.fub_axi_arburst.value  = 1
    dut.fub_axi_arlock.value   = 0
    dut.fub_axi_arcache.value  = 0
    dut.fub_axi_arprot.value   = 0
    dut.fub_axi_arqos.value    = 0
    dut.fub_axi_arregion.value = 0
    dut.fub_axi_aruser.value   = 0
    dut.fub_axi_arvalid.value  = 0
    dut.fub_axi_rready.value   = 1
    dut.m_axi_arready.value    = 1
    dut.m_axi_rid.value        = 0
    dut.m_axi_rdata.value      = 0
    dut.m_axi_rresp.value      = 0
    dut.m_axi_rlast.value      = 1
    dut.m_axi_ruser.value      = 0
    dut.m_axi_rvalid.value     = 0
    dut.monbus_ready.value     = 1

    # Standard monitor cfg — most off, so the only events we expect are
    # address-range hits (event_code=4'hD).
    dut.cfg_monitor_enable.value     = 0
    dut.cfg_error_enable.value       = 1   # enable the error path (addr_range rides here)
    dut.cfg_timeout_enable.value     = 0
    dut.cfg_perf_enable.value        = 0
    dut.cfg_timeout_cycles.value     = 0xFFFF
    dut.cfg_latency_threshold.value  = 0xFFFFFFFF
    dut.cfg_axi_pkt_mask.value       = 0
    dut.cfg_axi_err_select.value     = 0
    dut.cfg_axi_error_mask.value     = 0
    dut.cfg_axi_timeout_mask.value   = 0xFFFF
    dut.cfg_axi_compl_mask.value     = 0xFFFF
    dut.cfg_axi_thresh_mask.value    = 0xFFFF
    dut.cfg_axi_perf_mask.value      = 0xFFFF
    dut.cfg_axi_addr_mask.value      = 0
    dut.cfg_axi_debug_mask.value     = 0xFFFF

    # Free-running monitor-time broadcast (driven externally in real use;
    # tie low for this test — it's the side-band timestamp, not the packet).
    dut.i_mon_time.value             = 0

    # Address-range checker config:
    #   range 0 : [0x1000, 0x1FFF]  inclusive
    #   range 1 : [0x8000, 0x8000]  exact match
    dut.cfg_addr_check_enable.value = 1
    dut.cfg_addr_range_enable.value = 0b11
    dut.cfg_addr_range_low.value    = (0x00008000 << 32) | 0x00001000
    dut.cfg_addr_range_high.value   = (0x00008000 << 32) | 0x00001FFF

    # Hold reset for 10 cycles
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    for _ in range(5):
        await RisingEdge(dut.aclk)

    # --- Background monbus capture -----------------------------------------
    captured = []
    async def capture_monbus():
        while True:
            await RisingEdge(dut.aclk)
            await ReadOnly()
            if int(dut.monbus_valid.value) and int(dut.monbus_ready.value):
                pkt = int(dut.monbus_packet.value)
                cyc = cocotb.utils.get_sim_time(units="ns") // 10
                captured.append((cyc, decode_monbus(pkt)))
    cocotb.start_soon(capture_monbus())

    # --- AR drive helper ---------------------------------------------------
    async def drive_ar(addr, arid=0):
        # Single-beat AR. Drop arvalid in the same cycle the handshake
        # completes (write commits before next posedge). No ReadOnly phase
        # — that would block the subsequent write to arvalid.
        dut.fub_axi_araddr.value  = addr
        dut.fub_axi_arid.value    = arid
        dut.fub_axi_arlen.value   = 0
        dut.fub_axi_arvalid.value = 1
        while True:
            await RisingEdge(dut.aclk)
            if dut.fub_axi_arready.value == 1:
                break
        dut.fub_axi_arvalid.value = 0
        dut.fub_axi_araddr.value  = 0
        dut.fub_axi_arid.value    = 0
        # Idle a few cycles so the monitor has time to drive monbus
        for _ in range(8):
            await RisingEdge(dut.aclk)

    # --- R driver: respond to every AR with a single-beat R ----------------
    async def respond_r():
        while True:
            await RisingEdge(dut.aclk)
            await ReadOnly()
            if int(dut.m_axi_arvalid.value) and int(dut.m_axi_arready.value):
                arid = int(dut.m_axi_arid.value)
                await RisingEdge(dut.aclk)
                dut.m_axi_rid.value    = arid
                dut.m_axi_rdata.value  = 0xDEADBEEF
                dut.m_axi_rresp.value  = 0
                dut.m_axi_rlast.value  = 1
                dut.m_axi_rvalid.value = 1
                while True:
                    await RisingEdge(dut.aclk)
                    await ReadOnly()
                    if int(dut.m_axi_rready.value):
                        break
                await RisingEdge(dut.aclk)
                dut.m_axi_rvalid.value = 0
                dut.m_axi_rlast.value  = 0
    cocotb.start_soon(respond_r())

    # --- Drive test vectors ------------------------------------------------
    # Sequence:
    #   1) addr=0x500  → no range hit, no monbus packet expected
    #   2) addr=0x1200 → hits range 0, expect packet (range_index=0, addr=0x1200)
    #   3) addr=0x8000 → hits range 1 (exact), expect packet (range_index=1)
    #   4) addr=0x8001 → just outside range 1, no packet
    await drive_ar(0x00000500, arid=1)
    await drive_ar(0x00001200, arid=2)
    await drive_ar(0x00008000, arid=3)
    await drive_ar(0x00008001, arid=4)

    # Idle long enough for any in-flight monbus packet to drain
    for _ in range(20):
        await RisingEdge(dut.aclk)

    # --- Verify ------------------------------------------------------------
    # Filter to addr-range packets only (event_code is now 8 bits: 0x0D)
    range_pkts = [
        (cyc, p) for (cyc, p) in captured
        if p['packet_type'] == 0 and p['event_code'] == 0x0D
    ]

    dut._log.info(f"Captured {len(captured)} monbus packets total")
    for cyc, p in captured:
        dut._log.info(f"  cyc={cyc} pkt_type={p['packet_type']:#x} "
                      f"evcode={p['event_code']:#04x} range={p['range_index']} "
                      f"addr={p['addr']:#010x}")

    assert len(range_pkts) == 2, (
        f"Expected exactly 2 ADDR_RANGE packets, got {len(range_pkts)}. "
        f"All packets: {captured}"
    )

    # First range hit: address 0x1200, range 0
    cyc0, pkt0 = range_pkts[0]
    assert pkt0['protocol']    == 0,         f"protocol expected AXI(0), got {pkt0['protocol']}"
    assert pkt0['event_code']  == 0x0D,      f"event_code expected ADDR_RANGE(0x0D), got {pkt0['event_code']:#04x}"
    assert pkt0['range_index'] == 0,         f"range_index expected 0, got {pkt0['range_index']}"
    assert pkt0['addr']        == 0x1200,    f"addr expected 0x1200, got {pkt0['addr']:#x}"

    # Second range hit: address 0x8000, range 1
    cyc1, pkt1 = range_pkts[1]
    assert pkt1['range_index'] == 1,         f"range_index expected 1, got {pkt1['range_index']}"
    assert pkt1['addr']        == 0x8000,    f"addr expected 0x8000, got {pkt1['addr']:#x}"

    dut._log.info(f"PASS: 2 ADDR_RANGE packets at cycles {cyc0} and {cyc1}")


# ============================================================================
# PyTest runner
# ============================================================================
def test_axi_monitor_addr_check():
    """Smoke test for the new address-range checker."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi4':         'rtl/amba/axi4/',
        'rtl_gaxi':         'rtl/amba/gaxi',
        'rtl_includes':     'rtl/amba/includes',
        'rtl_common':       'rtl/common',
        'rtl_shared':       'rtl/amba/shared',
        'rtl_amba_includes':'rtl/amba/includes',
    })

    dut_name  = "axi4_master_rd_mon"
    test_name = f"test_axi_monitor_addr_check_{worker_id}"

    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources = [
        os.path.join(rtl_dict['rtl_includes'], "monitor_common_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_amba4_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_amba5_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_arbiter_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_pkg.sv"),
        os.path.join(rtl_dict['rtl_common'],   "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_common'],   "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_common'],   "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_common'],   "counter_freq_invariant.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],     "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],     "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axi4'],     "axi4_master_rd.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_trans_mgr.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_timer.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_timeout.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_reporter.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_addr_check.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_base.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_filtered.sv"),
        os.path.join(rtl_dict['rtl_axi4'],     f"{dut_name}.sv"),
    ]
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    rtl_parameters = {
        'AXI_ID_WIDTH':    '8',
        'AXI_ADDR_WIDTH':  '32',
        'AXI_DATA_WIDTH':  '32',
        'AXI_USER_WIDTH':  '1',
        'UNIT_ID':         '1',
        'AGENT_ID':        '10',
        'MAX_TRANSACTIONS':'16',
        'ENABLE_FILTERING':'1',
        'SKID_DEPTH_AR':   '2',
        'SKID_DEPTH_R':    '4',
        'N_ADDR_RANGES':   '2',
    }

    extra_env = {
        'DUT':              dut_name,
        'LOG_PATH':         log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_CLK_PERIOD':  '10',
        'SEED':             str(random.randint(0, 100000)),
    }

    compile_args = [
        "--trace-fst", "--trace-structs",
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED", "-Wno-DECLFILENAME",
        "-Wno-PINMISSING", "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE",
        "-Wno-TIMESCALEMOD",
    ]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=[rtl_dict['rtl_includes'], rtl_dict['rtl_common'], sim_build],
        toplevel=dut_name,
        module="test_axi_monitor_addr_check",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=enable_waves,
        keep_files=True,
        compile_args=compile_args,
    )
