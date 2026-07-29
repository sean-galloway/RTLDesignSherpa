# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi_monitor_addr_check
# Purpose: Cocotb smoke test for the address-range ALLOWLIST checker, exercised
#          through axi4_master_rd_mon (the wrapper carries the new params
#          and config inputs through to the addr_check module).
#
# Allowlist semantics: the N configured ranges are the EXPECTED addresses.
#   - MATCH (addr in >=1 range), gated by cfg_debug_enable:
#         PktTypeAddrMatch (4'h8) + AXI_ADDR_RANGE_MATCH (8'h01), range_index set
#   - MISS  (addr in NO range), gated by cfg_error_enable:
#         PktTypeError     (4'h0) + AXI_ERR_ADDR_RANGE   (8'h0D), range_index=0xF
#
# The standalone addr_check module is formally verified (see
# formal/amba/axi_monitor_addr_check/). This test verifies wrapper
# integration: that with N_ADDR_RANGES=2 the parameters and config inputs
# reach the comparator, and that hitting/missing the configured ranges
# produces the right packet class on monbus. (is_read was dropped from the
# AXI variant — implied by the IS_READ build param.)

import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ReadOnly

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist


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
    # Header fields decode via the house chokepoint (TBClasses.monbus.parse):
    # one field-layout source of truth + feeds MONBUS_COVERAGE. The
    # event_data sub-field splits below are test-specific and stay local.
    from TBClasses.monbus import parse as _monbus_parse
    _mp = _monbus_parse(pkt)
    return {
        'packet_type': int(_mp.packet_type),
        'protocol': int(_mp.protocol),
        'event_code': int(_mp.event_code),
        'channel_id': int(_mp.channel_id),
        'agent_id': int(_mp.agent_id),
        'unit_id': int(_mp.unit_id),
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
    #
    # cfg_monitor_enable MUST be 1: since the E5 wrapper rewiring it is the
    # real master runtime gate (0 = monitor fully inert, including the
    # address-range checker, whose cmd_valid feed is gated off). This test
    # historically tied it 0 only because the port used to be connected to
    # nothing.
    dut.cfg_monitor_enable.value     = 1
    dut.cfg_error_enable.value       = 1   # MISS path: no-range-match -> PktTypeError/0x0D
    dut.cfg_debug_enable.value       = 1   # MATCH path: range hit -> PktTypeAddrMatch(8)/0x01
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

    # Address-range checker config — two flavors (ADDR_RANGE_IS_ERROR=2'b10):
    #   range 0 : [0x1000, 0x1FFF]  DEBUG -> a hit emits an AddrMatch packet
    #   range 1 : [0x1000, 0x1FFF]  ERROR -> allowlist; an address in NO enabled
    #             error range emits an Error/ADDR_RANGE packet
    # Same window on both flavors: addresses inside are watched (debug) AND
    # allowed (error); addresses outside raise an error.
    dut.cfg_addr_check_enable.value = 1
    dut.cfg_addr_range_enable.value = 0b11
    dut.cfg_addr_range_low.value    = (0x00001000 << 32) | 0x00001000
    dut.cfg_addr_range_high.value   = (0x00001FFF << 32) | 0x00001FFF

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
    # DEBUG=[0x1000,0x1FFF] (range0), ERROR allowlist=[0x1000,0x1FFF] (range1).
    #   1) addr=0x500  → outside debug + outside error allowlist → MISS (Error/0x0D)
    #   2) addr=0x1200 → in debug (MATCH) + inside error allowlist (allowed) → AddrMatch, r0
    #   3) addr=0x1FFF → in debug (MATCH) + inside error allowlist (allowed) → AddrMatch, r0
    #   4) addr=0x2000 → outside debug + outside error allowlist → MISS (Error/0x0D)
    await drive_ar(0x00000500, arid=1)
    await drive_ar(0x00001200, arid=2)
    await drive_ar(0x00001FFF, arid=3)
    await drive_ar(0x00002000, arid=4)

    # Idle long enough for any in-flight monbus packet to drain
    for _ in range(20):
        await RisingEdge(dut.aclk)

    dut._log.info(f"Captured {len(captured)} monbus packets total")
    for cyc, p in captured:
        dut._log.info(f"  cyc={cyc} pkt_type={p['packet_type']:#x} "
                      f"evcode={p['event_code']:#04x} range={p['range_index']} "
                      f"addr={p['addr']:#010x}")

    # MATCH packets: PktTypeAddrMatch (8) + AXI_ADDR_RANGE_MATCH (0x01)
    match_pkts = [
        (cyc, p) for (cyc, p) in captured
        if p['packet_type'] == 0x8 and p['event_code'] == 0x01
    ]
    # MISS packets: PktTypeError (0) + AXI_ERR_ADDR_RANGE (0x0D)
    miss_pkts = [
        (cyc, p) for (cyc, p) in captured
        if p['packet_type'] == 0x0 and p['event_code'] == 0x0D
    ]

    assert len(match_pkts) == 2, (
        f"Expected exactly 2 ADDR_MATCH packets, got {len(match_pkts)}. "
        f"All packets: {captured}"
    )
    assert len(miss_pkts) == 2, (
        f"Expected exactly 2 ADDR_RANGE (miss) error packets, got {len(miss_pkts)}. "
        f"All packets: {captured}"
    )

    # First match: address 0x1200, DEBUG range 0
    _, m0 = match_pkts[0]
    assert m0['protocol']    == 0,      f"protocol expected AXI(0), got {m0['protocol']}"
    assert m0['range_index'] == 0,      f"range_index expected 0 (debug range), got {m0['range_index']}"
    assert m0['addr']        == 0x1200, f"addr expected 0x1200, got {m0['addr']:#x}"

    # Second match: address 0x1FFF, DEBUG range 0 (error-flavored range never matches)
    _, m1 = match_pkts[1]
    assert m1['range_index'] == 0,      f"range_index expected 0 (debug range), got {m1['range_index']}"
    assert m1['addr']        == 0x1FFF, f"addr expected 0x1FFF, got {m1['addr']:#x}"

    # Misses carry the no-range sentinel 0xF and the offending address.
    _, ms0 = miss_pkts[0]
    assert ms0['range_index'] == 0xF,   f"miss range_index expected 0xF sentinel, got {ms0['range_index']:#x}"
    assert ms0['addr']        == 0x500, f"first miss addr expected 0x500, got {ms0['addr']:#x}"

    dut._log.info(f"PASS: 2 ADDR_MATCH + 2 MISS-error packets "
                  f"(match cycles {match_pkts[0][0]},{match_pkts[1][0]}; "
                  f"miss cycles {miss_pkts[0][0]},{miss_pkts[1][0]})")


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
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_amba_includes':'rtl/amba/includes',
    })

    dut_name  = "axi4_master_rd_mon"
    test_name = f"test_{worker_id}_axi_monitor_addr_check"

    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi4_master_rd_mon.f")
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
        'ADDR_RANGE_IS_ERROR': '2',   # 2'b10: range1 = ERROR/allowlist, range0 = DEBUG/match
    }

    extra_env = {
        'DUT':              dut_name,
        'LOG_PATH':         log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_CLK_PERIOD':  '10',
        'SEED':             os.environ.get('SEED', str(random.randint(0, 100000))),
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
        includes=includes + [rtl_dict['rtl_common'], sim_build],
        toplevel=dut_name,
        module="test_axi_monitor_addr_check",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=enable_waves,
        keep_files=True,
        compile_args=compile_args,
    )
