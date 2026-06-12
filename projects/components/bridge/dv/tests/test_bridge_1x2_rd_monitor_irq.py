#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# IRQ + s_mon_axil drain exercise for the monitored bridge.
#
# Sister test to test_bridge_1x2_rd_monitor_capture.py. That test
# proved the bulk-trace m_mon_axil_* write path; this one proves the
# IRQ + CPU-readable err_fifo drain path on the slave AXIL.
#
# Instantiates bridge_1x2_rd_mon_smoke with
#     MONITOR_ENABLE=1               (per-port monitors fire)
#     ROUTE_COMPL_TO_ERR_FIFO=1      (PktTypeCompletion -> err FIFO -> IRQ)
#
# Drives a small number of clean reads. Each transaction produces a
# completion packet at each wrapper boundary; with the routing above
# those completions land in the err FIFO instead of the bulk-trace
# path, and the first one drives mon_irq_out high.
#
# Then the test issues 3 × 64-bit AXIL reads at s_mon_axil_*. The
# bridge's monbus_axil_group runs them through its slice-counter
# read path (the path I rewrote in cff739f2):
#   slice 0: packet[63:0]
#   slice 1: packet[127:64]
#   slice 2: source_ts[63:0]
# The FIFO entry advances only after the 3rd beat. We reassemble the
# three beats via the dump_monbus library functions and parse via the
# standalone TBClasses.monbus.parse, then assert the decoded packet
# is a completion and mon_irq_out was high.
#
# Honest scope: this exercises the IRQ + drain plumbing using
# completions (the most reliably-produced packet type). It does NOT
# exercise "real error -> IRQ" semantics; that requires either
# generator support for cfg_addr_range_* (so a read out of range
# fires AXI_ERR_ADDR_RANGE) or a slave-side SLVERR-injection knob.

import os
import sys
from pathlib import Path

import pytest

from TBClasses.shared.utilities import get_repo_root

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge, FallingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from projects.components.bridge.dv.tbclasses.bridge1x2_rd_tb import Bridge1x2RdTB

# Standalone parser library (host-side AND sim-side).
from TBClasses.monbus import (
    parse,
    PktType,
    ProtocolType,
)


# ============================================================================
# Helpers
# ============================================================================

async def axil_read32(dut, addr: int, timeout_cycles: int = 200) -> int:
    """Issue one 32-bit AXIL read on the bridge's s_mon_axil_* port and
    return the read data. Drives arvalid, waits for arready, then waits
    for rvalid and captures rdata.

    NB: even though s_mon_axil_rdata is 64-bit at the bridge top (after
    the S_AXIL_DATA_WIDTH bump), this helper returns the whole 64-bit
    word -- the slice-counter design means one AXIL read = one beat =
    one slice of the 192-bit err_fifo record, so the 'one read returns
    64 bits' contract is intentional here even though the AXIL pin is
    nominally a 32-bit-data port from a typical SoC perspective. The
    bridge's monbus_axil_group has S_AXIL_DATA_WIDTH=64 at this layer."""
    clk = dut.aclk
    dut.s_mon_axil_arvalid.value = 1
    dut.s_mon_axil_araddr.value = addr
    dut.s_mon_axil_arprot.value = 0
    dut.s_mon_axil_rready.value = 1
    # Wait for ar handshake
    for _ in range(timeout_cycles):
        await RisingEdge(clk)
        if int(dut.s_mon_axil_arready.value) == 1:
            break
    else:
        raise TimeoutError(
            f"s_mon_axil ar handshake timeout (addr=0x{addr:08x})"
        )
    dut.s_mon_axil_arvalid.value = 0
    # Wait for r handshake (may be same cycle)
    for _ in range(timeout_cycles):
        if int(dut.s_mon_axil_rvalid.value) == 1:
            rdata = int(dut.s_mon_axil_rdata.value) & ((1 << 64) - 1)
            break
        await RisingEdge(clk)
    else:
        raise TimeoutError(
            f"s_mon_axil r handshake timeout (addr=0x{addr:08x})"
        )
    # Hold rready high through one more clock so the handshake completes
    await RisingEdge(clk)
    dut.s_mon_axil_rready.value = 0
    return rdata


# ============================================================================
# CocoTB test
# ============================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_1x2_rd_mon_irq(dut):
    """Enable monitor + route completions to err FIFO, drive reads,
    confirm mon_irq_out asserts, drain via s_mon_axil_*, parse, assert
    a completion packet was retrieved."""

    tb = Bridge1x2RdTB(dut)
    await tb.setup_clocks_and_reset()
    tb.log.info("=" * 80)
    tb.log.info("Monitored bridge IRQ test (MONITOR_ENABLE=1, "
                "ROUTE_COMPL_TO_ERR_FIFO=1)")
    tb.log.info("=" * 80)

    # ---- Background: latch mon_irq_out's first rising edge --------
    irq_asserted = {'cycle': None}

    async def watch_irq():
        clk = dut.aclk
        prev = 0
        cyc = 0
        while True:
            await RisingEdge(clk)
            cyc += 1
            try:
                cur = int(dut.mon_irq_out.value)
            except (ValueError, AttributeError):
                continue
            if cur == 1 and prev == 0 and irq_asserted['cycle'] is None:
                irq_asserted['cycle'] = cyc
                tb.log.info(f"  mon_irq_out asserted at cycle {cyc}")
            prev = cur

    irq_task = cocotb.start_soon(watch_irq())

    # ---- DIAGNOSTICS: confirm cfg routing landed correctly ---------
    tb.log.info(f"  cfg_mon_group_axi_err_select = "
                f"0x{int(dut.u_dut.u_mon_axil_group.cfg_axi_err_select.value):04x}")
    tb.log.info(f"  cfg_mon_group_axi_pkt_mask   = "
                f"0x{int(dut.u_dut.u_mon_axil_group.cfg_axi_pkt_mask.value):04x}")

    # ---- Drive a few clean reads ------------------------------------
    # With ROUTE_COMPL_TO_ERR_FIFO=1 every completion lands in the
    # err FIFO; the first one drives mon_irq_out high.
    for slave_idx, addr in ((0, 0x00000100), (1, 0x80000100)):
        expected = tb.slave_mem_read(slave_idx, addr, master_idx=0)
        actual = await tb.master_read(0, addr)
        assert actual == expected, (
            f"Read mismatch master 0 -> slave {slave_idx} at 0x{addr:08x}: "
            f"got 0x{actual:08x}, expected 0x{expected:08x}"
        )
    await ClockCycles(tb.clock, 200)

    # ---- More diagnostics: did anything land in err_fifo? -----------
    err_count = int(dut.u_dut.u_mon_axil_group.err_fifo_count.value)
    wr_count = int(dut.u_dut.u_mon_axil_group.write_fifo_count.value)
    # The monbus_<p1>_<p2>_group family exposes err_fifo_count (no
    # standalone err_fifo_empty port like the legacy monbus_axil_group);
    # derive emptiness from the count.
    err_empty = int(err_count == 0)
    irq = int(dut.mon_irq_out.value)
    tb.log.info(f"  err_fifo_count = {err_count}, empty = {err_empty}")
    tb.log.info(f"  write_fifo_count = {wr_count}")
    tb.log.info(f"  mon_irq_out = {irq}")

    irq_task.kill()

    # ---- Assert IRQ went high --------------------------------------
    assert irq_asserted['cycle'] is not None, (
        "mon_irq_out never asserted -- completions were not routed to "
        "the err FIFO. Check ROUTE_COMPL_TO_ERR_FIFO parameter and the "
        "cfg_mon_group_axi_err_select wiring in the wrapper."
    )
    tb.log.info(f"PASS: mon_irq_out asserted at cycle {irq_asserted['cycle']}")

    # ---- Drain one packet via the s_mon_axil_* slice-counter path --
    # Three 64-bit reads at any offset; the bridge's monbus_axil_group
    # advances its internal r_slice_idx on each successful read and
    # pops the FIFO entry on the third beat. Read at addresses
    # 0x00 / 0x08 / 0x10 -- conventional offsets that match what a
    # CPU IRQ handler would naturally use.
    tb.log.info("Draining one err_fifo entry via s_mon_axil_* ...")
    beats = []
    for offset in (0x00, 0x08, 0x10):
        beat = await axil_read32(dut, offset)
        tb.log.info(f"  beat @0x{offset:02x}: 0x{beat:016x}")
        beats.append(beat)

    # Reassemble (matches dump_monbus.beats_to_packet ordering):
    #   beats[0] = packet[63:0]
    #   beats[1] = packet[127:64]
    #   beats[2] = source_ts[63:0]
    raw_pkt = ((beats[1] & ((1 << 64) - 1)) << 64) | (beats[0] & ((1 << 64) - 1))
    source_ts = beats[2] & ((1 << 64) - 1)
    pkt = parse(raw_pkt)
    tb.log.info(f"Decoded: {pkt}  (source_ts=0x{source_ts:016x})")

    # ---- Assert decoded content ------------------------------------
    assert pkt.protocol == ProtocolType.PROTOCOL_AXI, pkt
    assert pkt.packet_type == PktType.PktTypeCompletion, (
        f"Expected PktTypeCompletion, got {pkt.get_packet_type_name()}. "
        f"Full packet: {pkt}"
    )
    # UNIT_ID should be 1 (slave-side wrapper, axi4_master_*_mon) or 2
    # (master-side wrapper, axi4_slave_*_mon) per the Stage-2 ID
    # scheme. Order of arrival depends on arbitration.
    assert pkt.unit_id in (1, 2), (
        f"Unexpected UNIT_ID {pkt.unit_id}: completion packets should "
        f"come from a bridge-instantiated wrapper (Unit 1 or 2)."
    )
    tb.log.info(
        f"PASS: drained completion packet from UNIT_ID={pkt.unit_id} "
        f"(AGENT_ID={pkt.agent_id:#x})"
    )


# ============================================================================
# Pytest wrapper
# ============================================================================

def test_bridge_1x2_rd_mon_irq(request):
    module, repo_root_, tests_dir, log_dir, _rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba':   '../../../../rtl/amba',
    })

    dut_name = "bridge_1x2_rd_mon_smoke"
    smoke_wrap = os.path.join(
        os.path.dirname(os.path.abspath(__file__)),
        'bridge_1x2_rd_mon_smoke.sv',
    )
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path='projects/components/bridge/rtl/filelists/bridge_1x2_rd_mon.f',
    )
    verilog_sources = list(verilog_sources) + [smoke_wrap]

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    sim_build_name = f"test_{dut_name}_irq{worker_suffix}"
    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    waves = get_wave_config(sim_build)
    extra_args = [
        '--assert', '--coverage',
        '-Wno-PINMISSING',
        '-Wno-WIDTHEXPAND',
    ] + waves['extra_args']
    extra_env = {
        'COCOTB_LOG_LEVEL': 'INFO',
        'LOG_PATH': log_path,
        'COCOTB_RESULTS_FILE': results_path,
        **waves['extra_env'],
    }

    rtl_parameters = {
        'MONITOR_ENABLE': 1,
        'ROUTE_COMPL_TO_ERR_FIFO': 1,
    }

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_bridge_1x2_rd_mon_irq",
        parameters=rtl_parameters,
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env,
    )
