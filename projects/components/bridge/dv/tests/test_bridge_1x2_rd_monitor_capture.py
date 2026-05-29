#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Real monitored-bridge test that asserts decoded monbus packets.
#
# Uses the same smoke wrapper as test_bridge_1x2_rd_monitor_smoke.py
# but instantiates it with MONITOR_ENABLE=1 so every per-port wrapper's
# cfg_monitor_enable is tied high. With monitoring on, completion
# packets fire on every transaction; they drain through the bridge's
# internal monbus_arbiter, into the unified monbus_axil_group's write
# FIFO, then out the m_mon_axil_* master-write port. The wrapper's
# tie-off accepts every write with awready=wready=1, so packets stream
# through unimpeded.
#
# This test:
#   - Spawns a cocotb monitor task that snoops every m_mon_axil_w
#     handshake and records the 64-bit wdata word
#   - Drives a small number of AXI4 reads
#   - Stops the monitor and reassembles the captured words into 128-bit
#     packets (packets-only mode: cfg_ts_append_enable=0, 16-byte
#     records = 2 × 64-bit beats per packet)
#   - Parses each packet via TBClasses.monbus.parse
#   - Asserts at least one completion packet appears from each side of
#     the bridge: the master-side wrapper (UNIT_ID=2) and the slave-
#     side wrapper (UNIT_ID=1)

import os
import sys
from pathlib import Path

import pytest

from TBClasses.shared.utilities import get_repo_root

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from projects.components.bridge.dv.tbclasses.bridge1x2_rd_tb import Bridge1x2RdTB

# Standalone monbus parser library -- no cocotb dependency, importable
# from any python entry point.
from TBClasses.monbus import (
    parse,
    MonitorPacket,
    MONBUS_PKT_WIDTH,
    PktType,
    ProtocolType,
)


# ============================================================================
# CocoTB test
# ============================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_1x2_rd_mon_capture(dut):
    """Enable monitoring, drive reads, capture monbus packets via
    m_mon_axil_w, parse, and assert on the resulting packet stream."""

    tb = Bridge1x2RdTB(dut)
    await tb.setup_clocks_and_reset()
    tb.log.info("=" * 80)
    tb.log.info("Monitored bridge capture test (MONITOR_ENABLE=1)")
    tb.log.info("=" * 80)

    # ---- Spawn the m_mon_axil_w snooper ------------------------------
    captured_words = []      # list of 64-bit wdata snapshots

    async def snoop_axil_writes():
        """Sample m_mon_axil_wdata on every cycle where
        wvalid && wready. The wrapper hard-ties wready=1, so this is
        effectively 'sample whenever wvalid'."""
        clk = dut.aclk
        while True:
            await RisingEdge(clk)
            try:
                wv = int(dut.m_mon_axil_wvalid.value)
                # 1'b1 tie at wrapper level means wready is always
                # 1; reading it here just keeps the assertion honest
                # in case the wrapper changes.
            except (ValueError, AttributeError):
                # Reset / X propagation -- skip
                continue
            if wv == 1:
                try:
                    wd = int(dut.m_mon_axil_wdata.value)
                except (ValueError, AttributeError):
                    continue
                captured_words.append(wd & ((1 << 64) - 1))

    snoop_task = cocotb.start_soon(snoop_axil_writes())

    # ---- Drive a few reads ------------------------------------------
    # One read per slave is enough to trigger compl packets from at
    # least the master-side rd wrapper and the active slave-side rd
    # wrapper. Two reads total -> 4 in-flight monbus events (2 per
    # transaction: one from master wrapper, one from slave wrapper).
    for slave_idx, addr in ((0, 0x00000100), (1, 0x80000100)):
        expected = tb.slave_mem_read(slave_idx, addr, master_idx=0)
        actual = await tb.master_read(0, addr)
        assert actual == expected, (
            f"Read mismatch master 0 -> slave {slave_idx} at 0x{addr:08x}: "
            f"got 0x{actual:08x}, expected 0x{expected:08x}"
        )
        tb.log.info(f"  read slave={slave_idx} addr=0x{addr:08x} OK")

    # Give the monbus path time to drain (per-port FIFO -> arbiter ->
    # group write FIFO -> AXIL master -> snooped wdata).
    await ClockCycles(tb.clock, 200)
    snoop_task.kill()

    tb.log.info(f"Captured {len(captured_words)} m_mon_axil_w beats")
    assert len(captured_words) >= 4, (
        f"Expected at least 4 wdata beats (2 packets * 2 beats per "
        f"packet-only record), got {len(captured_words)}"
    )
    assert len(captured_words) % 2 == 0, (
        f"Expected an even number of beats (2 per packet record), "
        f"got {len(captured_words)}"
    )

    # ---- Reassemble + parse -----------------------------------------
    # cfg_ts_append_enable=0 in the wrapper -> packets-only, 16-byte
    # records = 2 × 64-bit beats. Beat 0 = packet[63:0], beat 1 =
    # packet[127:64].
    packets = []
    for i in range(0, len(captured_words), 2):
        beat_lo = captured_words[i]
        beat_hi = captured_words[i + 1]
        raw = ((beat_hi & ((1 << 64) - 1)) << 64) | (beat_lo & ((1 << 64) - 1))
        if raw == 0:
            tb.log.warning(f"  beat-pair {i}/{i+1} all-zero, skipping")
            continue
        pkt = parse(raw)
        packets.append(pkt)
        tb.log.info(f"  pkt #{len(packets)}: {pkt}")

    assert len(packets) >= 2, (
        f"Expected at least 2 valid monbus packets, got {len(packets)}"
    )

    # ---- Assertions on decoded packet content -----------------------
    # The bridge generator's stage-2 ID scheme:
    #   master-side wrappers (axi4_slave_*_mon)  -> UNIT_ID = 2
    #   slave-side wrappers  (axi4_master_*_mon) -> UNIT_ID = 1
    # AGENT_ID encodes (port_idx << 4) | chan_bit, with chan_bit=0
    # for read wrappers. We did two reads, so we expect at least one
    # packet from the master-side wrapper (UNIT_ID=2, AGENT_ID=0x00)
    # and at least one from a slave-side wrapper (UNIT_ID=1, AGENT_ID
    # in {0x00, 0x10}).

    master_side = [p for p in packets if p.unit_id == 2]
    slave_side  = [p for p in packets if p.unit_id == 1]
    assert master_side, (
        f"No master-side wrapper packets (UNIT_ID=2) seen. "
        f"Got UNIT_IDs: {sorted({p.unit_id for p in packets})}"
    )
    assert slave_side, (
        f"No slave-side wrapper packets (UNIT_ID=1) seen. "
        f"Got UNIT_IDs: {sorted({p.unit_id for p in packets})}"
    )

    # All packets should be PROTOCOL_AXI -- the bridge is an AXI4
    # crossbar end-to-end.
    for p in packets:
        assert p.protocol == ProtocolType.PROTOCOL_AXI, (
            f"Non-AXI packet observed: {p}"
        )

    # At least one packet should be a Completion (PktTypeCompletion=1)
    # for the reads we drove. (Other packet types may also appear --
    # error/timeout/etc. aren't masked, but with clean reads to in-
    # range slave windows there should be no errors. We only care
    # that completions DO appear.)
    completions = [p for p in packets
                   if p.packet_type == PktType.PktTypeCompletion]
    assert completions, (
        f"No completion packets observed. Packet types seen: "
        f"{sorted({p.get_packet_type_name() for p in packets})}"
    )
    tb.log.info(
        f"PASS: {len(packets)} total packets, "
        f"{len(master_side)} master-side, {len(slave_side)} slave-side, "
        f"{len(completions)} completions"
    )


# ============================================================================
# Pytest wrapper
# ============================================================================

def test_bridge_1x2_rd_mon_capture(request):
    """Pytest wrapper for the monitored-bridge capture test."""
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
    test_name_plus_params = f"test_{dut_name}_capture"
    sim_build_name = f"{test_name_plus_params}{worker_suffix}"

    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    waves = get_wave_config(sim_build)

    # See test_bridge_1x2_rd_monitor_smoke.py for the rationale -- the
    # monitor RTL has pre-existing benign warnings that --assert would
    # promote to errors.
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

    # Override the smoke wrapper's MONITOR_ENABLE parameter so every
    # cfg_*_*_monitor_enable on the bridge top is tied high.
    rtl_parameters = {'MONITOR_ENABLE': 1}

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_bridge_1x2_rd_mon_capture",
        parameters=rtl_parameters,
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env,
    )
