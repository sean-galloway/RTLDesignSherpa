#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Real-error-injection exercise for the monitored bridge.
#
# Sister to test_bridge_1x2_rd_monitor_irq.py. That test exercises the
# IRQ + drain path using completions (the most reliably-produced packet
# type). This one exercises the same plumbing using a REAL on-bus error:
# the slave BFM is monkey-patched to drive RRESP=SLVERR on its read
# response, which causes the slave-side axi4_master_rd_mon wrapper
# (UNIT_ID=1) and the master-side axi4_slave_rd_mon wrapper (UNIT_ID=2)
# to each emit a PktTypeError packet with event_code = AXI_ERR_RESP_
# SLVERR (0x0).
#
# Instantiates bridge_1x2_rd_mon_smoke with
#     MONITOR_ENABLE=1               (per-port monitors fire)
#     ENABLE_ERROR_PATH=1            (per-port cfg_*_error_enable=1,
#                                     PktTypeError -> err FIFO -> IRQ)
#
# Confirms:
#   1. mon_irq_out asserts as a result of the slave returning SLVERR
#   2. The packet drained via s_mon_axil decodes as PktTypeError
#   3. The event_code is AXI_ERR_RESP_SLVERR (i.e. the chain monitor ->
#      arbiter -> monbus_axil_group preserves the SLVERR identity)
#
# Implementation note on the BFM override:
#   AXI4SlaveRead.create_r_packet hardcodes resp=0 (OKAY) on every beat.
#   There is no per-instance "force RRESP" knob -- the randomization
#   manager is stochastic, not per-transaction. So we monkey-patch the
#   slave's _generate_read_response coroutine with a small custom one
#   that mirrors the original burst-generation logic but stamps the
#   chosen resp value on every R beat. This is scoped to one slave
#   instance only (slave_rd[0] aka ddr_rd) so the other slave keeps
#   responding OKAY -- useful if a test wanted to alternate good/bad
#   responses, though this test only drives one read.

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

from TBClasses.monbus import (
    parse,
    PktType,
    ProtocolType,
)
from TBClasses.monbus.monbus_types import AXIErrorCode


# ============================================================================
# Slave BFM SLVERR override
# ============================================================================

def install_slverr_override(slave, force_resp: int = 2) -> None:
    """Monkey-patch `slave._generate_read_response` to drive RRESP=force_resp
    on every beat. Caller passes 2 for SLVERR, 3 for DECERR.

    Mirrors the original burst-handling structure from CocoTBFramework's
    AXI4SlaveRead._generate_read_response: emit `arlen+1` beats, mark the
    final one with last=1, push them all to r_channel.transmit_queue, and
    kick the transmit pipeline if it is not already running. The only
    semantic change is `resp=force_resp` instead of `resp=0`.
    """
    from cocotb.triggers import RisingEdge as _RE

    async def _slverr_response(ar_packet):
        try:
            burst_len = getattr(ar_packet, 'len', 0) + 1
            packet_id = getattr(ar_packet, 'id', 0)

            # Same configurable delay as the original.
            for _ in range(slave.response_delay_cycles):
                await _RE(slave.clock)

            r_packets = []
            for i in range(burst_len):
                is_last = (i == burst_len - 1)
                r_packets.append(slave.r_channel.create_packet(
                    id=packet_id,
                    data=0xDEAD_BEEF,  # Garbage data; resp is the point.
                    resp=force_resp,
                    last=1 if is_last else 0,
                ))

            for r_packet in r_packets:
                slave.r_channel.transmit_queue.append(r_packet)

            if not slave.r_channel.transmit_coroutine:
                slave.r_channel.transmit_coroutine = cocotb.start_soon(
                    slave.r_channel._transmit_pipeline()
                )
        except Exception as e:
            if slave.log:
                slave.log.error(f"slverr override response error: {e}")

    slave._generate_read_response = _slverr_response


# ============================================================================
# axil_read helper -- identical contract to the IRQ test's
# ============================================================================

async def axil_read32(dut, addr: int, timeout_cycles: int = 200) -> int:
    """One AR / R handshake on s_mon_axil_*. Returns the 64-bit rdata word
    (the bridge's monbus_axil_group has S_AXIL_DATA_WIDTH=64; each AXIL
    read returns one beat = one slice of the three-beat err_fifo record)."""
    clk = dut.aclk
    dut.s_mon_axil_arvalid.value = 1
    dut.s_mon_axil_araddr.value = addr
    dut.s_mon_axil_arprot.value = 0
    dut.s_mon_axil_rready.value = 1
    for _ in range(timeout_cycles):
        await RisingEdge(clk)
        if int(dut.s_mon_axil_arready.value) == 1:
            break
    else:
        raise TimeoutError(
            f"s_mon_axil ar handshake timeout (addr=0x{addr:08x})"
        )
    dut.s_mon_axil_arvalid.value = 0
    for _ in range(timeout_cycles):
        if int(dut.s_mon_axil_rvalid.value) == 1:
            rdata = int(dut.s_mon_axil_rdata.value) & ((1 << 64) - 1)
            break
        await RisingEdge(clk)
    else:
        raise TimeoutError(
            f"s_mon_axil r handshake timeout (addr=0x{addr:08x})"
        )
    await RisingEdge(clk)
    dut.s_mon_axil_rready.value = 0
    return rdata


# ============================================================================
# CocoTB test
# ============================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_1x2_rd_mon_error_inject(dut):
    """Drive a read, slave returns SLVERR, verify IRQ + decoded error packet."""

    tb = Bridge1x2RdTB(dut)
    await tb.setup_clocks_and_reset()
    tb.log.info("=" * 80)
    tb.log.info("Monitored bridge error-inject test (MONITOR_ENABLE=1, "
                "ENABLE_ERROR_PATH=1)")
    tb.log.info("=" * 80)

    # ---- DIAGNOSTICS: confirm cfg routing landed correctly ---------
    tb.log.info(f"  cfg_mon_group_axi_err_select = "
                f"0x{int(dut.u_dut.u_mon_axil_group.cfg_axi_err_select.value):04x}")
    assert int(dut.u_dut.u_mon_axil_group.cfg_axi_err_select.value) & 0x0001, (
        "cfg_axi_err_select bit 0 (PktTypeError) is not set; "
        "wrapper ENABLE_ERROR_PATH parameter didn't take effect."
    )

    # ---- Install the SLVERR override on slave 0 (ddr_rd) -----------
    install_slverr_override(tb.slave_rd[0], force_resp=2)  # 2 = SLVERR
    tb.log.info("Installed SLVERR override on slave_rd[0] (ddr_rd)")

    # ---- IRQ watcher ------------------------------------------------
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

    # ---- Drive one read; slave will return SLVERR -------------------
    # The master BFM raises RuntimeError("AXI4 read error: SLVERR") when
    # RRESP != 0 -- that's the expected outcome of a real bus error, so
    # we catch it. The point of the test is what the monitor chain sees
    # downstream, not what the master sees.
    tb.log.info("Driving read at slave 0 (ddr_rd) -- expecting SLVERR")
    try:
        await tb.master_read(0, 0x00000100)
        raise AssertionError(
            "Master read returned without RuntimeError -- the SLVERR "
            "override didn't take effect."
        )
    except RuntimeError as e:
        msg = str(e)
        assert "SLVERR" in msg, (
            f"Expected SLVERR in master read exception, got: {msg}"
        )
        tb.log.info(f"  Master saw expected error: {msg}")

    # Let the monitor chain quiesce.
    await ClockCycles(tb.clock, 200)

    err_count = int(dut.u_dut.u_mon_axil_group.err_fifo_count.value)
    wr_count = int(dut.u_dut.u_mon_axil_group.write_fifo_count.value)
    irq = int(dut.mon_irq_out.value)
    tb.log.info(f"  err_fifo_count = {err_count}")
    tb.log.info(f"  write_fifo_count = {wr_count}")
    tb.log.info(f"  mon_irq_out = {irq}")

    irq_task.kill()

    # ---- Assert IRQ fired -------------------------------------------
    assert irq_asserted['cycle'] is not None, (
        "mon_irq_out never asserted -- no error packet reached the err "
        "FIFO. Check ENABLE_ERROR_PATH wiring and the slave BFM override."
    )
    tb.log.info(f"PASS: mon_irq_out asserted at cycle {irq_asserted['cycle']}")

    # ---- Drain one packet via the s_mon_axil_* slice-counter path ---
    tb.log.info("Draining one err_fifo entry via s_mon_axil_* ...")
    beats = []
    for offset in (0x00, 0x08, 0x10):
        beat = await axil_read32(dut, offset)
        tb.log.info(f"  beat @0x{offset:02x}: 0x{beat:016x}")
        beats.append(beat)

    raw_pkt = ((beats[1] & ((1 << 64) - 1)) << 64) | (beats[0] & ((1 << 64) - 1))
    source_ts = beats[2] & ((1 << 64) - 1)
    pkt = parse(raw_pkt)
    tb.log.info(f"Decoded: {pkt}  (source_ts=0x{source_ts:016x})")

    # ---- Assert decoded content -------------------------------------
    assert pkt.protocol == ProtocolType.PROTOCOL_AXI, pkt
    assert pkt.packet_type == PktType.PktTypeError, (
        f"Expected PktTypeError, got {pkt.get_packet_type_name()}. "
        f"Full packet: {pkt}"
    )
    assert pkt.event_code == AXIErrorCode.AXI_ERR_RESP_SLVERR, (
        f"Expected event_code AXI_ERR_RESP_SLVERR (0x0), got "
        f"{pkt.event_code:#x}. Full packet: {pkt}"
    )
    # UNIT_ID should be 1 (slave-side axi4_master_*_mon, which sees the
    # SLVERR first on the m_axi side) or 2 (master-side axi4_slave_*_mon,
    # which sees it on the slave-side once the error has propagated back).
    assert pkt.unit_id in (1, 2), (
        f"Unexpected UNIT_ID {pkt.unit_id}: error packets should come "
        f"from a bridge-instantiated wrapper (Unit 1 or 2)."
    )
    tb.log.info(
        f"PASS: drained AXI_ERR_RESP_SLVERR packet from UNIT_ID={pkt.unit_id} "
        f"(AGENT_ID={pkt.agent_id:#x})"
    )


# ============================================================================
# Pytest wrapper
# ============================================================================

def test_bridge_1x2_rd_mon_error_inject(request):
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
    sim_build_name = f"test_{dut_name}_error_inject{worker_suffix}"
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
        'ENABLE_ERROR_PATH': 1,
    }

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_bridge_1x2_rd_mon_error_inject",
        parameters=rtl_parameters,
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env,
    )
