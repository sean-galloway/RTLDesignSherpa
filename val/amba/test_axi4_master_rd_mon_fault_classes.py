# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_axi4_master_rd_mon_fault_classes
# Purpose: POSITIVE emission tests for the monitor's FAULT cones -- THRESHOLD,
#          TIMEOUT and PERF -- driven by real AXI stimulus at the wrapper.
#
# Why this exists
# ---------------
# val/amba had no test proving these cones ever fire. The ENABLE sweep only
# checks the NEGATIVE direction (ENABLE=0 -> zero packets of that type) and says
# so in its own comment:
#
#     "Other cones (error/timeout/threshold) need stimulus to fire; we don't
#      require them under this clean traffic."
#
# That is a coverage hole wearing a justification, and it had a cause: the only
# knob for injecting latency, `set_timing_profile`, looked its config up into a
# local variable and never applied it. No test COULD provoke a threshold or a
# timeout. The pktgen harness (test_axi_monitor_pktgen) covers the packet
# GENERATION path by driving the transaction table directly, which is a
# different thing: it proves a packet is formatted correctly given a table
# state, not that real traffic ever produces that state.
#
# The gap showed up on silicon: the monitor-validation board flow reported
# TIMEOUT and THRESHOLD as NOT SEEN under deliberate fault injection, with the
# CSRs verified correct by readback -- and there was no unit test to bisect
# against.
#
# Each case is a pair: a POSITIVE (stimulus that must produce the packet) and a
# NEGATIVE control (the same traffic with the cone's trigger out of reach, which
# must produce none). A positive alone can pass for the wrong reason -- a cone
# that fires on everything looks identical to one that fires correctly.

import os
import random

import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.axi4.monitor.axi4_master_monitor_tb import AXI4MasterMonitorTB

PKT_ERROR, PKT_COMPL, PKT_THRESHOLD, PKT_TIMEOUT, PKT_PERF = 0, 1, 2, 3, 4


def _count(tb, ptype):
    return sum(1 for p in tb.mon_slave.received_packets
               if int(getattr(p, "pkt_type", -1)) == ptype)


async def _drive_reads(tb, n, base=0x1000, stride=0x40):
    for i in range(n):
        ok, _, _ = await tb.base_tb.single_read_test(base + i * stride)
        if not ok:
            raise RuntimeError(f"read #{i} failed")


@cocotb.test(timeout_time=60, timeout_unit="sec")
async def axi4_master_rd_mon_fault_classes_test(dut):
    """THRESHOLD / TIMEOUT / PERF must fire under stimulus, and must not without it."""
    case = os.environ.get("TEST_CASE", "threshold").lower()
    n_txns = int(os.environ.get("TEST_TXN_COUNT", "12"))

    tb = AXI4MasterMonitorTB(dut, is_write=False, aclk=dut.aclk, aresetn=dut.aresetn)
    await tb.initialize()

    if case == "threshold":
        # POSITIVE: a latency threshold BELOW the response latency the 'slow'
        # profile produces. This is the case that silently could not work while
        # set_timing_profile was a no-op -- the profile is what creates latency.
        dut.cfg_threshold_enable.value = 1
        dut.cfg_latency_threshold.value = 4        # cycles; slow profile exceeds this
        dut.cfg_timeout_cycles.value = 0xFFFF      # max: the port is 16-bit, so this
                                           # is as 'quiet' as the cone gets
        await tb.base_tb.wait_clocks("aclk", 2)
        tb.base_tb.set_timing_profile("slow")
        await _drive_reads(tb, n_txns)
        await tb.base_tb.wait_clocks("aclk", 400)
        got = _count(tb, PKT_THRESHOLD)
        tb.log.info(f"[threshold positive] latency_threshold=4 slow-traffic -> {got} packets")
        assert got > 0, (
            "THRESHOLD cone enabled, latency_threshold=4, and the slow timing "
            f"profile applied -- but {got} threshold packets were emitted. Either "
            "the cone does not respond to cfg_latency_threshold, or the timing "
            "profile is not producing latency (check set_timing_profile actually "
            "calls set_randomizer on the response components).")

        # NEGATIVE: same traffic, threshold out of reach -> must be silent.
        dut.cfg_latency_threshold.value = 0x0FFFFFFF
        await tb.base_tb.wait_clocks("aclk", 300)   # drain in-flight first...
        tb.mon_slave.received_packets.clear()       # ...THEN clear
        await _drive_reads(tb, n_txns, base=0x4000)
        await tb.base_tb.wait_clocks("aclk", 400)
        got = _count(tb, PKT_THRESHOLD)
        tb.log.info(f"[threshold negative] latency_threshold=0x0FFFFFFF -> {got} packets")
        assert got == 0, (
            f"{got} THRESHOLD packets with the threshold at 0x0FFFFFFF -- the cone "
            "is firing regardless of cfg_latency_threshold, so the positive case "
            "above proves nothing.")

    elif case == "timeout":
        # POSITIVE: a timeout window shorter than the response latency.
        # UNITS: cfg_timeout_cycles counts MICROSECONDS, not clocks -- the
        # timers advance on the 1 us frequency-invariant tick, which is the
        # point of using counter_freq_invariant (a timeout means the same
        # wall-clock thing at any aclk). The full 16 bits now reach the
        # comparator: up to 65535 us ~= 65 ms.
        #
        # This used to be squashed to 4 bits in the wrapper, saturating every
        # value >= 16, so a host asking for 50 and one asking for 100000 got
        # identical hardware -- which is exactly why this cone went untested
        # and why the board flow could never make a timeout fire.
        #
        # The tick is now EXACTLY 1 us: the wrapper builds the
        # counter_freq_invariant LUT from ACLK_MHZ (every entry = the real
        # clock), so the divisor is the clock frequency and cfg_freq_sel does
        # not matter. At this TB's 100 MHz, 1 us = 100 clocks.
        #
        # Two earlier revisions of this test were calibrated against broken
        # ticks -- 19 clocks (freq_sel hardwired to index 1) and then ~105
        # clocks (nearest entry in a generic 5..220 table). Sizing the table to
        # the design removes the approximation entirely.
        dut.cfg_timeout_enable.value = 1
        dut.cfg_timeout_cycles.value = 2               # 2 us = 200 clocks @100MHz
        dut.cfg_latency_threshold.value = 0x0FFFFFFF   # keep threshold quiet
        await tb.base_tb.wait_clocks("aclk", 2)
        # Stall responses FAR longer than one tick. The named profiles top out
        # around 12 clocks, so they cannot reach even the minimum timeout.
        from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
        tb.base_tb.r_master.set_randomizer(
            FlexRandomizer({'valid_delay': ([(300, 400)], [1.0])}))
        await _drive_reads(tb, n_txns)
        await tb.base_tb.wait_clocks("aclk", 600)
        got = _count(tb, PKT_TIMEOUT)
        tb.log.info(f"[timeout positive] timeout=2us (200 clk @100MHz) vs 300-400 clk stall -> {got} packets")
        assert got > 0, (
            "TIMEOUT cone enabled at 2 us (200 clocks @100MHz) against a 300-400 clock stall "
            f"-- but {got} timeout packets were emitted. The board flow sees the "
            "same thing with its CSRs verified by readback, so this is the unit "
            "case that should bisect it.")

        # NEGATIVE: generous window, same traffic -> silent.
        dut.cfg_timeout_cycles.value = 0xFFFF
        await tb.base_tb.wait_clocks("aclk", 300)   # drain in-flight first...
        tb.mon_slave.received_packets.clear()       # ...THEN clear
        await _drive_reads(tb, n_txns, base=0x4000)
        await tb.base_tb.wait_clocks("aclk", 600)
        got = _count(tb, PKT_TIMEOUT)
        tb.log.info(f"[timeout negative] timeout=0xFFFF (65535 us, full width) -> {got} packets")
        assert got == 0, (
            f"{got} TIMEOUT packets with a 65535 us window -- the cone is not "
            "honouring cfg_timeout_cycles.")

    elif case == "perf":
        # POSITIVE: perf packets are a rollup, so they need completed traffic.
        dut.cfg_perf_enable.value = 1
        dut.cfg_timeout_cycles.value = 0xFFFF   # 16-bit port; 100000 would overflow
        dut.cfg_latency_threshold.value = 0x0FFFFFFF
        await tb.base_tb.wait_clocks("aclk", 2)
        tb.base_tb.set_timing_profile("normal")
        await _drive_reads(tb, max(n_txns, 16))
        await tb.base_tb.wait_clocks("aclk", 600)
        got = _count(tb, PKT_PERF)
        tb.log.info(f"[perf positive] {max(n_txns,16)} clean reads -> {got} packets")
        assert got > 0, (
            f"PERF cone enabled with clean completed traffic but {got} perf packets. "
            "Note the board flow sees rd_perf firing and wr_perf at zero, so an "
            "asymmetry here would be the same defect at unit level.")

        # NEGATIVE: cone disabled at runtime -> silent.
        dut.cfg_perf_enable.value = 0
        await tb.base_tb.wait_clocks("aclk", 300)   # drain in-flight first...
        tb.mon_slave.received_packets.clear()       # ...THEN clear
        await _drive_reads(tb, n_txns, base=0x4000)
        await tb.base_tb.wait_clocks("aclk", 600)
        got = _count(tb, PKT_PERF)
        tb.log.info(f"[perf negative] cfg_perf_enable=0 -> {got} packets")
        assert got == 0, f"{got} PERF packets with cfg_perf_enable=0 (runtime gate leaks)"

    else:
        raise ValueError(f"unknown TEST_CASE {case!r}")

    tb.log.info(f"✓ fault-class case '{case}' PASS")


# ----------------------------------------------------------------------------
# Pytest wrapper
# ----------------------------------------------------------------------------
def _params():
    return [("threshold", 12), ("timeout", 12), ("perf", 16)]


@pytest.mark.parametrize("case, txn_count", _params())
def test_axi4_master_rd_mon_fault_classes(case, txn_count):
    """Positive + negative emission for the fault cones of axi4_master_rd_mon."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        "rtl_axi4":          "rtl/amba/axi4/",
        "rtl_gaxi":          "rtl/amba/gaxi",
        "rtl_includes":      "rtl/amba/includes",
        "rtl_common":        "rtl/common",
        "rtl_shared":        "rtl/amba/shared",
        "rtl_monitor":       "rtl/amba/monitor",
        "rtl_amba_includes": "rtl/amba/includes",
    })

    dut_name = "axi4_master_rd_mon"
    worker_id = os.environ.get("PYTEST_XDIST_WORKER", "gw0")
    test_name = f"test_{worker_id}_{dut_name}_faultclass_{case}"
    log_path = os.path.join(log_dir, f"{test_name}.log")
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi4_master_rd_mon.f")

    # Every cone built: this test is about whether they FIRE, not whether the
    # parameter gates them (that is the enable sweep's job).
    rtl_parameters = {
        "AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32",
        "AXI_DATA_WIDTH": "32", "AXI_USER_WIDTH": "1",
        "UNIT_ID": "1", "AGENT_ID": "10", "MAX_TRANSACTIONS": "16",
        "ENABLE_ERROR_LOGIC": "1", "ENABLE_TIMEOUT_LOGIC": "1",
        "ENABLE_COMPL_LOGIC": "1", "ENABLE_THRESHOLD_LOGIC": "1",
        "ENABLE_PERF_LOGIC": "1", "ENABLE_DEBUG_LOGIC": "0",
    }

    extra_env = {
        "DUT": dut_name, "LOG_PATH": log_path, "COCOTB_LOG_LEVEL": "INFO",
        "TEST_ID_WIDTH": "8", "TEST_ADDR_WIDTH": "32", "TEST_DATA_WIDTH": "32",
        "TEST_STUB": "0", "TEST_CLK_PERIOD": "10",
        "SEED": os.environ.get("SEED", str(random.randint(0, 100000))),
        "TEST_CASE": case,
        "TEST_TXN_COUNT": str(txn_count),
    }

    compile_args = [
        "--trace-fst", "--trace-structs",
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED", "-Wno-DECLFILENAME",
        "-Wno-PINMISSING", "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE",
        "-Wno-TIMESCALEMOD",
    ]

    create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="axi4_master_rd_mon_fault_classes_test",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        keep_files=True,
        compile_args=compile_args,
    )
