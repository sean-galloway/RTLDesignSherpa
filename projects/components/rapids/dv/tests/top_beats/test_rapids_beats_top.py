# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_rapids_beats_top
# Purpose: rapids_beats_top APB -> register -> config smoke test (Pattern B)
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids_beats_top
#
# Author: sean galloway
# Created: 2026-07-02

"""
Smoke test for rapids_beats_top.

Config-only bring-up: instantiate the top with USE_AXI_MONITORS=0, tie off / idle
every non-APB interface, and exercise the APB -> register -> config chain using
BY-NAME register access (RegisterMap + rapids_regmap.py). Proves that
apb_slave -> cmdrsp_router -> peakrdl_to_cmdrsp -> rapids_regs -> rapids_config_block
is alive and that the top is live (system_idle / sched_error readable, no X/hang).

No descriptor kickoff, no data transfers -- nothing that could hang.
"""

import os
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.rapids.dv.tbclasses.rapids_beats_top_tb import (
    RapidsBeatsTopTB, RapidsBeatsTopDatapathTB)


# ===========================================================================
# COCOTB TEST FUNCTIONS - thin; logic lives in the TB
# ===========================================================================

@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_smoke(dut):
    """APB->register->config smoke: by-name read/write-back on base registers."""
    tb = RapidsBeatsTopTB(dut)
    await tb.setup_clocks_and_reset()

    errors = []

    # ---- 1. Read-only sanity: confirm the APB->regblock read path is alive. ----
    # VERSION reset default from rapids_regmap.py: 0x0008005A
    #   MINOR=0x5A [7:0], MAJOR=0x00 [15:8], NUM_CHANNELS=0x08 [23:16]
    version = await tb.read_reg('VERSION')
    if (version & 0xFF) != 0x5A:
        errors.append(f"VERSION MINOR mismatch: got 0x{version:08X}, expected MINOR=0x5A")
    if ((version >> 16) & 0xFF) != tb.NUM_CHANNELS:
        errors.append(f"VERSION NUM_CHANNELS mismatch: got 0x{version:08X}, "
                      f"expected 0x{tb.NUM_CHANNELS:02X}")
    tb.log.info(f"VERSION = 0x{version:08X} (read path alive)")

    # GLOBAL_STATUS is readable (SYSTEM_IDLE reflected in bit 0).
    global_status = await tb.read_reg('GLOBAL_STATUS')
    tb.log.info(f"GLOBAL_STATUS = 0x{global_status:08X}")

    # ---- 2. Write/read-back RW base config registers (0x100-0x3FF). ----
    # (reg_name, write_value, readback_mask) -- mask covers only the RW field bits
    # that read back what was written (RSVD bits read 0).
    checks = [
        ('SCHED_TIMEOUT_CYCLES', 0x0001_2345, 0xFFFF_FFFF),  # full 32-bit RW
        ('DESCENG_ADDR0_BASE',   0xDEAD_BEEF, 0xFFFF_FFFF),  # full 32-bit RW
        ('CHANNEL_ENABLE',       0x0000_00AB, 0x0000_00FF),  # CH_EN[7:0]
        ('GLOBAL_CTRL',          0x0000_0001, 0x0000_0003),  # GLOBAL_EN[0] (avoid RST bit)
    ]

    for reg_name, wr_val, mask in checks:
        await tb.write_reg(reg_name, wr_val)
        rd_val = await tb.read_reg(reg_name)
        exp = wr_val & mask
        got = rd_val & mask
        if got != exp:
            errors.append(f"{reg_name}: wrote 0x{wr_val:08X}, read 0x{rd_val:08X} "
                          f"(masked exp 0x{exp:08X} != got 0x{got:08X})")
        else:
            tb.log.info(f"{reg_name}: write/readback OK (0x{got:08X})")

    # ---- 3. Confirm the top is live: status outputs resolvable (no X/hang). ----
    system_idle, sched_error = tb.read_status_signals()
    # After config-only bring-up nothing was kicked off -> no scheduler errors.
    if sched_error != 0:
        errors.append(f"sched_error non-zero after config-only bring-up: 0x{sched_error:X}")

    assert not errors, "rapids_beats_top smoke errors:\n  " + "\n  ".join(errors)
    tb.log.info("rapids_beats_top smoke PASSED")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_datapath(dut):
    """End-to-end DATAPATH test: config + kickoff over APB (by name), real data
    moved through the top in BOTH directions, verified against memory.

    SOURCE (memory->network): rd_mem is preloaded with a known pattern; the core
      reads it via m_axi_rd, pushes it through the source SRAM, and the TB drains
      it via src_drain -> compared to the preloaded pattern.
    SINK (network->memory): the TB injects a known pattern via snk_fill; the core
      buffers it in the sink SRAM and writes it via m_axi_wr into wr_mem ->
      compared to the injected pattern.
    """
    tb = RapidsBeatsTopDatapathTB(dut)
    await tb.setup_clocks_and_reset()   # clock/reset + APB master + config-by-name + BFMs
    await tb.initialize_test()          # start the source drainer

    # Phase 1: single channel, one descriptor, modest length.
    ok1, stats1 = await tb.test_single_channel(channel=0, beats=8)
    # Phase 2: same channel, two sequential descriptors.
    ok2, stats2 = await tb.test_multi_descriptor(channel=1, beats=6, ndesc=2)

    tb.finalize_test()

    # The top must not have flagged a scheduler error moving real data.
    _, sched_error = tb.read_status_signals()

    tb.log.info(f"datapath phase1={stats1} phase2={stats2} sched_error=0x{sched_error:X}")
    assert ok1, f"single-channel datapath failed: {stats1.get('errors')}"
    assert ok2, f"multi-descriptor datapath failed: {stats2.get('errors')}"
    assert sched_error == 0, f"sched_error non-zero after datapath run: 0x{sched_error:X}"
    tb.log.info("rapids_beats_top datapath PASSED (source + sink verified)")


@cocotb.test(timeout_time=180, timeout_unit="ms")
async def cocotb_test_datapath_stress(dut):
    """Multi-channel CONCURRENT datapath stress: drive ALL 8 channels, each with
    several descriptors, kicked off close together so they run concurrently and
    contend for the shared read/write engines. Verifies SOURCE + SINK end-to-end
    for every channel/descriptor, and sched_error==0 / system_idle==1 at the end.

    Concurrency is what surfaced the STREAM scheduler-timeout bug, so the
    scheduler watchdog (SCHED_TIMEOUT_CYCLES) is programmed BY NAME to a value
    sized for the whole contended batch before kickoff."""
    tb = RapidsBeatsTopDatapathTB(dut)
    await tb.setup_clocks_and_reset()   # clock/reset + APB master + config-by-name + BFMs
    await tb.initialize_test()          # start the source drainer

    # Size the write-completion watchdog to the concurrent workload (8 channels
    # sharing one write engine). BY NAME via SCHED_TIMEOUT_CYCLES.
    await tb.program_sched_timeout(500_000)

    channels = list(range(tb.NUM_CHANNELS))   # all 8 channels concurrently
    ok, stats = await tb.test_multi_channel_concurrent(channels, ndesc=3, beats=4)

    tb.finalize_test()

    system_idle, sched_error = tb.read_status_signals()
    tb.log.info(f"stress stats={stats} system_idle={system_idle} sched_error=0x{sched_error:X}")
    assert ok, f"concurrent multi-channel datapath failed: {stats.get('errors')}"
    assert sched_error == 0, f"sched_error non-zero after stress run: 0x{sched_error:X}"
    assert system_idle == 1, f"system not idle after stress run: {system_idle}"
    tb.log.info("rapids_beats_top datapath_stress PASSED (8 channels x 3 desc verified)")


# ---------------------------------------------------------------------------
# Monbus-group (USE_AXI_MONITORS=1) coverage -- mirrors stream_top_monbus.
# Monitor CSRs referenced BY NAME (resolved from rapids_regmap.py via the TB's
# RegisterMap): the MON block lives at 0x10C0+, reachable only with a 13-bit
# APB, hence APB_ADDR_WIDTH=13 for this build.
# Enable bits mirror stream: MON_EN[0], ERR_EN[1], COMPL_EN[2] -> 0x7 (leaves
# COMPRESS_EN[5]/PERF_EN[4] off; the group is built USE_COMPRESSION=0 anyway).
# ---------------------------------------------------------------------------
_MON_ENABLE_REGS   = ('DAXMON_ENABLE', 'RDMON_ENABLE', 'WRMON_ENABLE')
_MON_EN_VALUE      = 0x7
_MON_PKT_MASK_REGS = ('DAXMON_PKT_MASK', 'RDMON_PKT_MASK', 'WRMON_PKT_MASK')
_MON_ERR_CFG_REGS  = ('DAXMON_ERR_CFG', 'RDMON_ERR_CFG', 'WRMON_ERR_CFG')
# ERR_CFG.ERR_SELECT[3:0] bitmask by packet_type (bit1=Completion); ERR_MASK[15:8].
_ERR_CFG_ROUTE_COMPL = 0xFF02   # route completions -> err FIFO, error packets masked
_ERR_CFG_NONE        = 0xFF00   # nothing routed to err FIFO (trace path only)
# Monbus-group flush window (top-level cfg_mon_* inputs).
_MON_BASE  = 0x0000_1000
_MON_LIMIT = 0x0000_5000 - 1
_MON_WMARK = 3                  # one raw record = 3 beats -> flush eagerly


@cocotb.test(timeout_time=180, timeout_unit="ms")
async def cocotb_test_monbus(dut):
    """USE_AXI_MONITORS=1 monbus AXI-Lite end-to-end (mirrors stream_top_monbus).

    Builds the top with the three AXI monitors + monbus_axil_axil_group active,
    enables them BY NAME over APB, drives real descriptor transfers, and attaches
    the shared MonbusGroupHarness to the top's m_axil_mon_* (64-bit trace) /
    s_axil_err_* (32-bit err-drain) / mon_irq ports.
      Phase A -- completions stream out m_axil_mon_* and decode as AXI completions.
      Phase B -- completions routed to the err FIFO drive mon_irq; draining over
                 the 32-bit s_axil_err_* port (2:1 serializer, 6 beats/record)
                 clears the IRQ and the drained packets still decode."""
    from cocotb.triggers import ClockCycles
    from TBClasses.monbus import PktType
    from TBClasses.scoreboards.monbus_group import (
        MonbusGroupHarness, BeatLayout, BeatOrder)

    tb = RapidsBeatsTopDatapathTB(dut)   # apb_addr_width=13 comes from TEST_APB_ADDR_WIDTH env
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    # Enable the three AXI monitors (monitor+error+completion) and clear their
    # packet-drop masks so clean traffic emits completion packets.
    for reg in _MON_ENABLE_REGS:
        await tb.write_reg(reg, _MON_EN_VALUE)
    for reg in _MON_PKT_MASK_REGS:
        await tb.write_reg(reg, 0x0)

    # Program the group flush window (top-level inputs); default 0/0 stalls the
    # master-write path.
    dut.cfg_mon_base_addr.value = _MON_BASE
    dut.cfg_mon_limit_addr.value = _MON_LIMIT
    dut.cfg_mon_flush_watermark.value = _MON_WMARK
    await ClockCycles(dut.aclk, 5)

    # The group instance lives inside the g_axi_monitors generate; resolve it
    # best-effort for the fifo-count probes (trace/drain decode use only ports).
    group_node = None
    try:
        group_node = dut.g_axi_monitors.u_monbus_axil_group
    except AttributeError:
        tb.log.info("group instance not reachable; fifo-count probes disabled")

    mon = MonbusGroupHarness(
        dut, dut.aclk,
        drain_proto="axil", trace_proto="axil",
        drain_prefix="s_axil_err_", trace_prefix="m_axil_mon_",
        # rapids wires the group with S_AXIL_DATA_WIDTH=32: the err drain is a
        # 32-bit AXIL port (2:1 read serializer -> 6 beats/record); the trace
        # (m_axil_mon_*) stays 64-bit. Identical to stream_top_ch8.
        drain_data_width=32,
        group_node=group_node,
        irq_sig=dut.mon_irq,
        # Both ports emit beat0={tag,ts}, beat1=pkt[127:64], beat2=pkt[63:0].
        layout_drain=BeatLayout(order=BeatOrder.TS_HI_LO),
        layout_trace=BeatLayout(order=BeatOrder.TS_HI_LO),
        log=tb.log,
    )

    # ----- Phase A: trace path (completions stream out m_axil_mon_*) -----
    tb.log.info("=== Phase A: monbus group trace path (completions) ===")
    for reg in _MON_ERR_CFG_REGS:
        await tb.write_reg(reg, _ERR_CFG_NONE)     # nothing routed to err FIFO
    mon.start_trace_consumer()
    okA, statsA = await tb.test_single_channel(channel=0, beats=8)
    assert okA, f"Phase A transfer failed data integrity: {statsA.get('errors')}"
    await ClockCycles(dut.aclk, 4000)              # let the trace path flush
    mon.stop_trace_consumer()
    pkts = mon.parse_trace_records()
    st = mon.get_stats()
    tb.log.info(f"[rapids-monbus] trace beats={st.trace_beats} pkts={len(pkts)} "
                f"types={sorted({p.get_packet_type_name() for p in pkts})} "
                f"units={sorted({p.unit_id for p in pkts})} "
                f"protocols={sorted({int(p.protocol) for p in pkts})}")
    assert len(pkts) > 0, "no monbus records flushed from the rapids group trace path"
    assert len(pkts) == st.trace_beats // 3, "trace beats did not decode cleanly"
    assert any(p.packet_type == PktType.PktTypeCompletion for p in pkts), (
        f"no completion packets; got {sorted({p.get_packet_type_name() for p in pkts})}")
    tb.log.info("Phase A: trace path verified")

    # ----- Phase B: err FIFO + mon_irq (completions routed to err FIFO) -----
    tb.log.info("=== Phase B: err FIFO + mon_irq ===")
    for reg in _MON_ERR_CFG_REGS:
        await tb.write_reg(reg, _ERR_CFG_ROUTE_COMPL)   # completions -> err FIFO
    mon.clear()
    mon.start_irq_watch()
    okB, statsB = await tb.test_single_channel(channel=1, beats=8)
    assert okB, f"Phase B transfer failed data integrity: {statsB.get('errors')}"
    await ClockCycles(dut.aclk, 50)

    irq_live = int(dut.mon_irq.value)
    tb.log.info(f"[rapids-monbus] mon_irq={irq_live} irq_first_cycle={mon.irq_first_cycle}")
    assert mon.irq_asserted, "mon_irq never asserted with completions routed to err FIFO"

    # Drain records over the 32-bit port until mon_irq de-asserts (irq_out =
    # !err_fifo_empty). Loop-until-IRQ-clear is robust to the err_fifo_count net
    # not being reachable from cocotb (it is a PINCONNECTEMPTY output at the top).
    drained = []
    for _ in range(256):
        if int(dut.mon_irq.value) == 0:
            break
        try:
            drained.extend(await mon.drain_records(1))
        except TimeoutError:
            break
    await ClockCycles(dut.aclk, 20)
    irq_after = int(dut.mon_irq.value)
    mon.stop_irq_watch()
    tb.finalize_test()
    tb.log.info(f"[rapids-monbus] err-drained pkts={len(drained)} "
                f"types={sorted({p.get_packet_type_name() for p in drained})} "
                f"protocols={sorted({int(p.protocol) for p in drained})} "
                f"irq_after_drain={irq_after}")
    assert len(drained) >= 1, "no records drained from the err FIFO"
    assert all(p.packet_type == PktType.PktTypeCompletion for p in drained), (
        f"non-completion in err FIFO: {sorted({p.get_packet_type_name() for p in drained})}")
    assert irq_after == 0, "mon_irq did not clear after draining the err FIFO"
    mon.stop_fifo_monitor()
    tb.log.info("=== rapids_beats_top monbus-group trace + err-FIFO/IRQ paths verified ===")


# ===========================================================================
# PYTEST WRAPPER
# ===========================================================================

def _run_top(testcase, test_name, *, use_axi_monitors=0, apb_addr_width=12):
    """Shared runner: compile rapids_beats_top and run the given cocotb testcase.

    apb_addr_width / use_axi_monitors are threaded through BOTH the RTL build
    (-G params) AND the TB (TEST_* env) so they stay in lock-step. The monbus
    test needs APB_ADDR_WIDTH=13 to reach the MON regfile at 0x1000+ and
    USE_AXI_MONITORS=1 to instantiate the monbus_axil_axil_group under test."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_top_beats': '../../rtl/top_beats',
    })
    dut_name = "rapids_beats_top"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/top_beats/rapids_beats_top.f'
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'NUM_CHANNELS': 8,
        'DATA_WIDTH': 512,
        'ADDR_WIDTH': 64,
        'AXI_ID_WIDTH': 8,
        'SRAM_DEPTH': 512,
        'APB_ADDR_WIDTH': apb_addr_width,
        'APB_DATA_WIDTH': 32,
        'USE_AXI_MONITORS': use_axi_monitors,
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(12345),
        'TEST_NUM_CHANNELS': '8',
        'TEST_ADDR_WIDTH': '64',
        'TEST_DATA_WIDTH': '512',
        'TEST_AXI_ID_WIDTH': '8',
        'TEST_APB_ADDR_WIDTH': str(apb_addr_width),
        'TEST_APB_DATA_WIDTH': '32',
    }

    compile_args = [
        "-Wno-fatal",  # generated rapids_regs.sv trips MULTIDRIVEN/UNOPT; keep warnings non-fatal
        "-Wno-TIMESCALEMOD", "-Wno-WIDTH", "-Wno-UNOPTFLAT", "-Wno-CASEINCOMPLETE",
        "-Wno-MULTIDRIVEN", "-Wno-SELRANGE", "-Wno-UNUSEDSIGNAL",
    ]
    if enable_waves:
        compile_args.extend(['--trace', '--trace-structs', '--trace-max-array', '512'])

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir, os.path.join(repo_root, 'projects/components/rapids/dv/tbclasses')],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase=testcase,
            parameters=rtl_parameters,
            simulator='verilator',
            sim_build=sim_build,
            results_xml=results_path,
            extra_env=extra_env,
            compile_args=compile_args,
            waves=enable_waves,
            keep_files=True,
            plus_args=['--trace'] if enable_waves else [],
        )
        print(f"Test completed! Logs: {log_path}")
    except Exception as e:
        print(f"Test failed: {e}\nLogs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"View: {cmd_filename}")
        raise


@pytest.mark.top_beats
@pytest.mark.rapids_beats_top
def test_rapids_beats_top(request):
    """Config-only smoke: APB -> register -> config chain (by name)."""
    _run_top("cocotb_test_smoke", "test_rapids_beats_top_smoke")


@pytest.mark.top_beats
@pytest.mark.rapids_beats_top
def test_rapids_beats_top_datapath(request):
    """End-to-end datapath: real data moved through the top in both directions."""
    _run_top("cocotb_test_datapath", "test_rapids_beats_top_datapath")


@pytest.mark.top_beats
@pytest.mark.rapids_beats_top
def test_rapids_beats_top_datapath_stress(request):
    """Multi-channel concurrent datapath stress: all 8 channels, 3 desc each."""
    _run_top("cocotb_test_datapath_stress", "test_rapids_beats_top_datapath_stress")


@pytest.mark.top_beats
@pytest.mark.rapids_beats_top
def test_rapids_beats_top_monbus(request):
    """USE_AXI_MONITORS=1 monbus AXI-Lite end-to-end (trace + err-FIFO/IRQ)."""
    _run_top("cocotb_test_monbus", "test_rapids_beats_top_monbus",
             use_axi_monitors=1, apb_addr_width=13)


if __name__ == "__main__":
    class MockRequest:
        pass
    test_rapids_beats_top(MockRequest())
    test_rapids_beats_top_datapath(MockRequest())
    test_rapids_beats_top_datapath_stress(MockRequest())
    test_rapids_beats_top_monbus(MockRequest())
