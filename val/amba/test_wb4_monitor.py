# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""wb4_monitor: Wishbone B4 transaction monitor on the cmd/rsp queue contract.

Phases (each checks the monitor-bus packet stream against the stimulus):
  transfers   ACK/ERR/RTY mix, one packet per transfer in command order
  pipelined   responder latency > 1 so several transfers are open at once;
              pairing must stay in order (the slot-table failure mode)
  latency     perf packet only when latency > threshold, right direction code
  timeouts    cmd stall (consumer ready low) and rsp timeout (responder held),
              each reported once
  orphan      response with nothing outstanding -> WB_ERR_ORPHAN_RSP
  overflow    MAX_TRANSACTIONS+1 open -> WB_ERR_TRACK_LOST (+ the orphan its
              late response becomes)
  debug       queue active/idle edges
  addr_range  (N_ADDR_RANGES>0 builds) out-of-range address -> WB_ERR_ADDR_RANGE
              tagged PROTOCOL_WB
"""
import os
import random
from itertools import product

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.amba.wb4_monitor_tb import WB4MonitorTB, ERR_WINDOW, RTY_WINDOW
from TBClasses.monbus import PktType, WBErrorCode, WBTimeoutCode, WBCompletionCode, WBPerformanceCode, WBDebugCode
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

COUNTS = {'gate': 24, 'func': 96, 'full': 400}


def _mix(rng, n, aw):
    cmds = []
    for i in range(n):
        r = rng.random()
        if r < 0.10:
            adr = rng.randint(*ERR_WINDOW)
        elif r < 0.20:
            adr = rng.randint(*RTY_WINDOW)
        else:
            adr = rng.randrange(0, 0xD000, 4)
        cmds.append((adr & ((1 << aw) - 1), rng.randint(0, 1), rng.randint(1, 15), rng.getrandbits(32)))
    return cmds


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def wb4_monitor_test(dut):
    tb = WB4MonitorTB(dut)
    level = os.environ.get('TEST_LEVEL', 'gate')
    n = COUNTS[level]
    rng = random.Random(int(os.environ.get('SEED', '0')))
    await tb.setup_clocks_and_reset()
    d = dut
    if os.environ.get('TRACE_WIRES', '0') == '1':
        cocotb.start_soon(tb.trace_wires(160))

    # --- transfers: one packet per transfer, in order --------------------
    cmds = _mix(rng, n, tb.AW)
    await tb.send_cmds(cmds)
    await tb.wait_quiet()
    pk = tb.take_packets()
    tb.check_transfers(pk, list(tb.expected), 'transfers')
    tb.expected.clear()
    n_err = sum(1 for c in cmds if ERR_WINDOW[0] <= c[0] <= ERR_WINDOW[1])
    if int(d.transaction_count.value) != len(cmds):
        tb.errors.append(f"transaction_count {int(d.transaction_count.value)} != {len(cmds)}")
    if int(d.error_count.value) != n_err:
        tb.errors.append(f"error_count {int(d.error_count.value)} != {n_err} ERR terminations")
    if len(tb.of_type(pk, PktType.PktTypeTimeout)) or len(tb.of_type(pk, PktType.PktTypePerf)):
        tb.errors.append("transfers: timeout/perf packets while disabled")

    # --- pipelined: several open at once, pairing stays in order ---------
    tb.rsp_latency = 6
    peak = 0
    cmds = _mix(rng, n, tb.AW)
    chunk = max(2, tb.max_transactions // 2)
    for i in range(0, len(cmds), chunk):
        task = cocotb.start_soon(tb.send_cmds(cmds[i:i + chunk]))
        while not task.done():
            await tb.wait_clocks(tb.clk_name, 1)
            peak = max(peak, int(d.active_count.value))
        while int(d.active_count.value) > 1:
            await tb.wait_clocks(tb.clk_name, 1)
    await tb.wait_quiet()
    tb.check_transfers(tb.take_packets(), list(tb.expected), 'pipelined')
    tb.expected.clear()
    if peak < 2:
        tb.errors.append(f"pipelined: peak active_count {peak}, expected several open transfers")
    tb.log.info(f"pipelined: peak active_count {peak} (MAX_TRANSACTIONS={tb.max_transactions})")

    # --- latency: perf packet only over the threshold ---------------------
    # The BFM path adds a fixed few clocks; the threshold sits well above the
    # fast case and well below the slow one, and the packet carries the
    # measured latency, which must exceed the threshold.
    d.cfg_perf_enable.value = 1
    d.cfg_latency_enable.value = 1
    d.cfg_latency_threshold.value = 40
    tb.rsp_latency = 1
    await tb.send_cmds([(0x100, 0, 15, 0), (0x104, 1, 15, 0)])
    await tb.wait_quiet()
    fast = tb.of_type(tb.take_packets(), PktType.PktTypePerf)
    tb.expected.clear()
    tb.rsp_latency = 60
    await tb.send_cmds([(0x200, 0, 15, 0), (0x204, 1, 15, 0)])
    await tb.wait_quiet()
    slow = tb.of_type(tb.take_packets(), PktType.PktTypePerf)
    tb.expected.clear()
    if fast:
        tb.errors.append(f"latency: {len(fast)} perf packets under the threshold")
    codes = [p.event_code for p in slow]
    want = [int(WBPerformanceCode.WB_PERF_READ_LATENCY), int(WBPerformanceCode.WB_PERF_WRITE_LATENCY)]
    if codes != want or any(tb.addr_of(p) <= 40 for p in slow):
        tb.errors.append(f"latency: perf packets {[(p.event_code, tb.addr_of(p)) for p in slow]}, "
                         f"want codes {want} with latency > 40")
    d.cfg_perf_enable.value = 0
    d.cfg_latency_enable.value = 0
    tb.rsp_latency = 1

    # --- timeouts: cmd stall and rsp hold, reported once each -------------
    d.cfg_timeout_enable.value = 1
    d.cfg_cmd_timeout_cnt.value = 20
    d.cfg_rsp_timeout_cnt.value = 30
    tb.cmd_sink.ready_policy = 'stall'
    task = cocotb.start_soon(tb.send_cmds([(0x300, 1, 15, 0)]))
    await tb.wait_clocks(tb.clk_name, 120)
    tb.cmd_sink.ready_policy = 'valid_first'
    await task
    await tb.wait_quiet()
    to = tb.of_type(tb.take_packets(), PktType.PktTypeTimeout)
    tb.expected.clear()
    if [p.event_code for p in to] != [int(WBTimeoutCode.WB_TIMEOUT_CMD)] or tb.addr_of(to[0]) != 0x300 if to else True:
        tb.errors.append(f"cmd timeout: {[(p.event_code, hex(tb.addr_of(p))) for p in to]}, want one WB_TIMEOUT_CMD @0x300")
    tb.hold = True
    await tb.send_cmds([(0x400, 0, 15, 0), (0x404, 0, 15, 0)])
    await tb.wait_clocks(tb.clk_name, 150)
    tb.hold = False
    await tb.wait_quiet()
    pk = tb.take_packets()
    to = tb.of_type(pk, PktType.PktTypeTimeout)
    tb.check_transfers(pk, list(tb.expected), 'rsp-timeout')
    tb.expected.clear()
    # The head (0x400) times out once; 0x404 then becomes head with an age
    # already past the limit, so it is reported once as well.
    if [(p.event_code, tb.addr_of(p)) for p in to] != [(int(WBTimeoutCode.WB_TIMEOUT_RSP), 0x400),
                                                         (int(WBTimeoutCode.WB_TIMEOUT_RSP), 0x404)]:
        tb.errors.append(f"rsp timeout: {[(p.event_code, hex(tb.addr_of(p))) for p in to]}, want one per entry")
    d.cfg_timeout_enable.value = 0

    # --- orphan -----------------------------------------------------------
    tc = int(d.transaction_count.value)
    await tb.send_orphan()
    await tb.wait_quiet()
    er = tb.of_type(tb.take_packets(), PktType.PktTypeError)
    if [p.event_code for p in er] != [int(WBErrorCode.WB_ERR_ORPHAN_RSP)]:
        tb.errors.append(f"orphan: error packets {[p.event_code for p in er]}, want one WB_ERR_ORPHAN_RSP")
    if int(d.transaction_count.value) != tc:
        tb.errors.append("orphan: transaction_count moved on an orphan response")

    # --- overflow: MAX_TRANSACTIONS+1 open ---------------------------------
    tb.hold = True
    over = [(0x1000 + 4 * i, i & 1, 15, 0) for i in range(tb.max_transactions + 1)]
    await tb.send_cmds(over)
    await tb.wait_clocks(tb.clk_name, 10)
    if int(d.active_count.value) != tb.max_transactions:
        tb.errors.append(f"overflow: active_count {int(d.active_count.value)} != MAX_TRANSACTIONS")
    tb.hold = False
    await tb.wait_quiet()
    pk = tb.take_packets()
    tb.check_transfers(pk, list(tb.expected)[:tb.max_transactions], 'overflow')
    tb.expected.clear()
    lost = [p for p in pk if p.event_code == int(WBErrorCode.WB_ERR_TRACK_LOST) and p.pkt_type == int(PktType.PktTypeError)]
    orph = [p for p in pk if p.event_code == int(WBErrorCode.WB_ERR_ORPHAN_RSP) and p.pkt_type == int(PktType.PktTypeError)]
    if len(lost) != 1 or tb.addr_of(lost[0]) != over[-1][0]:
        tb.errors.append(f"overflow: TRACK_LOST packets {[(hex(tb.addr_of(p))) for p in lost]}, want one @0x{over[-1][0]:X}")
    if len(orph) != 1:
        tb.errors.append(f"overflow: {len(orph)} orphan packets for the untracked transfer's response, want 1")

    # --- debug: queue active/idle edges -----------------------------------
    d.cfg_debug_enable.value = 1
    d.cfg_trans_debug_enable.value = 1
    await tb.send_cmds([(0x500, 0, 15, 0)])
    await tb.wait_quiet()
    dbg = [p.event_code for p in tb.of_type(tb.take_packets(), PktType.PktTypeDebug)]
    tb.expected.clear()
    if dbg != [int(WBDebugCode.WB_DEBUG_QUEUE_ACTIVE), int(WBDebugCode.WB_DEBUG_QUEUE_IDLE)]:
        tb.errors.append(f"debug: {dbg}, want ACTIVE then IDLE")
    d.cfg_debug_enable.value = 0
    d.cfg_trans_debug_enable.value = 0

    # --- addr_range (only when the checker is built) ----------------------
    if tb.n_addr_ranges > 0:
        d.cfg_addr_check_enable.value = 1
        d.cfg_addr_range_enable.value = 1
        d.cfg_addr_range_low.value = 0x0000
        d.cfg_addr_range_high.value = 0x0FFF
        await tb.send_cmds([(0x0800, 1, 15, 0), (0x8000, 0, 15, 0)])
        await tb.wait_quiet()
        pk = tb.take_packets()
        tb.expected.clear()
        rng_pk = [p for p in pk if p.pkt_type == int(PktType.PktTypeError)
                  and p.event_code == int(WBErrorCode.WB_ERR_ADDR_RANGE)]
        if len(rng_pk) != 1 or not rng_pk[0].is_wb_protocol():
            tb.errors.append(f"addr_range: {len(rng_pk)} range packets (want 1, tagged WB): "
                             f"{[(p.protocol, p.event_code) for p in pk]}")
        d.cfg_addr_check_enable.value = 0

    tb.done = True
    assert tb.report(), f"wb4_monitor failed: {tb.errors[:5]}"


def _params():
    levels = os.environ.get('TEST_LEVEL', 'gate').split(',')
    return [(32, 32, 8, 0, lv) for lv in levels] + [(32, 32, 4, 2, lv) for lv in levels] + \
           [(16, 64, 8, 0, lv) for lv in levels if lv != 'gate']


@pytest.mark.parametrize("addr_width, data_width, max_transactions, n_addr_ranges, test_level", _params())
def test_wb4_monitor(request, addr_width, data_width, max_transactions, n_addr_ranges, test_level):
    """wb4_monitor (rtl/amba/wb4/wb4_monitor.sv) driven on both queues by GAXI BFMs,
    packets decoded through the shared MonbusSlave/parse path."""
    tag = f"aw{addr_width:03d}_dw{data_width:03d}_mt{max_transactions}_ar{n_addr_ranges}_{test_level}"
    unit_id, agent_id = 1, 11
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba', 'rtl_amba_includes': 'rtl/amba/includes'})
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path="rtl/amba/filelists/wb4_monitor.f")
    name = f"test_{worker_id}_wb4_monitor_{tag}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    rtl_parameters = {'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
                      'MAX_TRANSACTIONS': str(max_transactions), 'N_ADDR_RANGES': str(n_addr_ranges),
                      'UNIT_ID': str(unit_id), 'AGENT_ID': str(agent_id)}
    extra_env = {
        'TEST_LEVEL': test_level, 'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
        'MAX_TRANSACTIONS': str(max_transactions), 'N_ADDR_RANGES': str(n_addr_ranges),
        'UNIT_ID': str(unit_id), 'AGENT_ID': str(agent_id),
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': 'wb4_monitor', 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    compile_args = ["-Wno-DECLFILENAME", "-Wno-UNUSEDPARAM", "-Wno-UNUSEDSIGNAL",
                    "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC", "-Wno-PINCONNECTEMPTY"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel='wb4_monitor', module=module, parameters=rtl_parameters, sim_build=sim_build,
        extra_env=extra_env, waves=enable_waves, keep_files=True, compile_args=compile_args,
        sim_args=(["--trace-fst", "--trace-structs"] if enable_waves else []),
        plus_args=(["--trace"] if enable_waves else []))
