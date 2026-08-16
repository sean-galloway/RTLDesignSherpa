# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi_monitor_wr_same_cycle
# Purpose: same-cycle AW+W first-beat regression for the write monitor
#
# Documentation: docs/markdown/rtl-amba/index.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-07-21

"""
Same-cycle AW+W first-beat regression for the write monitor (E4).

The trans_mgr's WID-less write match is a predicate over REGISTERED entries
requiring cmd_received, so a W beat arriving in the SAME cycle as its AW
matched nothing; with IS_AXI=1 the write-data orphan path is compiled dead, so
the beat was silently lost. The entry then waited for data forever and the B
response produced a spurious EVT_PROTOCOL ("response before data") error
instead of a completion.

Legal AXI4: AW and W are independent channels, and a master driving both in
the same cycle (single-beat writes especially) is routine -- skid-buffered
cores do exactly this at full throughput.

Phases:
  1. AW + W(wlast) in ONE cycle (single-beat write), B later
     -> must complete, no error.
  2. AW + first beat of a 2-beat burst in one cycle, second beat later
     -> must complete, no error.
  3. Control: AW, then W a cycle later (registered path) -> unchanged.
  4. Bypass must NOT hijack when a registered same-ID entry is still open:
     an open burst takes the beat; the same-cycle AW gets its own slot.
"""

import os

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

RESP_OKAY = 0b00


async def send_cmd_and_data(tb, txn_id, addr, length=0, wlast=True):
    """Drive AW and a W beat in the SAME cycle (the E4 scenario)."""
    tb.dut.cmd_id.value = txn_id
    tb.dut.cmd_addr.value = addr
    tb.dut.cmd_len.value = length
    tb.dut.cmd_valid.value = 1
    tb.dut.data_id.value = txn_id
    tb.dut.data_last.value = 1 if wlast else 0
    tb.dut.data_resp.value = RESP_OKAY
    tb.dut.data_valid.value = 1
    await RisingEdge(tb.dut.aclk)
    tb.dut.cmd_valid.value = 0
    tb.dut.data_valid.value = 0
    tb.dut.data_last.value = 0


async def send_resp(tb, txn_id, code=RESP_OKAY):
    """One B beat."""
    tb.dut.resp_id.value = txn_id
    tb.dut.resp_code.value = code
    tb.dut.resp_valid.value = 1
    await RisingEdge(tb.dut.aclk)
    tb.dut.resp_valid.value = 0


@cocotb.test(timeout_time=120, timeout_unit="sec")
async def axi_monitor_wr_same_cycle_test(dut):
    """Same-cycle AW+W first-beat regression (write monitor, IS_AXI=1)."""
    # Lazy import: val/amba is on sys.path at sim time via python_search.
    from test_axi_monitor_trans_mgr import AxiMonitorTransMgrTB, TRANS_ERROR

    tb = AxiMonitorTransMgrTB(dut)
    await tb.setup_clocks_and_reset()
    failures = []

    # ------------------------------------------------------------------
    # Phase 1: single-beat write, AW + W(wlast) in one cycle, B later.
    # ------------------------------------------------------------------
    tb.log.info("PHASE 1: same-cycle AW + W(wlast), single beat")
    tb.clear_packets()
    await send_cmd_and_data(tb, txn_id=1, addr=0x1000, length=0, wlast=True)
    await tb.idle(3)
    await send_resp(tb, txn_id=1)
    await tb.drain()

    compl = tb.completions()
    errs = tb.errors()
    if len(compl) != 1:
        failures.append(
            f"1: {len(compl)} completion packet(s), expected 1 -- the same-cycle "
            "W beat was lost and the write never completed")
    if errs:
        failures.append(
            f"1: {len(errs)} spurious error packet(s) on legal traffic "
            f"(codes={[hex(e.event_code) for e in errs]}) -- B after a lost W "
            "beat fabricates EVT_PROTOCOL 'response before data'")

    # ------------------------------------------------------------------
    # Phase 2: 2-beat burst, AW + first beat same cycle.
    # ------------------------------------------------------------------
    tb.log.info("PHASE 2: same-cycle AW + first beat of a 2-beat burst")
    tb.clear_packets()
    await send_cmd_and_data(tb, txn_id=2, addr=0x2000, length=1, wlast=False)
    await tb.idle(2)
    await tb.send_data(txn_id=2, last=True)
    await tb.idle(2)
    await send_resp(tb, txn_id=2)
    await tb.drain()

    compl = tb.completions()
    errs = tb.errors()
    if len(compl) != 1:
        failures.append(
            f"2: {len(compl)} completion packet(s), expected 1 -- the first "
            "burst beat was lost so the beat count never reached expected_beats")
    if errs:
        failures.append(
            f"2: {len(errs)} spurious error packet(s) "
            f"(codes={[hex(e.event_code) for e in errs]})")
    if tb.beat_overruns:
        failures.append(f"2: beat overruns {tb.beat_overruns[:4]}")

    # ------------------------------------------------------------------
    # Phase 3: control -- AW then W one cycle later (registered path).
    # ------------------------------------------------------------------
    tb.log.info("PHASE 3: control, AW then W a cycle apart")
    tb.clear_packets()
    await tb.send_cmd(txn_id=3, addr=0x3000, length=0)
    await tb.idle(1)
    await tb.send_data(txn_id=3, last=True)
    await tb.idle(2)
    await send_resp(tb, txn_id=3)
    await tb.drain()

    compl = tb.completions()
    errs = tb.errors()
    if len(compl) != 1:
        failures.append(f"3: {len(compl)} completion packet(s), expected 1 "
                        "(registered write-data path regressed)")
    if errs:
        failures.append(f"3: {len(errs)} spurious error packet(s) "
                        f"(codes={[hex(e.event_code) for e in errs]})")

    # ------------------------------------------------------------------
    # Phase 4: bypass must not hijack an open registered entry.
    # AW1 opens a 2-beat burst; beat 1 lands; then AW2 + beat 2 arrive in
    # one cycle. AXI write-data ordering says beat 2 belongs to the OLDEST
    # open entry (AW1), and AW2's own beat follows later.
    # ------------------------------------------------------------------
    tb.log.info("PHASE 4: same-cycle AW while an older burst is still open")
    tb.clear_packets()
    await tb.send_cmd(txn_id=5, addr=0x5000, length=1)      # 2-beat burst
    await tb.idle(1)
    await tb.send_data(txn_id=5, last=False)                # beat 1 of AW1
    # AW2 (single beat) + final beat of AW1 in the same cycle.
    await send_cmd_and_data(tb, txn_id=5, addr=0x6000, length=0, wlast=True)
    await tb.idle(2)
    await send_resp(tb, txn_id=5)                           # B for AW1
    await tb.idle(1)
    await tb.send_data(txn_id=5, last=True)                 # AW2's beat
    await tb.idle(2)
    await send_resp(tb, txn_id=5)                           # B for AW2
    await tb.drain()

    compl = tb.completions()
    errs = tb.errors()
    if len(compl) != 2:
        failures.append(
            f"4: {len(compl)} completion packet(s), expected 2 -- the "
            "same-cycle beat must bind to the oldest OPEN registered entry, "
            "not to the entry allocated that cycle")
    if errs:
        failures.append(f"4: {len(errs)} spurious error packet(s) "
                        f"(codes={[hex(e.event_code) for e in errs]})")

    # No entry may be left stranded in a non-terminal state.
    await tb.idle(10)
    table = tb.read_table()
    stuck = [(i, e['state'], hex(e['addr'])) for i, e in enumerate(table)
             if e['valid'] and e['state'] != TRANS_ERROR]
    if stuck:
        failures.append(f"final: live non-terminal slots remain: {stuck}")

    if failures:
        tb.log.error("=" * 78)
        tb.log.error(f"{len(failures)} same-cycle AW+W failure(s):")
        for f in failures:
            tb.log.error(f"  - {f}")
        tb.log.error("=" * 78)
    assert not failures, (
        f"{len(failures)} same-cycle AW+W failure(s):\n  - "
        + "\n  - ".join(failures))


DEFAULT_SEED = 12345


def generate_test_params():
    """(iw, aw, max_transactions, seed). Directed, deterministic."""
    return [
        (4, 32, 8, DEFAULT_SEED),
        (8, 32, 16, DEFAULT_SEED),   # capped-table config (CMD_ENTRY_RESERVE > 0)
    ]


@pytest.mark.parametrize("iw, aw, max_transactions, seed", generate_test_params())
def test_axi_monitor_wr_same_cycle(iw, aw, max_transactions, seed):
    """Same-cycle AW+W test runner (axi_monitor_base DUT, IS_READ=0)."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_common': 'rtl/common',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "axi_monitor_base"

    # Write-data attribution mechanism, overridable from the environment.
    # Default 0 keeps the standing sweep on the legacy state-predicate select;
    # USE_WDATA_ORDER_Q=1 selects the AWID FIFO, whose empty-queue bypass is
    # exactly what carries the same-cycle AW+W case this file exists to pin.
    # Both go in the build directory name so a run at one setting cannot reuse
    # the other's binary.
    use_wq = int(os.environ.get('USE_WDATA_ORDER_Q', '0'))
    num_banks = int(os.environ.get('NUM_BANKS', '1'))

    test_name = (f"test_{worker_id}_axi_monitor_wr_same_cycle_"
                 f"iw{iw}_aw{aw}_mt{max_transactions}"
                 f"_nb{num_banks}_wq{use_wq}_seed{seed}")
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi_monitor_base.f")

    rtl_parameters = {
        'ID_WIDTH': str(iw),
        'ADDR_WIDTH': str(aw),
        'UNIT_ID': '1',
        'AGENT_ID': '10',
        'MAX_TRANSACTIONS': str(max_transactions),
        'IS_READ': '0',            # WRITE monitor -- the path under test
        'IS_AXI': '1',             # orphan write-data path compiled dead
        'USE_WDATA_ORDER_Q': str(use_wq),
        'NUM_BANKS': str(num_banks),
        'ENABLE_PERF_PACKETS': '0',
        'ENABLE_DEBUG_MODULE': '0',
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'RANDOM_SEED': str(seed),
        'COCOTB_RANDOM_SEED': str(seed),
        'SEED': str(seed),
        'TEST_IW': str(iw),
        'TEST_AW': str(aw),
        'TEST_MAX_TRANS': str(max_transactions),
    }

    compile_args = [
        "--public-flat-rw",
        "--trace-fst",
        "--trace-structs",
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED", "-Wno-DECLFILENAME",
        "-Wno-PINMISSING", "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE",
        "-Wno-TIMESCALEMOD",
    ]

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes + [rtl_dict['rtl_common'], sim_build],
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            plus_args=(['--trace'] if enable_waves else []),
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"✓ PASSED: {test_name}")
    except Exception as e:
        print(f"✗ FAILED: {test_name}")
        print(f"Error: {str(e)}")
        print(f"Log: {log_path}")
        raise
