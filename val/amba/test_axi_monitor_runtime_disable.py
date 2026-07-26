# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi_monitor_runtime_disable
# Purpose: runtime-disable slot-leak regression (reporter auto-retire)
#
# Documentation: docs/markdown/rtl-amba/index.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-07-21

"""
Runtime-disable slot-leak regression for axi_monitor_reporter auto-retire.

The reporter's auto-retire originally covered only packet classes COMPILED OUT
(!ENABLE_*_LOGIC). A class compiled IN but RUNTIME-disabled (e.g.
ENABLE_COMPL_LOGIC=1 with cfg_compl_enable=0 -- the documented "performance
mode") never marked its terminal entries reported, so trans_mgr never freed
them: the table pinned at MAX_TRANSACTIONS and block_ready wedged low for the
rest of the session, stalling the monitored command channel permanently.

Two leak paths are locked in here:

  Phase A -- steady-state runtime disable. cfg_compl_enable=0 from the start,
             drive > MAX clean transactions. Every completion is terminal and
             unreportable; without the fix each one leaks a slot and
             block_ready never recovers once traffic stops.

  Phase B -- FIFO-backpressure enable-toggle. cfg_compl_enable=1 with
             monbus_ready=0 until the reporter FIFO is full, so later
             completions cannot be accepted (marked); then disable the class.
             The unmarked TRANS_COMPLETE entries are the ones a one-shot
             (edge-triggered) retire check would miss -- retirement must be
             CONTINUOUS over the runtime disable.

Documented, accepted consequence of the fix: toggling an enable mid-flight may
drop that one entry's packet. This test therefore asserts slot recovery
(active_count drains to 0, block_ready re-asserts), never packet counts across
the disable window.
"""

import os

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist


async def _wait_recovery(tb, max_cycles=1000):
    """Wait for block_ready to re-assert AND the table to fully drain."""
    for _ in range(max_cycles):
        if int(tb.dut.block_ready.value) == 1 and int(tb.dut.active_count.value) == 0:
            return True
        await RisingEdge(tb.dut.aclk)
    return False


async def phase_runtime_disabled_compl(tb) -> list:
    """Phase A: compl compiled IN, runtime-disabled, > MAX clean reads."""
    failures = []
    tb.log.info("PHASE A: cfg_compl_enable=0 steady state, drive > MAX transactions")

    depth = len(tb.read_table())
    id_mask = (1 << int(tb.dut.cmd_id.value.n_bits)) - 1

    tb.clear_packets()
    tb.dut.cfg_compl_enable.value = 0     # runtime disable, logic compiled in
    tb.dut.cfg_error_enable.value = 1
    await tb.idle(2)

    # Emulate the wrapper gating: cmd_ready = block_ready.
    async def honor_block_ready():
        while True:
            tb.dut.cmd_ready.value = int(tb.dut.block_ready.value)
            await RisingEdge(tb.dut.aclk)

    gate = cocotb.start_soon(honor_block_ready())
    await tb.idle(2)

    n_txns = depth * 3
    for i in range(n_txns):
        await tb.send_cmd(txn_id=i & id_mask, addr=0x1000 + (i << 8), length=0)
        await tb.idle(1)
        await tb.send_data(txn_id=i & id_mask, last=True)
        await tb.idle(1)

    gate.kill()
    tb.dut.cmd_valid.value = 0
    tb.dut.data_valid.value = 0
    tb.dut.cmd_ready.value = 1

    recovered = await _wait_recovery(tb)
    final_count = int(tb.dut.active_count.value)
    final_block = int(tb.dut.block_ready.value)
    if not recovered:
        failures.append(
            f"A: runtime-disabled completion class leaked table slots: after "
            f"{n_txns} clean transactions and idle drain, active_count="
            f"{final_count}/{depth}, block_ready={final_block} -- terminal "
            "entries with cfg_compl_enable=0 were never auto-retired")
    else:
        tb.log.info(f"A: recovered, active_count={final_count}, block_ready={final_block}")

    # No completion packets may be emitted while the class is disabled.
    compl = tb.completions()
    if compl:
        failures.append(
            f"A: {len(compl)} completion packet(s) emitted with cfg_compl_enable=0")

    tb.dut.cfg_compl_enable.value = 1
    await tb.drain()
    return failures


async def phase_backpressure_toggle(tb) -> list:
    """Phase B: enable ON -> FIFO backpressure -> enable OFF must not leak."""
    failures = []
    tb.log.info("PHASE B: FIFO-backpressure then runtime disable (toggle leak path)")

    depth = len(tb.read_table())
    id_mask = (1 << int(tb.dut.cmd_id.value.n_bits)) - 1

    tb.clear_packets()
    tb.dut.cfg_compl_enable.value = 1
    tb.dut.monbus_ready.value = 0         # jam the monbus: FIFO fills, then
    await tb.idle(2)                      # completions stop being marked

    async def honor_block_ready():
        while True:
            tb.dut.cmd_ready.value = int(tb.dut.block_ready.value)
            await RisingEdge(tb.dut.aclk)

    gate = cocotb.start_soon(honor_block_ready())
    await tb.idle(2)

    # Enough completions to overrun INTR_FIFO_DEPTH (8) + output register:
    # the overflow entries sit TRANS_COMPLETE and UNMARKED.
    n_txns = depth * 3
    for i in range(n_txns):
        await tb.send_cmd(txn_id=i & id_mask, addr=0x2000 + (i << 8), length=0)
        await tb.idle(1)
        await tb.send_data(txn_id=i & id_mask, last=True)
        await tb.idle(1)

    gate.kill()
    tb.dut.cmd_valid.value = 0
    tb.dut.data_valid.value = 0
    tb.dut.cmd_ready.value = 1
    await tb.idle(4)

    table = tb.read_table()
    unmarked = [i for i, e in enumerate(table)
                if e['valid'] and not e['event_reported']]
    tb.log.info(f"B: before disable: active_count={int(tb.dut.active_count.value)}, "
                f"{len(unmarked)} live unmarked slot(s) {unmarked}")

    # The toggle: disable the class while its unemitted entries are stranded
    # behind the full FIFO. Then release the monbus so the already-queued
    # packets drain (their slots were marked at FIFO-write time).
    tb.dut.cfg_compl_enable.value = 0
    await tb.idle(4)
    tb.dut.monbus_ready.value = 1

    recovered = await _wait_recovery(tb)
    final_count = int(tb.dut.active_count.value)
    final_block = int(tb.dut.block_ready.value)
    if not recovered:
        failures.append(
            f"B: enable-toggle under FIFO backpressure leaked table slots: "
            f"active_count={final_count}/{depth}, block_ready={final_block} -- "
            "entries that completed while enabled but lost the FIFO race were "
            "stranded when the class was disabled (retire check must be "
            "continuous, not edge-triggered)")
    else:
        tb.log.info(f"B: recovered, active_count={final_count}, block_ready={final_block}")

    tb.dut.cfg_compl_enable.value = 1
    await tb.drain()
    return failures


@cocotb.test(timeout_time=120, timeout_unit="sec")
async def axi_monitor_runtime_disable_test(dut):
    """Runtime-disable auto-retire regression (E1)."""
    # Reuse the trans_mgr TB (same DUT: axi_monitor_base, IS_READ=1) --
    # stimulus helpers, table decode and drain() are identical requirements
    # here. Imported lazily: at pytest-collection time val/amba is not on
    # sys.path, but cocotb's python_search puts it there at sim time.
    from test_axi_monitor_trans_mgr import AxiMonitorTransMgrTB
    tb = AxiMonitorTransMgrTB(dut)
    await tb.setup_clocks_and_reset()

    all_failures = []
    all_failures += await phase_runtime_disabled_compl(tb)
    all_failures += await phase_backpressure_toggle(tb)

    if all_failures:
        tb.log.error("=" * 78)
        tb.log.error(f"{len(all_failures)} runtime-disable failure(s):")
        for f in all_failures:
            tb.log.error(f"  - {f}")
        tb.log.error("=" * 78)
    else:
        tb.log.info("All runtime-disable checks passed")

    assert not all_failures, (
        f"{len(all_failures)} runtime-disable failure(s):\n  - "
        + "\n  - ".join(all_failures))


DEFAULT_SEED = 12345


def generate_test_params():
    """(iw, aw, max_transactions, seed). Deterministic: directed stimulus."""
    return [
        (4, 32, 8, DEFAULT_SEED),
    ]


@pytest.mark.parametrize("iw, aw, max_transactions, seed", generate_test_params())
def test_axi_monitor_runtime_disable(iw, aw, max_transactions, seed):
    """Runtime-disable auto-retire test runner (axi_monitor_base DUT)."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_common': 'rtl/common',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "axi_monitor_base"
    test_name = (f"test_{worker_id}_axi_monitor_runtime_disable_"
                 f"iw{iw}_aw{aw}_mt{max_transactions}_seed{seed}")
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
        'IS_READ': '1',
        'IS_AXI': '1',
        # The classes under test are all COMPILED IN (defaults) -- runtime
        # disable is the whole point of this suite.
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
