# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi4_master_rd_mon_cfg
# Purpose: wrapper config-port regression (E5) -- cfg_monitor_enable /
#          cfg_timeout_cycles / ACTIVE_TRANS_THRESHOLD / count outputs
#
# Documentation: docs/markdown/RTLAmba/index.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-07-21

"""
Wrapper configuration-port regression for axi4_master_rd_mon (E5).

The wrapper API had four dead ends, locked in here:

  * cfg_monitor_enable was a port connected to NOTHING. It is now the master
    runtime gate: 0 = monitor inert (no allocation, CAM held clear,
    block_ready forced high so the datapath is never stalled), 1 = normal.

  * cfg_timeout_cycles was a port connected to NOTHING while the base's real
    knobs (cfg_addr/data/resp_cnt) were hardwired 4'd15. It now drives all
    three as the unified coarse control: 0 -> 4'hF (legacy default),
    1..15 -> that many timer ticks, >15 -> saturate at 4'hF.

  * cfg_active_trans_threshold was hardwired 16'd8 no matter the table size.
    It is now the ACTIVE_TRANS_THRESHOLD parameter, default
    MAX_TRANSACTIONS/2.

  * error_count / transaction_count outputs were hardwired '0. They now come
    from the base monitor's lifetime reporter counters.

Structural checks peek at internal signals via --public-flat-rw (precedent:
test_axi_monitor_trans_mgr.py) because pre-fix these nets/parameters simply
did not exist -- the peek itself is the fail-before proof. The 'thresh0'
config additionally overrides ACTIVE_TRANS_THRESHOLD=0 (compile fails on
pre-fix RTL where the parameter does not exist) and proves the threshold
cone fires end-to-end through the parameter.
"""

import os

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.axi4.monitor.axi4_master_monitor_tb import AXI4MasterMonitorTB
from TBClasses.monbus.monbus_types import PktType
from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=60, timeout_unit="sec")
async def axi4_master_rd_mon_cfg_test(dut):
    """E5 wrapper config-port regression."""
    thresh_mode = os.environ.get('TEST_THRESH_MODE', 'default')
    max_trans = int(os.environ.get('TEST_MAX_TRANS', '32'))

    tb = AXI4MasterMonitorTB(dut, is_write=False, aclk=dut.aclk, aresetn=dut.aresetn)
    await tb.initialize()
    tb.base_tb.set_timing_profile('normal')
    failures = []

    def packets():
        return list(tb.mon_slave.received_packets)

    def count_type(ptype):
        return sum(1 for p in packets()
                   if getattr(p, 'pkt_type', None) == ptype)

    if thresh_mode == 'thresh0':
        # --------------------------------------------------------------
        # Threshold positive control: ACTIVE_TRANS_THRESHOLD=0 override
        # means ANY in-flight transaction is over threshold, so with the
        # cone enabled clean traffic must produce threshold packets --
        # proving the wrapper parameter reaches the base monitor.
        # --------------------------------------------------------------
        dut.cfg_threshold_enable.value = 1
        await tb.base_tb.wait_clocks('aclk', 2)
        for i in range(10):
            success, _, _ = await tb.base_tb.single_read_test(0x3000 + i * 0x40)
            if not success:
                failures.append(f"thresh0: read #{i} failed")
                break
        await tb.base_tb.wait_clocks('aclk', 200)
        n_thresh = count_type(PktType.PktTypeThreshold)
        tb.log.info(f"thresh0: {n_thresh} threshold packet(s)")
        if n_thresh == 0:
            failures.append(
                "thresh0: ACTIVE_TRANS_THRESHOLD=0 with threshold enabled "
                "produced no threshold packets -- parameter not wired through")
    else:
        # --------------------------------------------------------------
        # Phase 1: threshold default sizing (ACTIVE_TRANS_THRESHOLD =
        # MAX_TRANSACTIONS/2). Clean low-outstanding traffic with the
        # cone enabled must be quiet. (Verilator does not expose the
        # generate-scope hierarchy to cocotb, so the parameter's
        # propagation into the base is proven by the 'thresh0' config,
        # whose override makes the cone fire end-to-end.)
        # --------------------------------------------------------------
        dut.cfg_threshold_enable.value = 1
        await tb.base_tb.wait_clocks('aclk', 2)
        for i in range(10):
            success, _, _ = await tb.base_tb.single_read_test(0x1000 + i * 0x40)
            if not success:
                failures.append(f"1: read #{i} failed")
                break
        await tb.base_tb.wait_clocks('aclk', 100)
        n_thresh = count_type(PktType.PktTypeThreshold)
        if n_thresh:
            failures.append(
                f"1: {n_thresh} threshold packet(s) at default sizing on "
                "low-outstanding clean traffic (threshold spam)")
        dut.cfg_threshold_enable.value = 0

        # --------------------------------------------------------------
        # Phase 2: cfg_timeout_cycles -> per-phase tick-count mapping.
        # The mapping net w_timeout_cnt did not exist pre-fix, and the
        # base's cnt inputs were hardwired 15 regardless of the port.
        # --------------------------------------------------------------
        mapping = [(0, 15), (1, 1), (5, 5), (15, 15), (16, 15), (1000, 15)]
        for cycles, expect in mapping:
            dut.cfg_timeout_cycles.value = cycles
            await tb.base_tb.wait_clocks('aclk', 1)
            got = int(dut.w_timeout_cnt.value)
            if got != expect:
                failures.append(
                    f"2: cfg_timeout_cycles={cycles} -> w_timeout_cnt={got}, "
                    f"expected {expect}")
        dut.cfg_timeout_cycles.value = 1000

        # --------------------------------------------------------------
        # Phase 3: cfg_monitor_enable=0 -> inert and never blocking.
        # --------------------------------------------------------------
        pre_packets = len(packets())
        if pre_packets == 0:
            failures.append("3: sanity -- no packets while enabled")

        dut.cfg_monitor_enable.value = 0
        await tb.base_tb.wait_clocks('aclk', 50)   # let in-flight packets drain
        tb.mon_slave.received_packets.clear()

        for i in range(6):
            success, _, _ = await tb.base_tb.single_read_test(0x2000 + i * 0x40)
            if not success:
                failures.append(
                    f"3: read #{i} FAILED with monitor disabled -- a disabled "
                    "monitor must never stall the datapath")
                break
        await tb.base_tb.wait_clocks('aclk', 100)

        n_disabled = len(packets())
        if n_disabled:
            failures.append(
                f"3: {n_disabled} monitor packet(s) while cfg_monitor_enable=0 "
                "-- the runtime gate is not wired")
        act = int(dut.active_transactions.value)
        if act != 0:
            failures.append(
                f"3: active_transactions={act} while disabled -- CAM not held clear")

        # Re-enable: clean restart, packets flow again.
        dut.cfg_monitor_enable.value = 1
        await tb.base_tb.wait_clocks('aclk', 5)
        for i in range(3):
            success, _, _ = await tb.base_tb.single_read_test(0x4000 + i * 0x40)
            if not success:
                failures.append(f"3: re-enable read #{i} failed")
                break
        await tb.base_tb.wait_clocks('aclk', 100)
        if len(packets()) == 0:
            failures.append("3: no packets after re-enable -- monitor did not restart")

        # --------------------------------------------------------------
        # Phase 4: count outputs move. transaction_count tracks emitted
        # completion packets; error_count stays 0 on clean traffic.
        # --------------------------------------------------------------
        txn_count = int(dut.transaction_count.value)
        err_count = int(dut.error_count.value)
        tb.log.info(f"4: transaction_count={txn_count} error_count={err_count}")
        if txn_count == 0:
            failures.append(
                "4: transaction_count=0 after completed reads -- output still "
                "hardwired instead of driven from the reporter counters")
        if err_count != 0:
            failures.append(f"4: error_count={err_count} on clean traffic")

    if failures:
        tb.log.error("=" * 78)
        tb.log.error(f"{len(failures)} wrapper-config failure(s):")
        for f in failures:
            tb.log.error(f"  - {f}")
        tb.log.error("=" * 78)
    assert not failures, (
        f"{len(failures)} wrapper-config failure(s):\n  - "
        + "\n  - ".join(failures))


def generate_test_params():
    """(id_w, addr_w, data_w, user_w, max_trans, thresh_mode, seed)."""
    return [
        (8, 32, 32, 1, 32, 'default', 12345),
        (8, 32, 32, 1, 32, 'thresh0', 12345),
    ]


@pytest.mark.parametrize(
    "id_width, addr_width, data_width, user_width, max_trans, thresh_mode, seed",
    generate_test_params())
def test_axi4_master_rd_mon_cfg(id_width, addr_width, data_width, user_width,
                                max_trans, thresh_mode, seed):
    """E5 wrapper config-port test runner."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi4': 'rtl/amba/axi4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
        'rtl_shared': 'rtl/amba/shared',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "axi4_master_rd_mon"
    test_name = f"test_{worker_id}_{dut_name}_cfg_mt{max_trans}_{thresh_mode}_seed{seed}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi4_master_rd_mon.f")

    rtl_parameters = {
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': str(user_width),
        'UNIT_ID': '1',
        'AGENT_ID': '10',
        'MAX_TRANSACTIONS': str(max_trans),
        'ENABLE_FILTERING': '1',
        'SKID_DEPTH_AR': '2',
        'SKID_DEPTH_R': '4',
    }
    if thresh_mode == 'thresh0':
        # Fails to elaborate on pre-fix RTL: the parameter did not exist.
        rtl_parameters['ACTIVE_TRANS_THRESHOLD'] = '0'

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_ID_WIDTH': str(id_width),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_STUB': '0',
        'RANDOM_SEED': str(seed),
        'COCOTB_RANDOM_SEED': str(seed),
        'SEED': str(seed),
        'TEST_CLK_PERIOD': '10',
        'TEST_THRESH_MODE': thresh_mode,
        'TEST_MAX_TRANS': str(max_trans),
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
            module=os.path.basename(__file__).replace(".py", ""),
            testcase="axi4_master_rd_mon_cfg_test",
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
