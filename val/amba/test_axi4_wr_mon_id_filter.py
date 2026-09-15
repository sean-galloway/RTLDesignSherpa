# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: TestAxi4WrMonIdFilter
# Purpose: Enabling the ID filter must not cost an OWNED write its completion
#
# Documentation: vault/handbook/dv/test-structure.md
# Subsystem: dv
"""TASK-073 regression: write monitors ID-filter W beats against the live AWID.

AXI4 dropped WID, so a W beat carries no ID and the four write monitors hand
`axi_monitor_base` the LIVE `m_axi_awid` as `data_id`. With more than one write
outstanding the AW on the bus belongs to a LATER transaction than the W beats in
flight, so `id_owned(data_id)` is evaluated against the wrong ID: an OWNED
transaction's W beats are refused, its data phase never closes, and it never
completes.

WHY THIS IS DIFFERENTIAL, not an absolute count. This stimulus does not complete
all eight writes even with the filter DISABLED -- measured 6 of 8 at 6k clocks
and 7 of 8 at 20k, so some loss is inherent to the traffic and the observation
window, and is NOT this bug. An absolute assertion (`completions == 4`) is red
with the filter off, which would "confirm" any RTL change made against it. So the
test runs the SAME stimulus twice -- filter off, then filter on -- and asserts
that enabling the filter loses no owned transaction that completed without it.
The monitor is passive, so both legs see identical AXI traffic and the baseline
loss cancels.

The filter-off leg is also the armed check: if it yields no owned completions the
DUT is silent and the comparison would pass vacuously, so that is asserted first.
"""
import os
import random

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.axi4.monitor.axi4_master_monitor_tb import AXI4MasterMonitorTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, sim_build_path

OWNED_ID = 0          # id_owned(id) == (id >= base) && (id < base + count)
OWNED_COUNT = 1       # ...so base=0, count=1 owns exactly ID 0
FOREIGN_ID = 1

N_WRITES = 8
ADDR_STRIDE = 0x40
LEG_OFF_BASE = 0x1000   # leg 1: filter disabled
LEG_ON_BASE = 0x8000    # leg 2: filter enabled -- distinct so completions
                        #        from leg 1 can never be miscounted as leg 2's
SETTLE_CLOCKS = 8
DRAIN_CLOCKS = 8000


def _is_owned(i):
    """Even indices carry the owned ID, odd ones the foreign ID."""
    return i % 2 == 0


def _addr(base, i):
    return base + i * ADDR_STRIDE


async def _run_leg(tb, dut, base, filter_on, overlap):
    """Drive N_WRITES interleaved writes; return the owned indices that completed."""
    dut.cfg_id_filter_enable.value = 1 if filter_on else 0
    dut.cfg_id_match_base.value = OWNED_ID
    dut.cfg_id_match_count.value = OWNED_COUNT
    await tb.base_tb.wait_clocks('aclk', SETTLE_CLOCKS)

    before = len(tb.mon_slave.received_packets)

    async def one(i):
        txn_id = OWNED_ID if _is_owned(i) else FOREIGN_ID
        try:
            await tb.base_tb.interface.write_transaction(
                _addr(base, i), 0xA5A50000 | i, id=txn_id)
        except (TypeError, AttributeError, NameError):
            raise                       # a bad call is a bug in this file
        except Exception as e:          # a stalled/dropped txn is under test
            tb.log.debug(f"leg filter_on={filter_on} i={i}: {e}")

    for i in range(N_WRITES):
        cocotb.start_soon(one(i))
    await tb.base_tb.wait_clocks('aclk', DRAIN_CLOCKS)

    pkts = tb.mon_slave.received_packets[before:]
    completed_addrs = {int(p.data) & 0xFFFFFFFF
                       for p in pkts if p.is_completion_packet()}
    owned_done = {i for i in range(N_WRITES)
                  if _is_owned(i) and _addr(base, i) in completed_addrs}

    tb.log.info(
        f"leg filter_on={filter_on}: packets={len(pkts)} "
        f"completions={len(completed_addrs)} owned_completed={sorted(owned_done)} "
        f"w_xfers={overlap['w_xfers']} "
        f"w_xfers_foreign_awid={overlap['w_xfers_foreign_awid']}")
    return owned_done


@cocotb.test(timeout_time=120, timeout_unit="sec")
async def axi4_wr_mon_id_filter_test(dut):
    tb = AXI4MasterMonitorTB(dut, is_write=True, aclk=dut.aclk, aresetn=dut.aresetn)
    await tb.initialize()

    # The monitor TBs initialise eleven cfg_* inputs but NOT the three cfg_id_*
    # ones, so on every other write-monitor test they sit at X and id_owned()'s
    # enable branch is evaluated on an undefined value. Drive them explicitly.
    dut.cfg_timeout_cycles.value = 0xFFFF   # never: a timeout retiring a slot
    dut.cfg_timeout_enable.value = 1        # would drain the table for an
                                            # unrelated reason mid-measurement

    # The bug's precondition is data_valid high while data_id (the LIVE AWID) is
    # foreign. Count it, so a green result cannot be mistaken for "the overlap
    # never happened".
    overlap = {'w_xfers': 0, 'w_xfers_foreign_awid': 0}

    async def _sample():
        while True:
            await RisingEdge(dut.aclk)
            try:
                wv = int(dut.m_axi_wvalid.value)
                wr = int(dut.m_axi_wready.value)
                awid = int(dut.m_axi_awid.value)
            except ValueError:
                continue                    # X/Z during reset
            if wv and wr:
                overlap['w_xfers'] += 1
                if awid != OWNED_ID:
                    overlap['w_xfers_foreign_awid'] += 1

    sampler = cocotb.start_soon(_sample())

    owned_off = await _run_leg(tb, dut, LEG_OFF_BASE, False, overlap)
    owned_on = await _run_leg(tb, dut, LEG_ON_BASE, True, overlap)
    sampler.kill()

    # Armed: without this, a silent DUT makes the comparison below vacuous.
    assert owned_off, (
        "filter-OFF leg produced no owned-ID completions at all, so the "
        "comparison below would pass on a dead DUT")

    assert overlap['w_xfers_foreign_awid'] > 0, (
        f"no W transfer ever coincided with a foreign AWID "
        f"({overlap['w_xfers']} transfers seen), so this stimulus never "
        f"created the condition TASK-073 describes and a pass means nothing")

    lost = sorted(owned_off - owned_on)
    assert not lost, (
        f"enabling the ID filter cost owned-ID write(s) {lost} their "
        f"completion: completed with the filter off {sorted(owned_off)}, with "
        f"it on {sorted(owned_on)}. The monitor filters W beats against the "
        f"LIVE m_axi_awid, so while an owned transaction's W beats stream a "
        f"later AW (id={FOREIGN_ID}) is on the bus and id_owned() refuses "
        f"them; the data phase never closes. "
        f"{overlap['w_xfers_foreign_awid']} of {overlap['w_xfers']} W "
        f"transfers occurred with a foreign AWID. TASK-073.")


@pytest.mark.parametrize("id_width, addr_width, data_width, max_trans", [(8, 32, 32, 16)])
def test_axi4_wr_mon_id_filter(id_width, addr_width, data_width, max_trans):
    """TASK-073: the write-data channel must not be ID-filtered."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi4': 'rtl/amba/axi4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
        'rtl_shared': 'rtl/amba/shared',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "axi4_master_wr_mon"
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name = f"test_{worker_id}_{dut_name}_idfilt_iw{id_width}_mt{max_trans}_{reg_level}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi4_master_wr_mon.f")
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    rtl_parameters = {
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'MAX_TRANSACTIONS': str(max_trans),
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_LEVEL': 'func',
        'TEST_ID_WIDTH': str(id_width),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_STUB': '0',
        'SEED': os.environ.get('SEED', '20260915'),  # PINNED: a regression must replay
        'TEST_CLK_PERIOD': '10',
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
        module="test_axi4_wr_mon_id_filter",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=enable_waves,
        plus_args=(['--trace'] if enable_waves else []),
        keep_files=True,
        compile_args=compile_args,
        # Pinned: this module holds exactly one cocotb test and must not be
        # swept into the standing axi4_master_wr_mon matrix.
        testcase="axi4_wr_mon_id_filter_test",
    )
