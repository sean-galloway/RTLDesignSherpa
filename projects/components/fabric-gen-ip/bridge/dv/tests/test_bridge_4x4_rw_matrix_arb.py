#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): bridge TASK-015, matrix arbitration with more
# than two requesters -- bridge_4x4_rw_matrix (bridge_4x4_rw with
# `arbitration = "matrix"`). Three masters reach periph_slave (32-bit): cpu
# (64-bit), dma0 (32-bit) and gpu (256-bit); dma1 is not connected to it. All
# three stream bursts at it against a slave that takes one AW per AW_HOLD+1
# cycles, and the grant order is read off periph's AWID (its top two bits are
# the master index). A matrix arbiter serves the least recently served
# requester, so with three persistent requesters no master waits more than
# TWO foreign grants between two of its own, and each gets about a third.
# The width converters sit between the masters and the arbiter: each master
# burst still reaches the slave as one AW, so grants count bursts.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from bridge4x4_rw_matrix_tb import Bridge4x4RwMatrixTB
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from bridge_perf_probe import BEATS, saturate, stream_writes, report
from bridge_arb_fairness import GrantLog

CPU, DMA0, DMA1, GPU = 0, 1, 2, 3
MASTERS = (CPU, DMA0, GPU)                        # the masters periph_slave is connected to
SIZE = {CPU: 3, DMA0: 2, GPU: 5}                  # AWSIZE: bus-wide beats (64 / 32 / 256 bits)
PERIPH = 0
PERIPH_BASE = 0x0000_0000
PERIPH_PFX = 'periph_slave_axi'
ID_W, BRIDGE_ID_W = 6, 2                          # bridge_4x4_rw_matrix_pkg
BURSTS = {'gate': 8, 'func': 16, 'full': 24}      # gpu's 512-byte bursts stay inside its 16 KB slot
SLOT = {CPU: 0, DMA0: 1, GPU: 2}                  # 16 KB of the slave's 64 KB seeded model each
AW_HOLD = 12
WAIT_BOUND = len(MASTERS) - 1                     # matrix: n-1 foreign grants, n persistent requesters
SHARE_FLOOR = 0.75 / len(MASTERS)                 # three-quarters of an equal share


def _hold_aw(tb, slave, hold):
    tb.slave_wr[slave].aw_channel.set_randomizer(FlexRandomizer({'ready_delay': ([(hold, hold)], [1])}))


def _plan(master, n, tag):
    """n bus-wide bursts for `master` inside its own 16 KB slot of the slave's
    64 KB seeded model (bridge_perf_probe.write_plan assumes two masters of
    4-byte beats; three masters, one of them 256-bit, need their own map)."""
    bb = 1 << SIZE[master]
    return [(master, PERIPH_BASE + 0x4000 * SLOT[master] + i * BEATS * bb,
             [(tag << 24) | (master << 16) | (i << 4) | k for k in range(BEATS)])
            for i in range(n)]


@cocotb.test(timeout_time=40000, timeout_unit="ms")
async def cocotb_test_bridge_4x4_rw_matrix_fair(dut):
    tb = Bridge4x4RwMatrixTB(dut)
    await tb.setup_clocks_and_reset()
    saturate(tb)
    _hold_aw(tb, PERIPH, AW_HOLD)
    n = BURSTS[tb.level]
    g = GrantLog(tb, PERIPH_PFX, ID_W, BRIDGE_ID_W).start()
    errors = []
    plan = sum((_plan(m, n, 0xB0 + m) for m in MASTERS), [])
    await stream_writes(tb, plan, errors, size=SIZE)
    assert not errors, errors[:5]
    share, worst, total, span, idle = g.analyze(MASTERS)
    names = {CPU: 'cpu', DMA0: 'dma0', GPU: 'gpu'}
    report(tb, "matrix 4x4 three-way", grants_in_window=total, window_cycles=span, longest_slot_gap=idle,
           **{f"{names[m]}_share": share[m] for m in MASTERS},
           **{f"{names[m]}_worst_wait": worst.get(m, 0) for m in MASTERS})
    assert total >= 2 * len(MASTERS), f"contended window too short to judge ({total} grants)"
    failures = []
    for m in MASTERS:
        if share[m] < SHARE_FLOOR:
            failures.append(f"{names[m]} got {share[m]:.3f} of the contended grants (floor {SHARE_FLOOR:.3f})")
        if worst.get(m, 0) > WAIT_BOUND:
            failures.append(f"{names[m]} waited {worst[m]} foreign grants between two of its own; "
                            f"the matrix bounds it at {WAIT_BOUND}")
    assert not failures, f"{len(failures)} failure(s):\n  " + "\n  ".join(failures)
    tb.log.info("bridge TASK-015 matrix 4x4 PASSED: least recently served, bounded wait, equal shares")


def _run(request, test_level, testcase):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_4x4_rw_matrix"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/fabric-gen-ip/bridge/rtl/filelists/{dut_name}.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_{testcase}_{test_level}_{reg_level}"
    sim_build_name = f"{test_name_plus_params}{worker_suffix}"
    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = sim_build_path(tests_dir, sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    waves = get_wave_config(sim_build)
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase=f"cocotb_test_bridge_4x4_rw_matrix_{testcase}",
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert', '--coverage'] + waves['extra_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            **level_env(test_level),
            **waves['extra_env'],
        },
        plus_args=waves['sim_args'],
        keep_files=True,
    )


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_4x4_rw_matrix_fair(request, test_level):
    _run(request, test_level, "fair")
