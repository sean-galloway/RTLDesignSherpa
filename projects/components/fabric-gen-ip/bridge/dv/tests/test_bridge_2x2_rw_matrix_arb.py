#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): bridge TASK-015, matrix arbitration on
# bridge_2x2_rw_matrix (bridge_2x2_rw with `arbitration = "matrix"`).
#
# Each slave arbiter keeps one "i outranks j" bit per master pair; the
# requester outranking every other requester wins and drops below everyone
# at its handshake, so the least recently served requester always wins a
# contended slot. With two persistent requesters that is strict alternation:
# no master waits more than ONE foreign grant between two of its own, each
# gets half the grants, and the port never idles. The grant order is read
# off the slave port's AWID (its top bit is the master index), inside the
# contended window, against a slave that holds AWREADY off for AW_HOLD cycles
# per AW so a backlog forms and every slot is an arbitration (as in the QoS
# test: a slave that takes every AW on arrival never lets two requests meet).

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

from bridge2x2_rw_matrix_tb import Bridge2x2RwMatrixTB
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from bridge_perf_probe import BEATS, Sampler, saturate, write_plan, stream_writes, report
from bridge_arb_fairness import GrantLog

CPU, DMA = 0, 1
MASTERS = (CPU, DMA)
DDR = 0
DDR_BASE = 0x0000_0000
DDR_PFX = 'ddr_s_axi'
ID_W, BRIDGE_ID_W = 5, 1                 # bridge_2x2_rw_matrix_pkg: XBAR_ID_WIDTH, BRIDGE_ID_WIDTH
BURSTS = {'gate': 8, 'func': 32, 'full': 96}
AW_HOLD = 12                             # ddr takes one AW per AW_HOLD+1 cycles
WAIT_BOUND = len(MASTERS) - 1            # matrix: at most n-1 foreign grants between two own grants
SHARE_FLOOR = 0.40                       # the round-robin baseline figure (QoS test, equal phase)
SATURATED_FLOOR = 0.95                   # W beats per cycle at the shared port


def _hold_aw(tb, slave, hold):
    tb.slave_wr[slave].aw_channel.set_randomizer(FlexRandomizer({'ready_delay': ([(hold, hold)], [1])}))


@cocotb.test(timeout_time=20000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_matrix_fair(dut):
    tb = Bridge2x2RwMatrixTB(dut)
    await tb.setup_clocks_and_reset()
    saturate(tb)
    _hold_aw(tb, DDR, AW_HOLD)
    n = BURSTS[tb.level]
    s = Sampler(tb, {'s_w': (DDR_PFX, 'w')}).start()
    g = GrantLog(tb, DDR_PFX, ID_W, BRIDGE_ID_W).start()
    errors = []
    plan = write_plan(CPU, DDR_BASE, n, 0xA0) + write_plan(DMA, DDR_BASE, n, 0xA1)
    await stream_writes(tb, plan, errors)
    assert not errors, errors[:5]
    beats, _cycles, rate = s.window_rate('s_w')
    assert beats == 2 * n * BEATS, f"{beats} W beats at the slave, expected {2 * n * BEATS}"
    share, worst, total, span, idle = g.analyze(MASTERS)
    report(tb, "matrix 2x2 equal", w_beats_per_cycle=rate, grants_in_window=total, window_cycles=span,
           cpu_share=share[CPU], dma_share=share[DMA], cpu_worst_wait=worst.get(CPU, 0),
           dma_worst_wait=worst.get(DMA, 0), longest_slot_gap=idle)
    assert total >= 4, f"contended window too short to judge ({total} grants)"
    failures = []
    if rate < SATURATED_FLOOR:
        failures.append(f"port not saturated: {rate:.3f} W beats/cycle (floor {SATURATED_FLOOR})")
    for m, name in ((CPU, 'cpu'), (DMA, 'dma')):
        if share[m] < SHARE_FLOOR:
            failures.append(f"{name} got {share[m]:.3f} of the contended grants (floor {SHARE_FLOOR})")
        if worst.get(m, 0) > WAIT_BOUND:
            failures.append(f"{name} waited {worst[m]} foreign grants between two of its own; "
                            f"the matrix bounds it at {WAIT_BOUND}")
    assert not failures, f"{len(failures)} failure(s):\n  " + "\n  ".join(failures)
    tb.log.info("bridge TASK-015 matrix 2x2 PASSED: strict alternation, equal shares, port saturated")


def _run(request, test_level, testcase):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_rw_matrix"
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
        testcase=f"cocotb_test_bridge_2x2_rw_matrix_{testcase}",
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
def test_bridge_2x2_rw_matrix_fair(request, test_level):
    _run(request, test_level, "fair")
