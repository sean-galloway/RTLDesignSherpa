#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-017 QoS-with-aging arbitration.
#
# bridge_2x2_rw_qos is bridge_2x2_rw with `arbitration = "qos"`: each slave
# arbiter picks the requester with the highest effective priority (AxQOS +
# an age term, one level per 2**4 waiting cycles, saturating at 15) and
# shares round-robin among equals. Three things define that and each is
# asserted per master over the contended window (an aggregate cannot see
# one master starved):
#
#   priority   a QoS-8 stream against a QoS-0 stream at one slave port: the
#              high-QoS master gets most of the beats -- and it is QoS, not
#              the port index, so the phase runs both ways round;
#   no starve  the QoS-0 master still completes every burst, and the longest
#              gap between its W beats is bounded by what aging promises:
#              at most 15 levels x 16 cycles before it ties at 15, plus the
#              burst in flight;
#   equal      equal QoS shares the port like the round-robin baseline
#              (0.4 <= share), and the port stays saturated throughout.
#
# Priority can only reorder what is WAITING at the arbiter. A slave that
# accepts an AW every cycle takes each master's AW the moment it arrives --
# faster than either master issues them -- so the arbiter never sees two
# requests at once and the W order is plain arrival order (measured: 0.52 /
# 0.48 with a free-running slave). Real slaves hold a bounded number of
# writes outstanding and backpressure AW beyond it; the phases model that by
# holding the ddr port's AWREADY off for AW_HOLD cycles per AW, so a backlog
# forms and every AW slot is an arbitration. The share is measured on the W
# beats the port serves; starvation on the AW grants, which is what aging
# promises (the W beats behind a grant queue in AW order).

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

from projects.components.bridge.dv.tbclasses.bridge2x2_rw_qos_tb import Bridge2x2RwQosTB
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from projects.components.bridge.dv.tbclasses.bridge_perf_probe import (
    BEATS, Sampler, saturate, write_plan, stream_writes, report,
)

CPU, DMA = 0, 1
DDR = 0                                           # slave index of the contended port
DDR_BASE = 0x0000_0000
MASTER_PFX = {CPU: 'cpu_m_axi', DMA: 'dma_m_axi'}
BURSTS = {'gate': 8, 'func': 32, 'full': 96}
AGING_SHIFT = 4                                   # qos_aging_shift in the fixture
AW_HOLD = 12               # ddr accepts one AW per AW_HOLD+1 cycles: outstanding-limited slave
# Worst wait aging allows a QoS-0 requester behind a QoS-15 one: 15 levels
# to tie, then one round-robin turn; plus the burst the winner is streaming.
STARVE_BOUND = 15 * (1 << AGING_SHIFT) + 3 * (AW_HOLD + 1)   # aging to a tie, then an AW slot and the RR turn

HIGH_SHARE_FLOOR = 0.75    # high-QoS master's share of the contended beats
EQUAL_SHARE_FLOOR = 0.40   # min share with equal QoS (the rr baseline figure)
SATURATED_FLOOR = 0.95     # W beats/cycle at the shared port, equal-QoS phase
# When one master wins every slot it streams its own bursts back to back, and
# the requester BFM leaves one idle W cycle between two bursts of the same
# master (the next burst's W starts the cycle after the previous WLAST is
# handed over). Round-robin alternation hides that cycle behind the other
# master's beats; priority exposes it: 16 beats per ~17 cycles, 0.93
# measured, and a second bubble where the loser's burst is spliced in
# (1.0 idle cycle per burst at gate, 1.4 at func). The port itself never
# stalls a beat, so the priority phases take a floor of 0.90 and
# additionally bound the port's idle cycles to two per burst served -- the
# requester's bubbles and nothing else.
PRIORITY_RATE_FLOOR = 0.90
IDLE_PER_BURST = 2


def _hold_aw(tb, slave, hold):
    """The slave accepts one AW per hold+1 cycles: a slave with its
    outstanding-write depth full, so AWs queue at the arbiter."""
    tb.slave_wr[slave].aw_channel.set_randomizer(FlexRandomizer({'ready_delay': ([(hold, hold)], [1])}))


async def _contend(tb, n, qos_cpu, qos_dma, tag):
    """Both masters stream n bursts to ddr with the given QoS; returns
    (rate at the slave port, cpu share, dma share, worst dma AW gap, worst cpu AW gap, window)."""
    _hold_aw(tb, DDR, AW_HOLD)
    s = Sampler(tb, {'s_w': ('ddr_s_axi', 'w'),
                     'cpu_w': (MASTER_PFX[CPU], 'w'), 'dma_w': (MASTER_PFX[DMA], 'w'),
                     'cpu_aw': (MASTER_PFX[CPU], 'aw'), 'dma_aw': (MASTER_PFX[DMA], 'aw')}).start()
    errors = []
    plan = write_plan(CPU, DDR_BASE, n, tag) + write_plan(DMA, DDR_BASE, n, tag + 1)
    await stream_writes(tb, plan, errors, qos={CPU: qos_cpu, DMA: qos_dma})
    assert not errors, errors[:5]
    beats, cycles, rate = s.window_rate('s_w')
    assert beats == 2 * n * BEATS, f"{beats} W beats at the slave, expected {2 * n * BEATS}"
    lo = max(s.marks['cpu_w'][0], s.marks['dma_w'][0])
    hi = min(s.marks['cpu_w'][-1], s.marks['dma_w'][-1])
    cpu_c, dma_c = s.count_in('cpu_w', lo, hi), s.count_in('dma_w', lo, hi)
    tot = cpu_c + dma_c
    assert tot >= 4 * BEATS, f"contended window too short to judge ({tot} beats)"
    _stalled, idle = s.gaps_in('s_w', lo, hi)
    # bursts straddle both window edges, and the loser's first grant costs
    # one round-robin turn: count partial bursts and allow two more
    idle_bound = IDLE_PER_BURST * ((tot + BEATS - 1) // BEATS + 2)
    assert idle <= idle_bound, (
        f"the port sat idle {idle} cycles inside the contended window with {tot} beats served; "
        f"at most one requester bubble per burst ({idle_bound}) is explained")
    # starvation: the longest a master's AW waited for a grant while the
    # other master's AWs were also pending (both still had bursts to issue)
    alo = max(s.marks['cpu_aw'][0], s.marks['dma_aw'][0])
    ahi = min(s.marks['cpu_aw'][-1], s.marks['dma_aw'][-1])
    return (rate, cpu_c / tot, dma_c / tot,
            s.max_gap('dma_aw', alo, ahi), s.max_gap('cpu_aw', alo, ahi), (hi - lo + 1))


@cocotb.test(timeout_time=20000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_qos_priority(dut):
    tb = Bridge2x2RwQosTB(dut)
    await tb.setup_clocks_and_reset()
    saturate(tb)
    n = BURSTS[tb.level]
    failures = []

    # cpu high, dma low
    rate, cpu_s, dma_s, dma_gap, _cpu_gap, win = await _contend(tb, n, 8, 0, 0xA0)
    report(tb, "qos cpu8 vs dma0", beats_per_cycle=rate, cpu_share=cpu_s, dma_share=dma_s,
           dma_worst_gap=dma_gap, contended_cycles=win)
    if rate < PRIORITY_RATE_FLOOR:
        failures.append(f"cpu8/dma0: port not saturated ({rate:.3f} beats/cycle, floor {PRIORITY_RATE_FLOOR})")
    if cpu_s < HIGH_SHARE_FLOOR:
        failures.append(f"cpu8/dma0: high-QoS cpu got {cpu_s:.3f} of the contended beats, floor {HIGH_SHARE_FLOOR}")
    if dma_s <= 0.0:
        failures.append("cpu8/dma0: QoS-0 dma got NO beats inside the contended window -- starved")
    if dma_gap > STARVE_BOUND:
        failures.append(f"cpu8/dma0: QoS-0 dma waited {dma_gap} cycles between AW grants; aging bounds it at {STARVE_BOUND}")

    # dma high, cpu low -- it is the QoS value, not the master index
    rate, cpu_s, dma_s, _dma_gap, cpu_gap, win = await _contend(tb, n, 0, 8, 0xB0)
    report(tb, "qos cpu0 vs dma8", beats_per_cycle=rate, cpu_share=cpu_s, dma_share=dma_s,
           cpu_worst_gap=cpu_gap, contended_cycles=win)
    if rate < PRIORITY_RATE_FLOOR:
        failures.append(f"cpu0/dma8: port not saturated ({rate:.3f} beats/cycle, floor {PRIORITY_RATE_FLOOR})")
    if dma_s < HIGH_SHARE_FLOOR:
        failures.append(f"cpu0/dma8: high-QoS dma got {dma_s:.3f} of the contended beats, floor {HIGH_SHARE_FLOOR}")
    if cpu_gap > STARVE_BOUND:
        failures.append(f"cpu0/dma8: QoS-0 cpu waited {cpu_gap} cycles between AW grants; aging bounds it at {STARVE_BOUND}")

    assert not failures, f"{len(failures)} failure(s):\n  " + "\n  ".join(failures)
    tb.log.info("BRIDGE-017 QoS priority PASSED (both orientations, no starvation)")


@cocotb.test(timeout_time=20000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_qos_equal(dut):
    tb = Bridge2x2RwQosTB(dut)
    await tb.setup_clocks_and_reset()
    saturate(tb)
    n = BURSTS[tb.level]
    rate, cpu_s, dma_s, _dg, _cg, win = await _contend(tb, n, 3, 3, 0xC0)
    report(tb, "qos equal (3/3)", beats_per_cycle=rate, cpu_share=cpu_s, dma_share=dma_s, contended_cycles=win)
    assert rate >= SATURATED_FLOOR, f"equal QoS: port not saturated ({rate:.3f})"
    assert min(cpu_s, dma_s) >= EQUAL_SHARE_FLOOR, (
        f"equal QoS: shares {cpu_s:.3f}/{dma_s:.3f}; equals must share round-robin (floor {EQUAL_SHARE_FLOOR})")
    tb.log.info("BRIDGE-017 QoS equal PASSED: round-robin among equals")


def _run(request, test_level, testcase):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_rw_qos"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/bridge/rtl/filelists/{dut_name}.f')
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
        testcase=f"cocotb_test_bridge_2x2_rw_qos_{testcase}",
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
def test_bridge_2x2_rw_qos_priority(request, test_level):
    _run(request, test_level, "priority")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_qos_equal(request, test_level):
    _run(request, test_level, "equal")
