#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): traffic patterns against offered load
# (bridge TASK-014) -- uniform, permutation and hot-spot, open loop, on the
# combinational and the registered 2x2 and on the mixed-width 4x4.
#
# Per fixture and pattern, every master starts one 4-beat read every `gap`
# cycles at the slave the pattern names. Each point records offered load and
# accepted throughput in SLAVE beats per cycle summed over the targeted slave
# ports, against the capacity of one beat per cycle per targeted port, and
# each master's mean and p95 latency (call to last beat at the requester, so
# queueing in the requester counts once the port's outstanding limit binds).
# Asserted at every point:
#   accepted >= 0.85 * capacity                    the fabric carries what the
#                                                  targeted ports can absorb:
#                                                  capacity = sum over slaves of
#                                                  min(offered at the slave, 1.0),
#                                                  in slave beats (a 64-bit
#                                                  master's 4-beat read is 8 at
#                                                  a 32-bit slave)
#   mean latency <= lightest-load mean + 4 while offered <= capacity / 2
#                                                  no queueing of the fabric's
#                                                  own below saturation
# Under a hot spot the capacity is one port, so latency climbs with the queue
# past offered = 1.0; under a permutation the fabric must carry N flows at
# once, so a serialising stage would show as accepted flattening under N.
#
# UNIFORM traffic past saturation on a fabric WITHOUT response queues
# (bridge TASK-021, measured 2026-10-24/25 at FUNC): a slave returns R in
# its own order, so when its head burst is for a master whose R port the
# other slave is feeding, it stalls -- and the master its NEXT burst was for
# sits idle. Head-of-line blocking on the response path, at the slave's
# output: both slave R channels stalled 31 percent of the cycles while no
# master R port was. bridge_2x2_rw holds 0.80 of capacity at 1.33x offered
# and 0.67 at 2x, bridge_2x2_rw_pipe the same, bridge_4x4_rw 0.61 from 0.9x
# on. Permutation and hot-spot hold 1.00 everywhere. (4- and 8-deep request
# slots measured the identical curve; the master adapter's R mux is a single
# width path on these fixtures: neither is it.)
# The fix is `[bridge] r_queue_depth` (HAS 5.1 / 6.2): a per-(master, slave)
# R queue in the crossbar, so the slave hands a burst for a busy master over
# and serves the next. bridge_2x2_rw_rq8 (8 beats) measures 1.00 of capacity
# at every load point and is held to the full ACCEPT_FLOOR here. On the
# mixed-width bridge_4x4_rw_rq8 the queue keeps a beat's width ahead of the
# unqueued fabric but shares its ~2.55 slave-beats/cycle ceiling past 2x
# offered (bridge TASK-022, measured per cycle 2026-10-25): every slave R
# pin runs 0 percent stalled while sram/gpu_mem starve -- half the uniform
# beats target the 32-bit periph port (7x oversubscribed at gap 2),
# Little's law fills each master's shared 16-entry outstanding table with
# periph reads, and a master's single in-order AR channel then cannot
# supply the idle slaves. Architecturally forced, not a fabric defect, so
# the 4x4 fixtures are held to KNOWN_UNIFORM_FLOOR with the unqueued ones.
# The same measurement caught the driver's own ID rotation (k % 16 against
# a 3-target cycle, so each burst's ID twin sat at a DIFFERENT slave)
# tripping the per-ID same-target gate on 31-58 percent of AR cycles; the
# driver now partitions IDs per target (bridge_perf_patterns.open_loop),
# which is what took the 4x4 from 0.61 to 0.98 of capacity at 1.4x offered.
# The default is 0 -- the minimal fabric, by the owner's rule for every
# depth -- so the unqueued fixtures keep the measured curve and are held to
# KNOWN_UNIFORM_FLOOR past saturation: the cost of the minimum, documented,
# not a defect waiting on a fix.
# GATE runs three load points, FUNC and FULL the whole curve (the default
# is the minimal sweep; the curve is the knob -- bridge TASK-014).
#
#   BRIDGE_PERF_FIXTURE=bridge_2x2_rw_pipe  pytest test_bridge_perf_patterns.py
import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb                                                       # noqa: E402
from cocotb_test.simulator import run                               # noqa: E402
from TBClasses.shared.utilities import get_paths, get_wave_config   # noqa: E402
from TBClasses.shared.filelist_utils import get_sources_from_filelist  # noqa: E402
from TBClasses.shared.test_levels import level_env, reg_level_grid  # noqa: E402

from bridge2x2_rw_tb import Bridge2x2RwTB                           # noqa: E402
from bridge2x2_rw_pipe_tb import Bridge2x2RwPipeTB                  # noqa: E402
from bridge2x2_rw_rq8_tb import Bridge2x2RwRq8TB                    # noqa: E402
from bridge4x4_rw_tb import Bridge4x4RwTB                           # noqa: E402
from bridge4x4_rw_rq8_tb import Bridge4x4RwRq8TB                    # noqa: E402
from bridge_perf_probe import saturate, report                      # noqa: E402
from bridge_perf_patterns import Roles, PATTERNS, sweep, table      # noqa: E402

FIXTURES = {'bridge_2x2_rw': Bridge2x2RwTB, 'bridge_2x2_rw_pipe': Bridge2x2RwPipeTB,
            'bridge_2x2_rw_rq8': Bridge2x2RwRq8TB, 'bridge_4x4_rw': Bridge4x4RwTB,
            'bridge_4x4_rw_rq8': Bridge4x4RwRq8TB}
# masters, their reach (TOML connectivity), the hot slave
ROLES = {
    'bridge_2x2_rw':      Roles((0, 1), {0: (0, 1), 1: (0, 1)}, hot=0),
    'bridge_2x2_rw_pipe': Roles((0, 1), {0: (0, 1), 1: (0, 1)}, hot=0),
    'bridge_2x2_rw_rq8':  Roles((0, 1), {0: (0, 1), 1: (0, 1)}, hot=0),
    # 4x4: cpu 64b, dma0 32b, dma1 128b, gpu 256b; periph 32b, ddr0 64b, sram 128b, gpu_mem 256b
    'bridge_4x4_rw':      Roles((0, 1, 2, 3), {0: (0, 1, 2, 3), 1: (0, 1, 2), 2: (1, 2, 3), 3: (0, 1, 3)}, hot=1),
    'bridge_4x4_rw_rq8':  Roles((0, 1, 2, 3), {0: (0, 1, 2, 3), 1: (0, 1, 2), 2: (1, 2, 3), 3: (0, 1, 3)}, hot=1),
}
SLAVE_PFX = {
    'bridge_2x2_rw': {0: 'ddr_s_axi', 1: 'sram_s_axi'},
    'bridge_2x2_rw_pipe': {0: 'ddr_s_axi', 1: 'sram_s_axi'},
    'bridge_2x2_rw_rq8': {0: 'ddr_s_axi', 1: 'sram_s_axi'},
    'bridge_4x4_rw': {0: 'periph_slave_axi', 1: 'ddr0_slave_axi', 2: 'sram_slave_axi', 3: 'gpu_mem_slave_axi'},
    'bridge_4x4_rw_rq8': {0: 'periph_slave_axi', 1: 'ddr0_slave_axi', 2: 'sram_slave_axi', 3: 'gpu_mem_slave_axi'},
}
GAPS = {'gate': [16, 4, 2], 'func': [32, 16, 8, 6, 5, 4, 3, 2], 'full': [32, 16, 8, 6, 5, 4, 3, 2]}
NREADS = {'gate': 24, 'func': 48, 'full': 96}
ACCEPT_FLOOR = 0.85
LAT_SLACK = 4
KNOWN_UNIFORM_FLOOR = 0.55      # unqueued fabric past saturation (bridge TASK-021)
QUEUED = {'bridge_2x2_rw_rq8'}  # the queue removes the whole loss: the full floor applies

FIXTURE = os.environ.get('BRIDGE_PERF_FIXTURE', 'bridge_2x2_rw')


async def _pattern(dut, pattern):
    tb = FIXTURES[FIXTURE](dut)
    tb.R_INTERLEAVE = False
    for sl in tb.slave_rd.values():
        sl.interleave_r = False
    await tb.setup_clocks_and_reset()
    saturate(tb)
    roles = ROLES[FIXTURE]
    pts = await sweep(tb, roles, pattern, GAPS[tb.level], NREADS[tb.level],
                      lambda s: SLAVE_PFX[FIXTURE][s])
    failures = []
    base = None
    for p in pts:
        report(tb, f"{FIXTURE} {pattern} gap={p.gap}", offered=p.offered, capacity=p.capacity,
               accepted=p.accepted, **{f"s{s}_offered": v for s, v in (p.offered_by_slave or {}).items()},
               **{f"m{m}_mean": v for m, v in p.mean_lat.items()},
               **{f"m{m}_p95": v for m, v in p.p95_lat.items()})
        known = (pattern == 'uniform' and p.offered > p.capacity + 1e-9      # TASK-021
                 and FIXTURE not in QUEUED)
        floor = (KNOWN_UNIFORM_FLOOR if known else ACCEPT_FLOOR) * p.capacity
        if p.accepted < floor:
            failures.append(f"{pattern} gap {p.gap}: accepted {p.accepted:.3f} slave beats/cycle "
                            f"for {p.offered:.3f} offered, capacity {p.capacity:.3f} (floor {floor:.3f}"
                            f"{', unqueued fabric, bridge TASK-021' if known else ''})")
        if base is None:
            base = dict(p.mean_lat)
        if p.offered <= p.capacity / 2:
            for m, v in p.mean_lat.items():
                if v > base[m] + LAT_SLACK:
                    failures.append(f"{pattern} gap {p.gap}: m{m} mean latency {v:.1f} at "
                                    f"{p.offered:.2f} offered, {base[m]:.1f} at the lightest load")
    for line in table(pts, roles.masters):
        tb.log.info(line)
    assert not failures, f"{len(failures)} failure(s):\n  " + "\n  ".join(failures)
    tb.assert_compliance()


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_perf_patterns_uniform(dut):
    await _pattern(dut, 'uniform')


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_perf_patterns_permutation(dut):
    await _pattern(dut, 'permutation')


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_perf_patterns_hotspot(dut):
    await _pattern(dut, 'hotspot')


def _run(request, test_level, pattern, fixture):
    module, repo_root_, tests_dir, log_dir, _ = get_paths({})
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path=f'projects/components/fabric-gen-ip/bridge/rtl/filelists/{fixture}.f')
    worker = os.environ.get('PYTEST_XDIST_WORKER', '')
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    name = f"test_{fixture}_perf_patterns_{pattern}_{test_level}_{reg_level}" + (f"_{worker}" if worker else "")
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    waves = get_wave_config(sim_build)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=fixture, module=module, testcase=f"cocotb_test_perf_patterns_{pattern}",
        sim_build=sim_build, waves=False,
        extra_args=['--assert'] + waves['extra_args'],
        extra_env={'COCOTB_LOG_LEVEL': 'INFO', 'LOG_PATH': log_path,
                   'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
                   'BRIDGE_PERF_FIXTURE': fixture, **level_env(test_level), **waves['extra_env']},
        plus_args=waves['sim_args'], keep_files=True)


@pytest.mark.parametrize("fixture", sorted(FIXTURES))
@pytest.mark.parametrize("pattern", PATTERNS)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_perf_patterns(request, test_level, pattern, fixture):
    _run(request, test_level, pattern, fixture)
