#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): the buffer sizing rule at its boundary
# (bridge TASK-016).
#
# The generator sizes every unset max_outstanding to the smallest power of two
# >= 1 + latency_cycles + round trip (bridge_pkg.sizing; the figures it used
# are in <bridge>_sizing.json beside the RTL). This test runs single-beat and
# 8-beat closed-loop streams, cpu -> ddr, with as many in flight as the port
# allows, against a slave BFM that answers after exactly `lat` cycles, on two
# fixtures that differ only in the hint:
#   bridge_2x2_rw       latency_cycles 0   -> max_outstanding 16 (1 + 0 + 8 = 9)
#   bridge_2x2_rw_slow  latency_cycles 16  -> max_outstanding 32 (1 + 16 + 8 = 25)
# At lat = 16 the slow fixture saturates (32 >= 25) and the reference runs at
# about 16 / 25 of the port's peak -- the step the rule predicts, measured on
# both sides of it. At lat = 64 both are under their rule and both land on
# Little's law. 8-beat bursts saturate either fixture at lat = 16 (16 * 8 >=
# 8 + 16 + 8), which is the burst form of the rule.
import json
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
from bridge2x2_rw_slow_tb import Bridge2x2RwSlowTB                  # noqa: E402
from bridge_perf_char import Characterizer, Stream, pipeline        # noqa: E402
from bridge_perf_probe import report                                # noqa: E402

FIXTURES = {'bridge_2x2_rw': Bridge2x2RwTB, 'bridge_2x2_rw_slow': Bridge2x2RwSlowTB}
FIXTURE = os.environ.get('BRIDGE_PERF_FIXTURE', 'bridge_2x2_rw')
CPU, DDR = 0, 0
RTT = {'rd': 7, 'wr': 8}            # measured single-beat round trips, bridge_2x2_rw
FULL = 0.97
TOL = 0.90                          # Little's-law prediction, lower tolerance
BURSTS = {'gate': 32, 'func': 96, 'full': 256}
LATS = {'gate': (16,), 'func': (16, 64), 'full': (16, 64)}


def _sizing():
    p = os.path.join(repo_root, 'projects/components/fabric-gen-ip/bridge/rtl/generated',
                     FIXTURE, f'{FIXTURE}_sizing.json')
    with open(p) as fh:
        rep = json.load(fh)
    depth = {(r['direction'], r['port']): r['value'] for r in rep['ports'] if r['key'] == 'max_outstanding'}
    return rep, depth


def _predict(n_out, beats, lat, kind):
    return min(1.0, n_out * beats / (beats + lat + RTT[kind]))


@cocotb.test(timeout_time=300, timeout_unit="sec")
async def cocotb_test_perf_sizing_step(dut):
    tb = FIXTURES[FIXTURE](dut)
    tb.R_INTERLEAVE = False
    for sl in tb.slave_rd.values():
        sl.interleave_r = False
    await tb.setup_clocks_and_reset()
    pipeline(tb)
    ch = Characterizer(tb)
    rep, depth = _sizing()
    n_out = min(depth[('master', 'cpu')], depth[('slave', 'ddr')])
    hint = next((p for p in rep['paths'] if p['master'] == 'cpu' and p['slave'] == 'ddr'), {})
    tb.log.info(f"{FIXTURE}: max_outstanding cpu {depth[('master', 'cpu')]} / ddr {depth[('slave', 'ddr')]}, "
                f"model round trip write {hint.get('write')} / read {hint.get('read')}")
    s = ch.sampler({'s_w': ('s', DDR, 'w'), 's_r': ('s', DDR, 'r')})
    n = BURSTS[tb.level]
    failures, rows = [], []
    for lat in LATS[tb.level]:
        tb.slave_rd[DDR].response_delay_cycles = lat
        tb.slave_wr[DDR].response_delay_cycles = lat
        for beats in (1, 8):
            for kind in ('rd', 'wr'):
                # one ID per transaction in flight: the slave BFM answers same-ID
                # reads in order, one delayed response at a time per ID, so
                # rotating 16 IDs would cap the reads in flight at 16 whatever the
                # port allows (the 8-bit master IDs are remapped to slots anyway)
                st = Stream(kind, CPU, DDR, n, beats, outstanding=n_out, ids=tuple(range(n_out)))
                port = 's_r' if kind == 'rd' else 's_w'
                lo = s.cycle + 1
                await ch.run([st])
                hi = s.cycle
                marks = [c for c in s.marks[port] if lo <= c <= hi]
                rate = (len(marks) / (marks[-1] - marks[0] + 1)) if len(marks) > 1 else 0.0
                pred = _predict(n_out, beats, lat, kind)
                rule_ok = n_out * beats >= beats + lat + RTT[kind]
                label = f"sizing {kind} beats={beats} lat={lat} n_out={n_out}"
                report(tb, label, rate=rate, predicted=pred, rule_satisfied=int(rule_ok))
                rows.append((kind, beats, lat, n_out, rule_ok, pred, rate))
                if rule_ok and rate < FULL:
                    failures.append(f"{label}: the rule holds ({n_out}*{beats} >= {beats}+{lat}+{RTT[kind]}) "
                                    f"but the port ran at {rate:.3f} (floor {FULL})")
                if not rule_ok:
                    if rate < TOL * pred:
                        failures.append(f"{label}: {rate:.3f} under Little's law {pred:.3f}")
                    if rate >= FULL:
                        failures.append(f"{label}: saturated at {rate:.3f} although the rule says "
                                        f"{n_out}*{beats} < {beats}+{lat}+{RTT[kind]} -- the rule is too conservative here")
    tb.slave_rd[DDR].response_delay_cycles = 0
    tb.slave_wr[DDR].response_delay_cycles = 0
    tb.log.info("| kind | beats | slave lat | in flight | rule holds | predicted | measured |")
    for r in rows:
        tb.log.info("| {} | {} | {} | {} | {} | {:.3f} | {:.3f} |".format(*r))
    assert not failures, f"{len(failures)} failure(s):\n  " + "\n  ".join(failures)


def _run(request, test_level, fixture):
    module, repo_root_, tests_dir, log_dir, _ = get_paths({})
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path=f'projects/components/fabric-gen-ip/bridge/rtl/filelists/{fixture}.f')
    worker = os.environ.get('PYTEST_XDIST_WORKER', '')
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    name = f"test_{fixture}_perf_sizing_{test_level}_{reg_level}" + (f"_{worker}" if worker else "")
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    waves = get_wave_config(sim_build)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=fixture, module=module, testcase="cocotb_test_perf_sizing_step",
        sim_build=sim_build, waves=False,
        extra_args=['--assert'] + waves['extra_args'],
        extra_env={'COCOTB_LOG_LEVEL': 'INFO', 'LOG_PATH': log_path,
                   'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
                   'BRIDGE_PERF_FIXTURE': fixture, **level_env(test_level), **waves['extra_env']},
        plus_args=waves['sim_args'], keep_files=True)


@pytest.mark.parametrize("fixture", sorted(FIXTURES))
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_perf_sizing(request, test_level, fixture):
    _run(request, test_level, fixture)
