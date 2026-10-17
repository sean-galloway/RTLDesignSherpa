#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): throughput and latency of width-converted
# paths (GitHub #119 L4), on bridge_4x4_rw.
#
# Five paths, one master to one slave each, idle fabric otherwise:
#   matched   cpu    64b -> ddr0     64b
#   up 4:1    dma0   32b -> sram    128b
#   up 4:1    cpu    64b -> gpu_mem 256b
#   down 2:1  cpu    64b -> periph   32b
#   down 8:1  gpu   256b -> periph   32b
# For each: a stream of 16-beat write bursts then reads at the master's
# natural size, beat rates at the master and the slave port (aclk), every
# word checked, and the idle first-beat read latency (AR handshake to the
# first R handshake at the master port).
#
# The ideal is the narrower side's full rate: an upsize path moves one
# master beat per cycle (the slave sees 1/ratio); a downsize path moves one
# slave beat per cycle (the master sees 1/ratio). The floors below are set
# at 85% of that.

import os
import random
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from bridge4x4_rw_tb import Bridge4x4RwTB
from bridge_perf_probe import Sampler, saturate, report

BEATS = 16
FLOOR = 0.85
# (name, master idx, master prefix, master bits, slave idx, slave prefix, slave bits)
PATHS = [
    ('matched',  0, 'cpu_axi',  64,  1, 'ddr0_slave_axi',     64),
    ('up_4to1',  1, 'dma0_axi', 32,  2, 'sram_slave_axi',    128),
    ('up_4to1b', 0, 'cpu_axi',  64,  3, 'gpu_mem_slave_axi', 256),
    ('down_2to1', 0, 'cpu_axi', 64,  0, 'periph_slave_axi',   32),
    ('down_8to1', 3, 'gpu_axi', 256, 0, 'periph_slave_axi',   32),
]
NBURSTS = {'gate': 4, 'func': 8, 'full': 16}


async def _wait(tb, futs, what):
    for _ in range(20000):
        if all(f.done() for f in futs):
            for f in futs:
                f.result()
            return
        await ClockCycles(tb.clock, 5)
    raise AssertionError(f"{what}: {sum(f.done() for f in futs)}/{len(futs)} bursts completed")


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_4x4_rw_width_perf(dut):
    tb = Bridge4x4RwTB(dut)
    await tb.setup_clocks_and_reset()
    saturate(tb)
    n = NBURSTS[tb.level]
    rng = random.Random(int(os.environ.get('SEED', '1')))
    rows = []
    for name, m, mp, mbits, s, sp, sbits in PATHS:
        size = tb._natural_arsize(m)
        mbytes = mbits // 8
        _, sbase, _, _ = tb.slave_info[s]
        base = sbase + 0x1000 * (m + 1)
        plan = [(base + i * BEATS * mbytes,
                 [rng.getrandbits(mbits) for _ in range(BEATS)]) for i in range(n)]
        ideal_m = 1.0 if mbits <= sbits else sbits / mbits
        ideal_s = 1.0 if sbits <= mbits else mbits / sbits

        # writes
        smp = Sampler(tb, {'mw': (mp, 'w'), 'sw': (sp, 'w')}).start()
        futs = [cocotb.start_soon(tb.master_wr[m].write_transaction(a, d, id=i % 4, size=size))
                for i, (a, d) in enumerate(plan)]
        await _wait(tb, futs, f"{name} writes")
        for f in futs:
            res = f.result()
            assert not (isinstance(res, dict) and not res.get('success', True)), f"{name} write: {res}"
        _, _, mw = smp.window_rate('mw')
        _, _, sw = smp.window_rate('sw')

        # reads (and the data written)
        smp = Sampler(tb, {'mr': (mp, 'r'), 'sr': (sp, 'r')}).start()
        futs = [cocotb.start_soon(tb.master_rd[m].read_transaction(a, burst_len=BEATS, id=i % 4, size=size))
                for i, (a, _) in enumerate(plan)]
        await _wait(tb, futs, f"{name} reads")
        for f, (a, d) in zip(futs, plan):
            assert list(f.result()) == d, f"{name}: read 0x{a:08X} returned other data"
        _, _, mr = smp.window_rate('mr')
        _, _, sr = smp.window_rate('sr')

        # idle first-beat latency
        await ClockCycles(tb.clock, 20)
        smp = Sampler(tb, {'ar': (mp, 'ar'), 'r': (mp, 'r')}).start()
        await ClockCycles(tb.clock, 2)
        await tb.master_rd[m].read_transaction(plan[0][0], burst_len=1, id=0, size=size)
        await ClockCycles(tb.clock, 2)
        tb.log.info(f"{name} latency marks ar={smp.marks['ar']} r={smp.marks['r']} "
                    f"stalled_ar={smp.stalled['ar'][:4]} cycle={smp.cycle}")
        lat = smp.marks['r'][0] - smp.marks['ar'][0]

        report(tb, f"width {name} {mbits}b->{sbits}b", master_w=mw, slave_w=sw,
               master_r=mr, slave_r=sr, ideal_master=ideal_m, read_latency=lat)
        rows.append((name, mbits, sbits, mw, sw, mr, sr, ideal_m, lat))
        assert mw >= FLOOR * ideal_m and mr >= FLOOR * ideal_m, (
            f"{name}: master W {mw:.3f} / R {mr:.3f} beats/cycle, ideal {ideal_m:.3f}")
        await ClockCycles(tb.clock, 20)

    tb.log.info("| path | master | slave | master W | slave W | master R | slave R | ideal (master) | read latency |")
    for r in rows:
        tb.log.info("| {} | {}b | {}b | {:.3f} | {:.3f} | {:.3f} | {:.3f} | {:.3f} | {} |".format(*r))
    tb.assert_compliance()


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_4x4_rw_width_perf(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_4x4_rw"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/fabric-gen-ip/bridge/rtl/filelists/{dut_name}_checkers.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_width_perf_{test_level}_{reg_level}"
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
        testcase="cocotb_test_bridge_4x4_rw_width_perf",
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
