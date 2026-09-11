#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-017 registered crossbar (xbar_pipeline).
#
# bridge_2x2_rw_pipe is bridge_2x2_rw with a skid stage on every slave-side
# channel inside the crossbar. Two things define the option and both are
# asserted EXACTLY here, the way test_bridge_2x2_rw_latency pins the
# baseline: the structural propagation is one cycle longer each way (3/3
# against the baseline's 2/2) and not more -- a stage that cost two cycles
# would be a bug -- and the beat rates are unchanged, which
# test_bridge_2x2_rw_perf checks on both fixtures with the same floors.
#
# Same measurement as the baseline test: VALID arrival at the far port, on
# an idle bridge with a prompt slave, so the figure is pipeline depth and
# not queueing.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from projects.components.bridge.dv.tbclasses.bridge2x2_rw_pipe_tb import Bridge2x2RwPipeTB

REQ_CYCLES = 3   # master AW accepted -> AWVALID at the slave port (baseline 2)
RSP_CYCLES = 3   # slave B accepted   -> BVALID at the master port (baseline 2)


def _hi(sig):
    try:
        return int(sig.value) == 1
    except ValueError:
        return False


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_pipe_latency(dut):
    tb = Bridge2x2RwPipeTB(dut)
    await tb.setup_clocks_and_reset()
    tb.set_slave_response_delay(0, 1)
    samples = tb.level_cfg['latency_samples']
    for sample in range(samples):
        marks = {}

        async def _sampler():
            n = 0
            while True:
                await RisingEdge(tb.clock)
                n += 1
                if _hi(dut.cpu_m_axi_awvalid) and _hi(dut.cpu_m_axi_awready):
                    marks.setdefault('m_aw', n)
                if _hi(dut.ddr_s_axi_awvalid):
                    marks.setdefault('s_aw_valid', n)
                if _hi(dut.ddr_s_axi_bvalid) and _hi(dut.ddr_s_axi_bready):
                    marks.setdefault('s_b', n)
                if _hi(dut.cpu_m_axi_bvalid):
                    marks.setdefault('m_b_valid', n)

        task = cocotb.start_soon(_sampler())
        addr = 0x00002000 if sample == 0 else 0x00001000 + tb.rng.randrange(0, 0x2000, 4)
        await tb.master_write(0, addr, 0x91BE0000 | sample)
        for _ in range(60):
            if {'m_aw', 's_aw_valid', 's_b', 'm_b_valid'} <= marks.keys():
                break
            await ClockCycles(tb.clock, 1)
        task.kill()
        missing = {'m_aw', 's_aw_valid', 's_b', 'm_b_valid'} - marks.keys()
        assert not missing, f"never observed: {sorted(missing)}"
        req = marks['s_aw_valid'] - marks['m_aw']
        rsp = marks['m_b_valid'] - marks['s_b']
        tb.log.info(f"sample {sample + 1}/{samples}: request {req} cycles, response {rsp} cycles "
                    f"(baseline combinational crossbar: 2 / 2)")
        assert req == REQ_CYCLES, (
            f"registered crossbar: AW propagation is {req} cycles, expected exactly "
            f"{REQ_CYCLES} (baseline 2 + one request stage)")
        assert rsp == RSP_CYCLES, (
            f"registered crossbar: B propagation is {rsp} cycles, expected exactly "
            f"{RSP_CYCLES} (baseline 2 + one response stage)")
        await ClockCycles(tb.clock, 20)
    tb.log.info(f"BRIDGE-017 xbar_pipeline PASSED: {REQ_CYCLES}/{RSP_CYCLES} on {samples} sample(s)")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_pipe_latency(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_rw_pipe"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/bridge/rtl/filelists/{dut_name}.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_latency_{test_level}_{reg_level}"
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
        testcase="cocotb_test_bridge_2x2_rw_pipe_latency",
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
