# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""bs_harness: the whole stress model in simulation, driven by the board's
host library over the sim UART (dv/tbclasses/bs_harness_tb.py).

One test per (DUT, profile): every profile of bin/bstress.PROFILES runs at the
TEST_LEVEL budget on every master and both directions, and must pass the
board's own verdict -- no error bit anywhere, every budget issued and retired,
every slave reached, DECERR exactly when a hole was targeted.
"""
from __future__ import annotations

import os
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402  (not -Wno-MULTIDRIVEN)

AREA = 'projects/fpga-systems/Genesys2/bridge-stress'
DUTS = ['bridge_bs_axi4', 'bridge_bs_axi3', 'bridge_bs_axi5', 'bridge_bs_xil', 'bridge_bs_xmix']
# build-xil's vendor slaves are BFM memories here, which model aligned INCR only
# build-xil: the vendor-memory BFM models aligned INCR only; 'ocelus' is the
# monitors' self-check (bs_harness_tb.BsHarnessTB.run)
DUT_PROFILES = {'bridge_bs_xil': ['clean', 'ocelus'], 'bridge_bs_xmix': ['clean']}
TXNS = {'gate': 40, 'func': 200, 'full': 1000}
SIM_UART_CLKS_PER_BIT = 4


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_bs_harness(dut):
    from tbclasses.bs_harness_tb import BsHarnessTB
    toml = os.environ['BS_TOML']
    profiles = os.environ.get('BS_PROFILES', 'clean').split(',')
    level = os.environ.get('TEST_LEVEL', 'gate')
    txns = int(os.environ.get('BS_TXNS', TXNS.get(level, TXNS['gate'])))
    seed = int(os.environ.get('SEED', '1'))
    tb = BsHarnessTB(dut, toml)
    await tb.setup_clocks_and_reset()
    await tb.identify()
    for p in profiles:
        assert await tb.run(p, seed, txns)
    tb.check_go()
    assert not tb.failures, '\n'.join(tb.failures)


def _params():
    # BS_PROFILES=a,b,c runs those profiles in ONE simulation (one model build)
    from_env = os.environ.get('BS_PROFILES')
    if from_env:
        return [(d, from_env) for d in DUTS]
    profiles = [
        'clean', 'bursts', 'backpressure', 'reorder', 'narrow', 'single_id',
        'errors', 'short', 'chaos', 'w_first']
    return [(d, p) for d in DUTS for p in DUT_PROFILES.get(d, profiles)]


@pytest.mark.parametrize("dut_bridge, profile", _params())
def test_bs_harness(request, dut_bridge, profile, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    dut_name = f'bs_harness_{dut_bridge}'
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    tag = profile if ',' not in profile else 'multi'
    name = f"test_{worker_id}_bs_harness_{dut_bridge}_{tag}_{test_level}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'{AREA}/rtl/generated/filelists/bs_harness_{dut_bridge}.f')
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_env = {
        'TEST_LEVEL': test_level, 'BS_PROFILES': profile,
        'BS_TOML': os.path.join(repo_root, AREA, 'rtl/bridges/configs', f'{dut_bridge}.toml'),
        'CLKS_PER_BIT': str(SIM_UART_CLKS_PER_BIT),
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(1, 100000))),
    }
    for k in ('BS_TXNS', 'BS_BURSTS', 'BS_TIMEOUT_S', 'BS_FULL_AXI', 'BS_EXCLUDE'):
        if os.environ.get(k):
            extra_env[k] = os.environ[k]
    compile_args = ["-Wno-fatal", "-Werror-MULTIDRIVEN", "-Wno-lint", "-Wno-style", FIELD_COMBO_VLT,
                    "-Wno-TIMESCALEMOD", "-Wno-UNOPTFLAT"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_bs_harness",
        parameters={'CLKS_PER_BIT': SIM_UART_CLKS_PER_BIT},
        sim_build=sim_build, simulator="verilator", extra_env=extra_env,
        waves=enable_waves, keep_files=True,
        compile_args=compile_args, timescale="1ns/1ps",
        sim_args=(["--trace-fst", "--trace-structs"] if enable_waves else []),
        plus_args=(["--trace"] if enable_waves else []))
