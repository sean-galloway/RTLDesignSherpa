# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""fb_harness (K0): fabric-only mode W2, every simulatable leg, the board's runner.

The Genesys 2 STREAM characterization runner drives the harness over the sim
UART exactly as it drives the board; the leg is chosen only by which harness
filelist is compiled. Leg B2 (SmartConnect) is encrypted and has no sim
(PRD section 5).
"""
import os
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from tbclasses.fb_harness_tb import FbHarnessTB

AREA = 'projects/fpga-systems/Genesys2/fabric-benchmark'
# (channels, descriptors per channel, bytes per descriptor), cumulative by level
RUNS = {
    'gate': [(1, 1, 4096)],
    'func': [(1, 1, 4096), (4, 2, 8192), (8, 2, 8192)],
    'full': [(1, 1, 4096), (4, 2, 8192), (8, 2, 8192), (8, 4, 65536)],
}
SIM_FPGA_CLK_HZ = 100_000_000
SIM_UART_BAUD = 25_000_000           # CLKS_PER_BIT = 4, the measured floor


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_fb_harness(dut):
    tb = FbHarnessTB(dut)
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    runs = RUNS.get(level, RUNS['gate'])
    # FB_RUNS="ch:desc:bytes,..." replaces the level's list (debug / A-B only)
    if os.environ.get('FB_RUNS'):
        runs = [tuple(int(x) for x in r.split(':')) for r in os.environ['FB_RUNS'].split(',')]
    await tb.setup_clocks_and_reset()
    ok = await tb.ping()
    if ok:
        for ch, desc, nbytes in runs:
            await tb.run(ch, desc, nbytes)
    assert tb.report(), f"{len(tb.errors)} error(s); first: {tb.errors[0] if tb.errors else ''}"
    assert len(tb.results) == len(runs), "not every run executed"


def generate_test_params():
    reg = os.environ.get('REG_LEVEL', 'FUNC').upper()
    level = {'GATE': 'gate', 'FUNC': 'func', 'FULL': 'full'}.get(reg, 'func')
    return [(leg, level) for leg in ('bridge', 'xbar')]


@pytest.mark.parametrize("leg, test_level", generate_test_params())
def test_fb_harness(request, leg, test_level):
    """fb_harness per leg (rtl/filelists/fb_harness_<leg>.f)."""
    if leg == 'xbar' and not os.environ.get('XILINX_VIVADO'):
        pytest.fail("XILINX_VIVADO is not set: leg B1 compiles the AXI Crossbar from the Vivado install")
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    dut_name = 'fb_harness'
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    name = f"test_{worker_id}_fb_harness_{leg}_{test_level}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=f'{AREA}/rtl/filelists/fb_harness_{leg}.f')
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_env = {
        'TEST_LEVEL': test_level, 'FB_LEG': leg,
        'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ), 'UART_BAUD': str(SIM_UART_BAUD),
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    if os.environ.get('FB_RUNS'):
        extra_env['FB_RUNS'] = os.environ['FB_RUNS']
    compile_args = ["-Wno-fatal", "-Wno-lint", "-Wno-style", "-Wno-MULTIDRIVEN",
                    "-Wno-TIMESCALEMOD", "-Wno-UNOPTFLAT"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_fb_harness",
        parameters={'FPGA_CLK_HZ': SIM_FPGA_CLK_HZ, 'UART_BAUD': SIM_UART_BAUD},
        sim_build=sim_build, extra_env=extra_env, waves=enable_waves, keep_files=True,
        compile_args=compile_args, timescale="1ns/1ps",
        sim_args=(["--trace-fst", "--trace-structs"] if enable_waves else []),
        plus_args=(["--trace"] if enable_waves else []))
