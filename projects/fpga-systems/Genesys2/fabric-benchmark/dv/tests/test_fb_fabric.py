# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""fb_data_fabric, every leg: the data fabric under test, alone.

The same TB and the same seed drive each leg's `fb_data_fabric`; the leg is
chosen only by which filelist is compiled (PRD.md section 4). Both legs must
pass identically before either goes into the harness: concurrent traffic from
all four masters with data checked at both ends, IDs {slot, id} at every slave
with the master's ID in the low bits, DECERR for unconnected and unmapped
targets.

Leg B1 compiles the Xilinx AXI Crossbar from the Vivado install, so
XILINX_VIVADO must point at it (Vivado's settings64.sh sets it).
"""
import os
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from tbclasses.fb_fabric_tb import FbFabricTB

COUNTS = {'gate': 20, 'func': 120, 'full': 500}
AREA = 'projects/fpga-systems/Genesys2/fabric-benchmark'
LEG_FILELIST = {
    'bridge': f'{AREA}/rtl/filelists/fb_data_fabric_bridge.f',
    'xbar':   f'{AREA}/rtl/filelists/fb_data_fabric_xbar_sim.f',
}


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_fb_fabric(dut):
    tb = FbFabricTB(dut)
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    n = COUNTS.get(level, COUNTS['gate'])
    tb.preload()
    await tb.setup_clocks_and_reset()

    ok = await tb.run_traffic(n)
    tb.log.info(f"traffic: {'ok' if ok else 'FAILED'}")
    ok = ok and tb.check_memory()
    tb.log.info(f"memory: {'ok' if ok else 'FAILED'}")
    if ok:
        ok = await tb.run_decerr()
        tb.log.info(f"decerr: {'ok' if ok else 'FAILED'}")
    await tb.wait_clocks('aclk', 20)
    assert tb.report(), f"{len(tb.errors)} error(s); first: {tb.errors[0] if tb.errors else ''}"
    # A pass must have exercised what it claims (an idle run is not a pass).
    assert tb.stats['rd'] >= 2 * n and tb.stats['wr'] >= 2 * n, tb.stats
    assert tb.stats['decerr'] == 4 and tb.stats['ids'] >= 4 * n, tb.stats


def generate_test_params():
    """(leg, test_level)"""
    reg = os.environ.get('REG_LEVEL', 'FUNC').upper()
    level = {'GATE': 'gate', 'FUNC': 'func', 'FULL': 'full'}.get(reg, 'func')
    return [(leg, level) for leg in ('bridge', 'xbar')]


@pytest.mark.parametrize("leg, test_level", generate_test_params())
def test_fb_fabric(request, leg, test_level):
    """fb_data_fabric per leg (rtl/generated/fb_data_fabric_<leg>/fb_data_fabric.sv)."""
    if leg == 'xbar' and not os.environ.get('XILINX_VIVADO'):
        pytest.fail("XILINX_VIVADO is not set: leg B1 compiles the AXI Crossbar from the "
                    "Vivado install (source Vivado's settings64.sh)")
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    dut_name = 'fb_data_fabric'
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    name = f"test_{worker_id}_fb_fabric_{leg}_{test_level}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=LEG_FILELIST[leg])
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_env = {
        'TEST_LEVEL': test_level, 'FB_LEG': leg,
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    compile_args = ["-Wno-fatal", "-Wno-lint", "-Wno-style", "-Wno-MULTIDRIVEN"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_fb_fabric",
        sim_build=sim_build, extra_env=extra_env, waves=enable_waves, keep_files=True,
        compile_args=compile_args,
        sim_args=(["--trace-fst", "--trace-structs"] if enable_waves else []),
        plus_args=(["--trace"] if enable_waves else []))
