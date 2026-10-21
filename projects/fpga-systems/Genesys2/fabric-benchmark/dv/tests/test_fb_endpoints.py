# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""fb_endpoints: LFSR source + CRC sink behind AXI4 CDCs, verdicts back to aclk.

Clock pairs, all asynchronous: endpoint faster than the fabric (the design
point), equal periods, and endpoint SLOWER (a fault case: the crossings must
still be correct, only the line-rate floor is waived).
"""
import os
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from tbclasses.fb_endpoints_tb import FbEndpointsTB
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402

BURSTS = {'gate': 4, 'func': 16, 'full': 64}
AREA = 'projects/fpga-systems/Genesys2/fabric-benchmark'


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_fb_endpoints(dut):
    tb = FbEndpointsTB(dut)
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    n = BURSTS.get(level, BURSTS['gate'])
    floor = float(os.environ.get('LINE_RATE_FLOOR', '0.9'))
    await tb.setup_clocks_and_reset()
    ok = await tb.run_loopback(n)
    ok = ok and await tb.run_clear()
    if ok:
        await tb.run_line_rate(n, floor)
    assert tb.report(), f"{len(tb.errors)} error(s); first: {tb.errors[0] if tb.errors else ''}"


def generate_test_params():
    """(ch_sel, aclk_ns, ep_ns, line-rate floor, test_level)

    'addr' is the benchmark's build (CH_SEL_ADDR=1) at every clock pair;
    'id' keeps the ID-select build covered at one.
    """
    reg = os.environ.get('REG_LEVEL', 'FUNC').upper()
    level = {'GATE': 'gate', 'FUNC': 'func', 'FULL': 'full'}.get(reg, 'func')
    pairs = [(10.0, 8.0, 0.9), (10.0, 10.0, 0.9), (10.0, 13.0, 0.0)]
    if reg == 'GATE':
        pairs = pairs[:1]
    return [('addr', a, e, f, level) for a, e, f in pairs] + [('id', *pairs[0], level)]


@pytest.mark.parametrize("ch_sel, aclk_ns, ep_ns, floor, test_level", generate_test_params())
def test_fb_endpoints(request, ch_sel, aclk_ns, ep_ns, floor, test_level):
    """fb_endpoints (rtl/fb_endpoints.sv)."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    dut_name = 'fb_endpoints'
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    name = f"test_{worker_id}_fb_endpoints_{ch_sel}_a{int(aclk_ns * 10)}_e{int(ep_ns * 10)}_{test_level}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=f'{AREA}/rtl/filelists/fb_endpoints.f')
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_env = {
        'TEST_LEVEL': test_level, 'ACLK_PERIOD_NS': str(aclk_ns), 'EP_PERIOD_NS': str(ep_ns),
        'LINE_RATE_FLOOR': str(floor), 'CH_SEL': ch_sel,
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    compile_args = ["-Wno-fatal", "-Werror-MULTIDRIVEN", FIELD_COMBO_VLT, "-Wno-lint", "-Wno-style"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_fb_endpoints",
        parameters={'CH_SEL_ADDR': 1 if ch_sel == 'addr' else 0},
        sim_build=sim_build, extra_env=extra_env, waves=enable_waves, keep_files=True,
        compile_args=compile_args, timescale="1ns/1ps",
        sim_args=(["--trace-fst", "--trace-structs"] if enable_waves else []),
        plus_args=(["--trace"] if enable_waves else []))
