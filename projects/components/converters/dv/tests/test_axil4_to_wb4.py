# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""axil4_to_wb4: AXI4-Lite slave in, Wishbone B4 master out.

Phases (all levels; counts scale with TEST_LEVEL):
  sequential   one transaction at a time, ACK/ERR/RTY windows
  strobes      full write, partial write, read back: untouched bytes survive
  pipelined    several reads and writes in flight, mixed, against a stalling
               and a slow-terminating slave (the arbiter and the direction
               queue under load; the monitor's max_inflight must exceed 1 in
               pipelined mode)
  drain        busy drops and the Wishbone monitor saw one transfer per
               transaction with no B4 violations
CLASSIC=1 builds run the same phases against a classic-mode slave BFM.
"""
import os
import random
from itertools import product

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from projects.components.converters.dv.tbclasses.axil4_to_wb4_tb import AXIL4ToWB4TB

COUNTS = {'gate': (24, 40), 'func': (80, 160), 'full': (200, 600)}


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_axil4_to_wb4(dut):
    tb = AXIL4ToWB4TB(dut)
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    n_seq, n_pipe = COUNTS[level]
    rng = random.Random(int(os.environ.get('SEED', '0')))
    await tb.setup_clocks_and_reset()

    await tb.run_random(rng, n_seq, concurrency=1)
    await tb.run_strobes(rng, max(4, n_seq // 4))
    await tb.wait_idle()
    seq_errors = len(tb.errors)

    tb.set_slave_profile('stally')
    await tb.run_random(rng, n_pipe // 2, concurrency=6)
    tb.set_slave_profile('slow')
    await tb.run_random(rng, n_pipe - n_pipe // 2, concurrency=6)
    tb.set_slave_profile('mixed')
    await tb.run_random(rng, n_pipe, concurrency=4, windows=False)
    await tb.wait_idle()
    tb.check_monitor()

    if not tb.classic and tb.mon.max_inflight < 2:
        tb.errors.append(f"pipelined: max_inflight {tb.mon.max_inflight}, expected several transfers open")
    if tb.classic and tb.mon.max_inflight != 1:
        tb.errors.append(f"classic: max_inflight {tb.mon.max_inflight}, expected exactly 1")
    tb.log.info(f"sequential phase errors: {seq_errors}")
    assert tb.report(), f"axil4_to_wb4 failed: {tb.errors[:5]}"


def generate_test_params():
    reg = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg == 'GATE':
        return [(32, 32, 0, 'gate'), (32, 32, 1, 'gate')]
    if reg == 'FUNC':
        return [(32, 32, 0, 'func'), (32, 32, 1, 'func'), (16, 64, 0, 'func')]
    return list(product([16, 32], [32, 64], [0, 1], ['full']))


@pytest.mark.parametrize("addr_width, data_width, classic, test_level", generate_test_params())
def test_axil4_to_wb4(request, addr_width, data_width, classic, test_level):
    """axil4_to_wb4 (projects/components/converters/rtl/axil4_to_wb4.sv) with AXI4-Lite
    master BFMs in front and the framework Wishbone slave + monitor behind."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/converters/rtl',
        'rtl_amba_includes': 'rtl/amba/includes'})
    dut_name = 'axil4_to_wb4'
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    name = (f"test_{worker_id}_{dut_name}_aw{addr_width:03d}_dw{data_width:03d}"
            f"_{'classic' if classic else 'pipe'}_{test_level}")
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path='projects/components/converters/rtl/filelists/axil4_to_wb4.f')
    rty_resp = 3 if classic else 2          # DECERR on the classic builds proves the parameter path
    rtl_parameters = {'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
                      'CLASSIC': str(classic), 'RTY_RESP': f"2'd{rty_resp}"}
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_env = {
        'TEST_LEVEL': test_level, 'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
        'CLASSIC': str(classic), 'RTY_RESP': str(rty_resp),
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    compile_args = ["-Wno-DECLFILENAME", "-Wno-UNUSEDPARAM", "-Wno-UNUSEDSIGNAL"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_axil4_to_wb4",
        parameters=rtl_parameters, sim_build=sim_build, extra_env=extra_env, waves=enable_waves,
        keep_files=True, compile_args=compile_args,
        sim_args=(["--trace-fst", "--trace-structs"] if enable_waves else []),
        plus_args=(["--trace"] if enable_waves else []))
