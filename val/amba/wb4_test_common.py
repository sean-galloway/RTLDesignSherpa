# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Shared tables and the pytest runner for the wb4 family tests.

A test file must not import another test file: cocotb registers every
@cocotb.test it sees at import time, so `from test_wb4_master import PHASES`
would make the slave test also run the master's cocotb test against the
slave DUT. Shared pieces live here instead.
"""
import os
import random

from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# (cmd GAXI profile, rsp GAXI profile, WB4Slave profile) -- see test_wb4_master
MASTER_PHASES = [
    ('fixed',      'fixed',       'fixed'),
    ('backtoback', 'backtoback',  'slow_ack'),
    ('fast',       'burst_pause', 'slow_ack'),
    ('backtoback', 'backtoback',  'fixed'),
    ('fast',       'fast',        'slow_ack'),
    ('fast',       'burst_pause', 'stally'),
    ('constrained', 'constrained', 'mixed'),
]

# (WB4Master profile, cmd GAXI profile, rsp GAXI profile) -- see test_wb4_slave
SLAVE_PHASES = [
    ('fixed',  'fixed',       'fixed'),
    ('fixed',  'backtoback',  'backtoback'),
    ('gappy',  'burst_pause', 'fast'),
    ('fixed',  'fast',        'burst_pause'),
    ('sparse', 'constrained', 'constrained'),
]

COUNTS = {'gate': 60, 'func': 200, 'full': 400}


def run_wb4(request, dut_name, filelist, tag, rtl_parameters, extra_env):
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba', 'rtl_amba_includes': 'rtl/amba/includes'})
    # get_paths() names the cocotb MODULE after its caller, which is this
    # helper: cocotb would then load a module with no tests and report a
    # pass without simulating anything. The test file is the module.
    module = os.path.splitext(os.path.basename(str(request.fspath)))[0]
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=filelist)
    name = f"test_{worker_id}_{dut_name}_{tag}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_env.update({
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    })
    compile_args = ["-Wno-DECLFILENAME", "-Wno-UNUSEDPARAM"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, parameters=rtl_parameters, sim_build=sim_build,
        extra_env=extra_env, waves=enable_waves, keep_files=True, compile_args=compile_args,
        sim_args=(["--trace-fst", "--trace-structs"] if enable_waves else []),
        plus_args=(["--trace"] if enable_waves else []))
