# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Shared configuration grid and pytest runner for the cxs family tests.

A test file must not import another test file: cocotb registers every
@cocotb.test it sees at import time (see wb4_test_common). Shared pieces
live here.

The grid spans every spec issue, so each REG_LEVEL proves the family, not
one corner of it: GATE has one Issue A, B and C point; FUNC adds Issue D
(4-byte start alignment, source/target IDs, user bits, 2048-bit flits),
CXS-Lite with link control, and an interface with no link control.
"""
import os
import random

from cocotb_test.simulator import run

from CocoTBFramework.components.cxs import CXSConfig
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

GATE_CONFIGS = [
    CXSConfig(issue='A', data_width=256, max_pkt_per_flit=2),
    CXSConfig(issue='B', data_width=512, max_pkt_per_flit=3, has_last=True, has_prcltype=True,
              check=True),
    CXSConfig(issue='C', data_width=72, max_pkt_per_flit=1, max_credit=63, link_control=False,
              check=True),
]

FUNC_CONFIGS = GATE_CONFIGS + [
    CXSConfig(issue='D', data_width=256, max_pkt_per_flit=3, start_align=4, srcid_width=4,
              tgtid_width=2, user_width=12, check=True),
    CXSConfig(issue='D', data_width=1024, max_pkt_per_flit=4, max_credit=6),
    CXSConfig(issue='C', data_width=256, max_pkt_per_flit=1, max_credit=4),
    CXSConfig(issue='A', data_width=512, max_pkt_per_flit=2, link_control=False),
    CXSConfig(issue='D', data_width=2048, max_pkt_per_flit=4, has_last=True),
]

FULL_CONFIGS = FUNC_CONFIGS + [
    CXSConfig(issue='D', data_width=512, max_pkt_per_flit=4, start_align=4, has_last=True,
              has_prcltype=True, srcid_width=8, tgtid_width=8, user_width=128, check=True,
              max_credit=31),
    CXSConfig(issue='B', data_width=1024, max_pkt_per_flit=3, max_credit=1, check=True),
    CXSConfig(issue='D', data_width=8, max_pkt_per_flit=1, max_credit=2, user_width=3),
    CXSConfig(issue='D', data_width=2048, max_pkt_per_flit=2, start_align=4, link_control=False,
              check=True),
]

# Packets per traffic phase
COUNTS = {'gate': 12, 'func': 40, 'full': 100}


def configs_for_level():
    """[(cfg, test_level)] for REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [(c, 'gate') for c in GATE_CONFIGS]
    if reg_level == 'FUNC':
        return [(c, 'func') for c in FUNC_CONFIGS]
    return [(c, 'full') for c in FULL_CONFIGS]


def current_test_level():
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    return level if level in COUNTS else 'gate'


def run_cxs(request, dut_name, cfg, test_level, extra_params=None, tag_extra=''):
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba', 'rtl_amba_includes': 'rtl/amba/includes'})
    # get_paths() takes the module AND the test directory from its caller --
    # this helper. Both come from the test file instead, so a runner in a
    # sub-area (val/amba/monitor-lite) builds, logs and imports from its own dir.
    module = os.path.splitext(os.path.basename(str(request.fspath)))[0]
    tests_dir = os.path.dirname(os.path.abspath(str(request.fspath)))
    log_dir = os.path.join(tests_dir, 'logs')
    filelist = f"rtl/amba/filelists/{dut_name}.f"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=filelist)
    rtl_parameters = {k: str(v) for k, v in cfg.rtl_parameters().items()}
    rtl_parameters.update({k: str(v) for k, v in (extra_params or {}).items()})
    name = f"test_{worker_id}_{dut_name}_{cfg.short_name()}{tag_extra}_{test_level}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_env = dict(rtl_parameters)
    extra_env.update({
        'TEST_LEVEL': test_level,
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    })
    compile_args = ["-Wno-DECLFILENAME", "-Wno-UNUSEDPARAM", "-Wno-UNUSEDSIGNAL"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, parameters=rtl_parameters, sim_build=sim_build,
        extra_env=extra_env, waves=enable_waves, keep_files=True, compile_args=compile_args,
        sim_args=(["--trace-fst", "--trace-structs"] if enable_waves else []),
        plus_args=(["--trace"] if enable_waves else []))
