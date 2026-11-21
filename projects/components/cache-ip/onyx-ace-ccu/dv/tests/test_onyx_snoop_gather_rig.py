# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""onyx snoop-gather rig (onyx TASK-001 step 1): the ACE snoop BFMs and the
house ACE transport movers in the N-port gather shape onyx will use, before
any onyx RTL exists.

GATE:  (N 2, DW 64, gate)
FUNC:  + (N 2, DW 64, func), (N 3, DW 64, func), (N 4, DW 32, func)
FULL:  N {2,3,4} x DW {32,64} x {gate, func, full}

The DUT is dv/tb/onyx_snoop_gather_rig_tb.sv (pure wiring: per port an
axi4ace_snoop_master mover into an axi4ace_snoop_slave mover); sources are
the two rtl/amba ACE mover filelists plus the harness.
"""
import os
import random
import sys
from itertools import product

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import create_view_cmd, get_paths, get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)
from projects.components.cache_ip.onyx_ace_ccu.dv.tbclasses.onyx_snoop_gather_tb import (  # noqa: E402
    OnyxSnoopGatherTB,
)

HARNESS = 'projects/components/cache-ip/onyx-ace-ccu/dv/tb/onyx_snoop_gather_rig_tb.sv'
MOVER_FILELISTS = ('rtl/amba/filelists/axi4ace_snoop_master.f',
                   'rtl/amba/filelists/axi4ace_snoop_slave.f')
DUT_TOP = 'onyx_snoop_gather_rig_tb'


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_onyx_snoop_gather(dut):
    tb = OnyxSnoopGatherTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    for i, chk in enumerate(tb.checkers):
        if chk is not None:
            chk.print_compliance_report()
    assert ok, (f"onyx_snoop_gather: {report['mismatches']} mismatches in {report['checks']} checks, "
                f"{report['default_matrix_diffs']} default-matrix diffs, "
                f"{report['compliance_violations']} compliance violations")


def generate_params():
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [(2, 64, 'gate')]
    if reg_level == 'FUNC':
        return [(2, 64, 'gate'), (2, 64, 'func'), (3, 64, 'func'), (4, 32, 'func')]
    return [(n, dw, lvl) for n, dw, lvl in product((2, 3, 4), (32, 64), ('gate', 'func', 'full'))]


@pytest.mark.parametrize("n_caches, data_width, test_level", generate_params())
def test_onyx_snoop_gather_rig(request, n_caches, data_width, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, _rtl_dict = get_paths({})
    verilog_sources, includes = [], []
    for fl in MOVER_FILELISTS:
        srcs, incs = get_sources_from_filelist(repo_root=repo_root, filelist_path=fl)
        for s in srcs:
            if s not in verilog_sources:
                verilog_sources.append(s)
        for inc in incs:
            if inc not in includes:
                includes.append(inc)
    verilog_sources.append(os.path.join(repo_root, HARNESS))

    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    name = f"test_onyx_snoop_gather_rig_n{n_caches}_d{data_width:03d}_{test_level}_{reg_level}"
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{name}.xml')

    rtl_parameters = {'N_CACHES': str(n_caches), 'ADDR_WIDTH': '32',
                      'DATA_WIDTH': str(data_width)}
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': DUT_TOP,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_LEVEL': test_level,
        'TEST_N_CACHES': str(n_caches),
        'TEST_ADDR_WIDTH': '32',
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_LINE_BYTES': '64',
        'TEST_CLK_PERIOD': '10',
        'ACE_COMPLIANCE_CHECK': '1',
    }
    compile_args = ["-Wall", "-Wno-SYNCASYNCNET", "-DUSE_ASYNC_RESET", "-Wno-UNUSED",
                    "-Wno-DECLFILENAME"]
    sim_args, plus_args = [], []
    if enable_waves:
        compile_args += ["--trace", "--trace-depth", "99"]
        sim_args += ["--trace", "--trace-depth", "99"]
        plus_args += ["--trace"]
    create_view_cmd(os.path.dirname(log_path), log_path, sim_build, module, name)
    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=DUT_TOP,
            module=module,
            testcase="cocotb_test_onyx_snoop_gather",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plus_args,
        )
    except Exception as e:
        print(f"onyx_snoop_gather_rig {name} FAILED: {e}; log {log_path}")
        raise
