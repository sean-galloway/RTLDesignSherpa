# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""onyx core-alone rig (onyx TASK-001 step 5): onyx_ccu with N BFM caches and
a BFM memory -- every request class onyx decodes, WriteClean included, at
N 2..4 and both D6 modes.

GATE:  (N 2, DW 64, DEFER_AR 0, normal, gate)
FUNC:  + (N 3, 64, 0, stress, func), (N 4, 64, 1, normal, func),
         (N 2, 32, 1, stress, func)
FULL:  N {2,3,4} x DEFER_AR {0,1} x profile {fast, normal, stress} at DW 64
       (full), plus N {2,4} at DW 32 (func)

The DUT is dv/tb/onyx_core_rig_tb.sv (pure wiring around onyx_ccu); the
sources are onyx_ccu.f plus the harness.
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
from projects.components.cache_ip.onyx_ace_ccu.dv.tbclasses.onyx_core_rig_tb import (  # noqa: E402
    OnyxCoreRigTB,
)

HARNESS = 'projects/components/cache-ip/onyx-ace-ccu/dv/tb/onyx_core_rig_tb.sv'
FILELIST = 'projects/components/cache-ip/onyx-ace-ccu/rtl/filelists/onyx_ccu.f'
DUT_TOP = 'onyx_core_rig_tb'


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_onyx_core_rig(dut):
    tb = OnyxCoreRigTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, (f"onyx_core_rig: {report['mismatches']} mismatches in {report['checks']} checks; "
                f"first: {tb.errors[:3]}")


def generate_params():
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    gate = [(2, 64, 0, 'normal', 'gate')]
    if reg_level == 'GATE':
        return gate
    func = gate + [(3, 64, 0, 'stress', 'func'), (4, 64, 1, 'normal', 'func'),
                   (2, 32, 1, 'stress', 'func')]
    if reg_level == 'FUNC':
        return func
    full = [(n, 64, d, prof, 'full')
            for n, d, prof in product((2, 3, 4), (0, 1), ('fast', 'normal', 'stress'))]
    return func + full + [(2, 32, 0, 'normal', 'func'), (4, 32, 0, 'stress', 'func')]


@pytest.mark.parametrize("n_ports, data_width, defer_ar, profile, test_level", generate_params())
def test_onyx_core_rig(request, n_ports, data_width, defer_ar, profile, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, _rtl_dict = get_paths({})
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=FILELIST)
    verilog_sources = list(verilog_sources) + [os.path.join(repo_root, HARNESS)]

    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    name = (f"test_onyx_core_rig_n{n_ports}_d{data_width:03d}_def{defer_ar}_{profile}"
            f"_{test_level}_{reg_level}")
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{name}.xml')

    rtl_parameters = {'N_PORTS': str(n_ports), 'ADDR_WIDTH': '32', 'LINE_BYTES': '64',
                      'BUS_WIDTH': str(data_width), 'AXI_ID_WIDTH': '8',
                      'SLOTS': str(n_ports * 4), 'SNOOP_INFLIGHT': '2',
                      'DEFER_AR': str(defer_ar), 'SERIAL_MODE': '0'}
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': DUT_TOP,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_LEVEL': test_level,
        'TEST_N_PORTS': str(n_ports),
        'TEST_ADDR_WIDTH': '32',
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_LINE_BYTES': '64',
        'TEST_PROFILE': profile,
        'TEST_HOT_LINES': '8',
        'TEST_CLK_PERIOD': '10',
    }
    compile_args = ["-Wall", "-Wno-SYNCASYNCNET", "-DUSE_ASYNC_RESET", "-Wno-UNUSED",
                    "-Wno-DECLFILENAME", "-Wno-PINCONNECTEMPTY"]
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
            testcase="cocotb_test_onyx_core_rig",
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
        print(f"onyx_core_rig {name} FAILED: {e}; log {log_path}")
        raise
