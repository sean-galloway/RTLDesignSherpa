"""
jet_monlite test runner

Unit test for the J7 MonBus observer (Task 10).  The harness
jet_monlite_th exposes every observer tap and a functional-side counter
that increments on alloc pulses.  The grid exercises the observer live
(MON_CFG=tap) and tied off (MON_CFG=notap) at the J1 default geometry.

Author: RTL Design Sherpa
Created: 2026-10-29
"""

import os
import sys
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.cache_ip.jet_mesi_l1.dv.tbclasses.jet_monlite_tb import JetMonliteTB

JET_FL = 'projects/components/cache-ip/jet-mesi-l1/rtl/filelists'
HARNESS = 'projects/components/cache-ip/jet-mesi-l1/dv/tb/jet_monlite_th.sv'

GEOMS = [
    (128, 4),
]


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_jet_monlite(dut):
    tb = JetMonliteTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"jet_monlite: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("sets,ways", GEOMS)
@pytest.mark.parametrize("mon_cfg", ['tap', 'notap'])
def test_jet_monlite(request, sets, ways, test_level, mon_cfg):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    dut_name = "jet_monlite_th"
    verilog_sources = []
    includes = []
    for fl in ('jet_monlite',):
        srcs, incs = get_sources_from_filelist(
            repo_root=repo_root, filelist_path=f'{JET_FL}/{fl}.f')
        for s in srcs:
            if s not in verilog_sources:
                verilog_sources.append(s)
        for i in incs:
            if i not in includes:
                includes.append(i)
    verilog_sources = verilog_sources + [os.path.join(repo_root, HARNESS)]

    test_name_plus_params = (
        f"test_{dut_name}_s{TBBase.format_dec(sets, 3)}w{ways}"
        f"_{mon_cfg}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)

    rtl_parameters = {'SETS': str(sets), 'WAYS': str(ways)}
    if mon_cfg == 'notap':
        rtl_parameters['USE_MONITOR'] = '0'
    extra_env = level_env(test_level, SETS=sets, WAYS=ways,
                          DUT=dut_name, LOG_PATH=log_path,
                          MON_CFG=mon_cfg,
                          COCOTB_LOG_LEVEL='INFO')

    compile_args = ["--trace-fst", "--trace-structs", "--trace-depth", "99"] if enable_waves else []
    sim_args = ["--trace-fst", "--trace-structs"] if enable_waves else []
    plusargs = ["+trace"] if enable_waves else []

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    print(f"\n{'='*60}\nRunning {test_name_plus_params}\nLog: {log_path}\n{'='*60}")
    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_jet_monlite",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"PASS {test_name_plus_params}")
    except Exception as e:
        print(f"FAIL {test_name_plus_params}: {e}\nLog: {log_path}\nView: {cmd_filename}")
        raise
