"""
rs_error_injector test runner

The error injector through the GAXI BFMs: exact count, burst, rate and none,
scored on the in/out symbol difference and on its statistics outputs.

Author: RTL Design Sherpa
Created: 2026-09-30
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

from projects.components.ecc_ip.reed_solomon.dv.tbclasses.rs_injector_tb import RSInjectorTB

FILELIST = 'projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_error_injector.f'

# (symbol_width, t, n, symbols_per_beat)
PROFILES = [
    (8, 8, 255, 1),
    (8, 8, 252, 4),   # the Nexys A7 loop harness profile
    (8, 1, 21, 4),
    (4, 2, 15, 3),
]


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_rs_error_injector(dut):
    tb = RSInjectorTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run_all()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"rs_error_injector: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("symbol_width, t, n, spb", PROFILES)
def test_rs_error_injector(request, symbol_width, t, n, spb, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rs': 'projects/components/ecc-ip/reed-solomon/rtl',
    })
    dut_name = "rs_error_injector"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=FILELIST)

    test_name_plus_params = (f"test_{dut_name}_m{TBBase.format_dec(symbol_width, 2)}"
                             f"_n{TBBase.format_dec(n, 3)}_t{TBBase.format_dec(t, 2)}_s{spb}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {'SYMBOL_WIDTH': str(symbol_width), 'T_SYMBOLS': str(t), 'N_SYMBOLS': str(n),
                      'SYMBOLS_PER_BEAT': str(spb)}
    extra_env = level_env(test_level, DUT=dut_name, LOG_PATH=log_path, COCOTB_LOG_LEVEL='INFO')

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
            testcase="cocotb_test_rs_error_injector",
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
