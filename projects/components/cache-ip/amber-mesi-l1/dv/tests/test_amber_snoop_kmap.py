"""
amber_snoop_kmap test runner

Combinational {state, snoop} -> {CRRESP, next_state} decode against an
independent copy of the amber HAS Table 3.0 truth table. Exhaustive at func
(reserved encodings contract to the safe default) and full (whole 3-bit x
3-bit space).

Author: RTL Design Sherpa
Created: 2026-10-06
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

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_snoop_kmap_tb import AmberSnoopKmapTB

FILELIST_DIR = 'projects/components/cache-ip/amber-mesi-l1/rtl/filelists'


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_amber_snoop_kmap(dut):
    tb = AmberSnoopKmapTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"amber_snoop_kmap: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_amber_snoop_kmap(request, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amber': 'projects/components/cache-ip/amber-mesi-l1/rtl/fub',
    })
    dut_name = "amber_snoop_kmap"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=f'{FILELIST_DIR}/amber_snoop_kmap.f')

    test_name_plus_params = f"test_{dut_name}_{test_level}"
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    extra_env = level_env(test_level, DUT=dut_name, LOG_PATH=log_path,
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
            testcase="cocotb_test_amber_snoop_kmap",
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
