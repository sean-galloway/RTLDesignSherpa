"""
jet_mshr test runner

The MAB (miss address buffer) file: fully-associative CAM of outstanding
misses + per-set victim-claim counters. Pin-level stimulus scored against
the TB's Python golden model (MAS ch02_blocks/02 contract), at the J1
default geometry (MSHR_COUNT=8, SETS=128, WAYS=4).

Author: RTL Design Sherpa
Created: 2026-10-28
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

from projects.components.cache_ip.jet_mesi_l1.dv.tbclasses.jet_mshr_tb import JetMshrTB

FILELIST_DIR = 'projects/components/cache-ip/jet-mesi-l1/rtl/filelists'
# test-side harness wrapper (pure wiring; lives with the test, not in an RTL
# filelist -- the same sanctioned pattern as other tb_*.sv harnesses)
HARNESS = 'projects/components/cache-ip/jet-mesi-l1/dv/tb/jet_mshr_th.sv'

# (mshr_count, sets, ways): J1 default geometry. The 2/4/8/16 MSHR_COUNT
# sweep is the J7 experiment, not a unit-TB grid cell.
GEOMS = [
    (8, 128, 4),
]


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_jet_mshr(dut):
    tb = JetMshrTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"jet_mshr: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("mshr_count,sets,ways", GEOMS)
def test_jet_mshr(request, mshr_count, sets, ways, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    dut_name = "jet_mshr_th"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=f'{FILELIST_DIR}/jet_mshr.f')
    verilog_sources = verilog_sources + [os.path.join(repo_root, HARNESS)]

    test_name_plus_params = (f"test_{dut_name}_m{mshr_count}"
                             f"_s{TBBase.format_dec(sets, 3)}w{ways}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)

    rtl_parameters = {'MSHR_COUNT': str(mshr_count), 'SETS': str(sets),
                      'WAYS': str(ways)}
    extra_env = level_env(test_level, MSHR_COUNT=mshr_count, SETS=sets,
                          WAYS=ways, DUT=dut_name, LOG_PATH=log_path,
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
            testcase="cocotb_test_jet_mshr",
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
