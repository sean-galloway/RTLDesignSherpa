"""
jet_prime_fill test runner

The multi-outstanding AXI4 read fill engine (jet-prime TASK-001 step 2):
one read ID per MSHR entry plus the no-data upgrade slot, R demuxed by ID,
beats placed by the launch's claimed set/way.  Pin-level stimulus on the
launch seam, the house AXI4 slave read BFM on the fub_axi pins (in-order
at gate; out-of-order at func, interleaved R at full), scored per launch
by the TB's own monitor.  Two cells: the engine at its full in-flight
depth, and FILL_INFLIGHT=1 (the pair rig's single-outstanding setting
until the fabric is rebuilt in step 3).

Author: RTL Design Sherpa
Created: 2026-11-15
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

from projects.components.cache_ip.jet_prime_mesi_l1.dv.tbclasses.jet_prime_fill_tb import JetFillTB

FILELIST_DIR = 'projects/components/cache-ip/jet-prime-mesi-l1/rtl/filelists'

# (mshr_count, fill_inflight): the engine at full depth (every entry and
# the upgrade in flight) and at 1 (the single-outstanding contract the pair
# fabric still relies on)
GEOMS = [
    (8, 9),
    (8, 1),
]


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_jet_prime_fill(dut):
    tb = JetFillTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"jet_prime_fill: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("mshr_count,fill_inflight", GEOMS)
def test_jet_prime_fill(request, mshr_count, fill_inflight, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    dut_name = "jet_prime_fill"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=f'{FILELIST_DIR}/jet_prime_fill.f')

    test_name_plus_params = (f"test_{dut_name}_m{mshr_count}"
                             f"_inflight{fill_inflight}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)

    rtl_parameters = {'MSHR_COUNT': str(mshr_count),
                      'FILL_INFLIGHT': str(fill_inflight)}
    extra_env = level_env(test_level, MSHR_COUNT=mshr_count,
                          FILL_INFLIGHT=fill_inflight, DUT=dut_name,
                          LOG_PATH=log_path, COCOTB_LOG_LEVEL='INFO')

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
            testcase="cocotb_test_jet_prime_fill",
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
