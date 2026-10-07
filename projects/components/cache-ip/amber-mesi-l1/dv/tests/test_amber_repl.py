"""
amber_repl test runner

Replacement-policy engine across the policy enum (LRU default, FIFO,
RANDOM, TREE_PLRU) and the geometry grid (proposed 128/4, tiny formal 16/2,
deep 64/8). The victim way is scored every request against an independent
Python golden model carried by the TB.

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

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_repl_tb import AmberReplTB

FILELIST_DIR = 'projects/components/cache-ip/amber-mesi-l1/rtl/filelists'

# (policy_name, policy_int): ints are the amber_repl_t encodings in amber_pkg
POLICIES = [
    ('lru', 0),
    ('tree_plru', 1),
    ('fifo', 2),
    ('random', 3),
]

# (sets, ways): proposed geometry, tiny formal config, deep associativity
GEOMS = [
    (128, 4),
    (16, 2),
    (64, 8),
]


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_amber_repl(dut):
    tb = AmberReplTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"amber_repl: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("sets,ways", GEOMS)
@pytest.mark.parametrize("policy_name,policy_int", POLICIES)
def test_amber_repl(request, policy_name, policy_int, sets, ways, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amber': 'projects/components/cache-ip/amber-mesi-l1/rtl/fub',
    })
    dut_name = "amber_repl"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=f'{FILELIST_DIR}/amber_repl.f')

    test_name_plus_params = (f"test_{dut_name}_{policy_name}"
                             f"_s{TBBase.format_dec(sets, 3)}w{ways}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {'SETS': str(sets), 'WAYS': str(ways),
                      'REPL_POLICY': str(policy_int)}
    extra_env = level_env(test_level, SETS=sets, WAYS=ways, POLICY=policy_name,
                          DUT=dut_name, LOG_PATH=log_path,
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
            testcase="cocotb_test_amber_repl",
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
