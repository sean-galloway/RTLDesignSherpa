"""
amber_control test runner

Blocking-pipeline control FSM vs the Task 2 gem5-derived oracle, at two
geometries: the tiny formal configuration (16 sets / 2 ways) and the
proposed default (128 sets / 4 ways). The DUT is the test harness
amber_control_th (control + landed tag/data/repl arrays + partner-stub
pins); the TB models partner handshake timing only (D-12).

Levels: gate = InitWalk + directed HitSequence smoke; func = + MissSequence
(clean + dirty victim, upgrade) + sticky CTRL_ERROR; full = + randomized
oracle-lockstep stream (10k transactions). Seeds are pinned per test node
by the repo-root conftest.

One generated test function per (geometry, level) cell so the node ids are
the exact required names (test_amber_control_s016w2_gate et al.); the
REG_LEVEL grid selects which cells exist, as everywhere else.

Author: RTL Design Sherpa
Created: 2026-10-07
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

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_control_tb import AmberControlTB

FILELIST_DIR = 'projects/components/cache-ip/amber-mesi-l1/rtl/filelists'
# test-side harness wrapper (pure wiring; lives with the test, not in an RTL
# filelist -- the same sanctioned pattern as other tb_*.sv harnesses)
HARNESS = 'projects/components/cache-ip/amber-mesi-l1/dv/tb/amber_control_th.sv'

# (sets, ways): tiny formal config + proposed geometry
GEOMS = [
    (16, 2),
    (128, 4),
]

DUT_TOP = 'amber_control_th'
TEST_PREFIX = 'amber_control'


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_amber_control(dut):
    tb = AmberControlTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"amber_control: {report['mismatches']} mismatches in {report['checks']} checks"


def _run_cell(request, sets, ways, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amber': 'projects/components/cache-ip/amber-mesi-l1/rtl/fub',
    })
    # Merge the closure filelists (control + the landed arrays/repl it
    # drives), dedup'ing the shared package include order-preserving.
    verilog_sources = []
    for fl in ('amber_control', 'amber_tag_array',
               'amber_data_array', 'amber_repl'):
        srcs, includes = get_sources_from_filelist(
            repo_root=repo_root,
            filelist_path=f'{FILELIST_DIR}/{fl}.f')
        for s in srcs:
            if s not in verilog_sources:
                verilog_sources.append(s)
    verilog_sources = verilog_sources + [os.path.join(repo_root, HARNESS)]

    test_name_plus_params = (f"test_{TEST_PREFIX}"
                             f"_s{TBBase.format_dec(sets, 3)}w{ways}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {'SETS': str(sets), 'WAYS': str(ways)}
    extra_env = level_env(test_level, SETS=sets, WAYS=ways,
                          DUT=TEST_PREFIX, LOG_PATH=log_path,
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
            toplevel=DUT_TOP,
            module=module,
            testcase="cocotb_test_amber_control",
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


def _generate_cells():
    """One test function per (geometry, level) cell -> exact node ids."""
    for sets, ways in GEOMS:
        for test_level in reg_level_grid():
            name = (f"test_{TEST_PREFIX}"
                    f"_s{TBBase.format_dec(sets, 3)}w{ways}_{test_level}")

            def make(s=sets, w=ways, lvl=test_level, n=name):
                def _cell(request):
                    _run_cell(request, s, w, lvl)
                _cell.__name__ = n
                _cell.__doc__ = (f"amber_control {n}: blocking pipeline FSM "
                                 f"vs oracle (geometry s{s}/w{w}, level {lvl})")
                return _cell

            globals()[name] = make()


_generate_cells()
