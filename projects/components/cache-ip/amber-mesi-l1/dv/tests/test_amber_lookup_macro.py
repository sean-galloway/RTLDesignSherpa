"""
amber_lookup_macro test runner

Macro composition suite 1 (Task 9.5): the lookup dataplane group --
control + tag_array + data_array + repl -- pinned in isolation between the
unit suites and amber_core. The DUT is the test wrapper
amber_lookup_macro_test (the group's landed FUBs composed exactly like the
control harness: pure wiring + the array write-port / port-B muxes), with
fill/drain/victim/snoop partner timing stubbed at the boundary (D-12).

Scenarios: init-walk interaction with the real arrays, hit/miss decode +
multi-way compare, promotion (write-hit E/S -> M), victim selection parity
with the repl engine, randomized oracle-lockstep soak over the group.

Geometries: tiny formal config (16 sets / 2 ways) + pkg default (128 / 4);
line 64 B, bus 64-bit throughout. Levels: gate = InitWalk + directed
hit/miss/promotion sequence; func = + randomized lockstep soak. Seeds are
pinned per test node by the repo-root conftest.

One generated test function per (geometry, level) cell so the node ids are
the exact required names (test_amber_lookup_macro_s016w2_gate et al).

Author: RTL Design Sherpa
Created: 2026-10-08
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

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_lookup_macro_tb import (
    AmberLookupMacroTB,
)

FILELIST_DIR = 'projects/components/cache-ip/amber-mesi-l1/rtl/filelists'
# test-side wrapper (pure wiring; lives with the test, not in an RTL
# filelist -- the same sanctioned pattern as the other tb_* harnesses)
HARNESS = 'projects/components/cache-ip/amber-mesi-l1/dv/tb/amber_lookup_macro_test.sv'

# (sets, ways): tiny formal config + proposed geometry
GEOMS = [
    (16, 2),
    (128, 4),
]

DUT_TOP = 'amber_lookup_macro_test'
TEST_PREFIX = 'amber_lookup_macro'


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_amber_lookup_macro(dut):
    tb = AmberLookupMacroTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"amber_lookup_macro: {report['mismatches']} mismatches in {report['checks']} checks"


def _run_cell(request, sets, ways, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amber': 'projects/components/cache-ip/amber-mesi-l1/rtl/fub',
    })
    # Merge the group closure filelists (control carries the
    # pending_fill_bypass / victim leaves; the arrays + repl close the
    # dataplane), dedup'ing the shared package include order-preserving.
    verilog_sources = []
    includes = []
    for fl in ('amber_control', 'amber_tag_array',
               'amber_data_array', 'amber_repl'):
        srcs, incs = get_sources_from_filelist(
            repo_root=repo_root,
            filelist_path=f'{FILELIST_DIR}/{fl}.f')
        for s in srcs:
            if s not in verilog_sources:
                verilog_sources.append(s)
        for i in incs:
            if i not in includes:
                includes.append(i)
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
            testcase="cocotb_test_amber_lookup_macro",
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
                _cell.__doc__ = (f"amber_lookup_macro {n}: lookup dataplane "
                                 f"group vs oracle (geometry s{s}/w{w}, "
                                 f"level {lvl})")
                return _cell

            globals()[name] = make()


_generate_cells()
