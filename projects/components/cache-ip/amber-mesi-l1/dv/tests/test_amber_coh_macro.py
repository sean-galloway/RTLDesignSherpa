"""
amber_coh_macro test runner

Macro composition suite 4 (Task 9.5): the coherence/snoop loop group --
control + snoop_resp + pending_fill_bypass + victim -- the promoted Task 7
ad-hoc composition (amber_snoop_resp_th + real_control_loop) as a named
macro regression cell. The DUT is the test wrapper amber_coh_macro_test:
REAL amber_control (with the pending_fill_bypass / victim leaves) + landed
tag/data/repl arrays + REAL amber_snoop_resp on the house
axi4ace_snoop_slave transport; fill/drain partner timing stubbed (D-12).
Snoops enter at the ACE boundary only; the ctrl_* snoop handshake is
internal to the wrapper and observed through taps.

The Task 7 found-and-fixed pins travel here: EWriteHitPromotes (HIT_WR
E->M promotion one-hot, amber_control.sv:944) and the cross-set way+tag
collision stale-grant checks (sn_stale_gnt set-narrowing, :531-535) via
the real_control_loop stale-victim discrimination.

Geometries: tiny formal config (16 sets / 2 ways) + pkg default (128 / 4);
32-bit address, 64-bit bus, 64 B lines throughout. Levels: gate =
table30_directed + EWriteHitPromotes; func = + pool soak + zero-gap AC
pairs + SnoopVictimLineDuringGather + real_control_loop; full = deeper
soak/loop (the T7 pins must stay green at FULL).

One generated test function per (geometry, level) cell so the node ids are
the exact required names (test_amber_coh_macro_s016w2_gate et al).

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

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_coh_macro_tb import (
    AmberCohMacroTB,
)

FILELIST_DIR = 'projects/components/cache-ip/amber-mesi-l1/rtl/filelists'
# test-side wrapper (pure wiring; lives with the test, not in an RTL
# filelist -- the same sanctioned pattern as amber_snoop_resp_th.sv)
HARNESS = 'projects/components/cache-ip/amber-mesi-l1/dv/tb/amber_coh_macro_test.sv'

# (sets, ways): tiny formal config + proposed geometry; the responder
# geometry (32-bit addr / 64-bit bus / 64 B line) is fixed, matching the
# macro bring-up ladder convention (only SETS/WAYS vary)
GEOMS = [
    (16, 2),
    (128, 4),
]

DUT_TOP = 'amber_coh_macro_test'
TEST_PREFIX = 'amber_coh_macro'


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_amber_coh_macro(dut):
    tb = AmberCohMacroTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"amber_coh_macro: {report['mismatches']} mismatches in {report['checks']} checks"


def _run_cell(request, sets, ways, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amber': 'projects/components/cache-ip/amber-mesi-l1/rtl/fub',
    })
    # Merge the closure filelists (snoop responder + control + the landed
    # arrays/repl it drives), dedup'ing the shared package include
    # order-preserving -- the same set the promoted Task 7 suite uses.
    verilog_sources = []
    includes = []
    for fl in ('amber_snoop_resp', 'amber_control',
               'amber_tag_array', 'amber_data_array', 'amber_repl'):
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
                          ADDR_WIDTH='32', DATA_WIDTH='64', LINE_BYTES='64',
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
            testcase="cocotb_test_amber_coh_macro",
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
                _cell.__doc__ = (f"amber_coh_macro {n}: coherence/snoop "
                                 f"loop group (promoted Task 7 composition) "
                                 f"vs oracle (geometry s{s}/w{w}, "
                                 f"level {lvl})")
                return _cell

            globals()[name] = make()


_generate_cells()
