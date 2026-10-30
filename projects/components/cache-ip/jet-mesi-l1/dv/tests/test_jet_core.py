"""
jet_top full-core oracle-lockstep test runner

The Task-8 integration: jet_top (the pair-rig top: jet_control + the jet
FUBs + the REAL common-ip arrays/engines/frontend/snoop/monlite + the
house axi4_master_*_monlite transports and MonBus arbiter) driven at its
external boundary -- CPU GAXI, monlite-wrapped AXI4 memory masters closed
by the house responders on a shared MemoryModel, the ACE snoop port by
the house snoop master.  The event-stream scoreboard (JetCoreTB, built
on the inherited AmberControlTB machinery) keeps per-line coherence
lockstep against the gem5-derived oracle, windowed timing properties
(fill launch within W of alloc; response release in issue order), the
sticky CTRL_ERROR contract, and the Task-8 killed-upgrade demote corner.

Grid (Task 12, MAS ch06/02): gate/func run the J1 default cell
(MSHR_COUNT=8, VICTIM_DEPTH=2, SETS=128, WAYS=4, LRU); full runs the
sign-off sweep -- geometry {tiny 16/2, default 128/4} x MSHR_COUNT
{2,4,8,16} x VICTIM_DEPTH {1,2,4} x policy {LRU,FIFO,RANDOM}, corners
(MSHR {2,16} x VICTIM {1,4}) x all policies x both geometries plus
interior samples.  Seeds are pinned per node by the repo-root conftest.

One generated test function per (geometry, knobs, policy, level) cell so
the node ids are exact (test_jet_core_s128w4_m08v2_lru_full et al).

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

from projects.components.cache_ip.jet_mesi_l1.dv.tbclasses.jet_core_tb import JetCoreTB

JET_FL = 'projects/components/cache-ip/jet-mesi-l1/rtl/filelists'
# test-side harness wrapper (pure wiring; lives with the test, not in an
# RTL filelist -- the same sanctioned pattern as the other tb harnesses)
HARNESS = 'projects/components/cache-ip/jet-mesi-l1/dv/tb/jet_core_th.sv'

# (sets, ways): tiny formal config + pkg default
GEOMS = [
    (128, 4),
    (16, 2),
]

# (mshr_count, victim_depth, repl_policy): the J1/J5/pkg-default cell
DEFAULT_KNOBS = (8, 2, 0)

# policy axis: amber_repl_t encodings (l1_pkg).  tree-PLRU is covered by
# the RTL self-check, not the grid (ch06/02).
GRID_POLICIES = ((0, 'lru'), (2, 'fifo'), (3, 'rand'))

# FULL sign-off grid (ch06/02): run the corners, sample the interior.
# corners: MSHR {2,16} x VICTIM {1,4} x every policy x both geometries
CORNER_MSHR = (2, 16)
CORNER_VIC = (1, 4)
# interior samples: (mshr, victim, repl_policy) at both geometries
INTERIOR = [
    (4, 2, 0), (8, 2, 0),      # LRU mid-file (8/2 is the J1 default)
    (4, 2, 2), (8, 2, 3),      # FIFO / RANDOM mid-file
]


@cocotb.test(timeout_time=1800, timeout_unit="ms")
async def cocotb_test_jet_core(dut):
    tb = JetCoreTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"jet_core: {report['mismatches']} mismatches in {report['checks']} checks"


def _run_cell(request, sets, ways, mshr, victim, repl, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    dut_name = "jet_core_th"
    verilog_sources = []
    includes = []
    for fl in ('jet_top',):
        srcs, incs = get_sources_from_filelist(
            repo_root=repo_root, filelist_path=f'{JET_FL}/{fl}.f')
        for s in srcs:
            if s not in verilog_sources:
                verilog_sources.append(s)
        for i in incs:
            if i not in includes:
                includes.append(i)
    verilog_sources = verilog_sources + [os.path.join(repo_root, HARNESS)]

    pol_name = dict(GRID_POLICIES)[repl]
    if test_level == 'full':
        test_name_plus_params = (
            f"test_{dut_name}"
            f"_s{TBBase.format_dec(sets, 3)}w{ways}"
            f"_m{TBBase.format_dec(mshr, 2)}v{victim}_{pol_name}"
            f"_{test_level}")
    else:
        # gate/func run the default cell; keep the short node id
        test_name_plus_params = (f"test_{dut_name}"
                                 f"_s{TBBase.format_dec(sets, 3)}w{ways}"
                                 f"_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)

    rtl_parameters = {'SETS': str(sets), 'WAYS': str(ways),
                      'MSHR_COUNT': str(mshr), 'VICTIM_DEPTH': str(victim),
                      'REPL_POLICY': str(repl)}
    extra_env = level_env(test_level, SETS=sets, WAYS=ways,
                          MSHR_COUNT=mshr, VICTIM_DEPTH=victim,
                          REPL_POLICY=repl,
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
            testcase="cocotb_test_jet_core",
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
    """One test function per (geometry, knobs, policy, level) cell.

    gate/func: the default-knob cells at both geometries (the directed
    suite + the short soak).  full: the ch06/02 sign-off grid -- every
    corner plus the interior samples.
    """
    for test_level in reg_level_grid():
        if test_level == 'full':
            cells = []
            for sets, ways in GEOMS:
                for repl, _pol in GRID_POLICIES:
                    for mshr in CORNER_MSHR:
                        for victim in CORNER_VIC:
                            cells.append((sets, ways, mshr, victim, repl))
                for sets, ways in GEOMS:
                    for mshr, victim, repl in INTERIOR:
                        cells.append((sets, ways, mshr, victim, repl))
        else:
            cells = [(sets, ways) + DEFAULT_KNOBS for sets, ways in GEOMS]
        for sets, ways, mshr, victim, repl in cells:
            pol_name = dict(GRID_POLICIES)[repl]
            if test_level == 'full':
                name = (f"test_jet_core"
                        f"_s{TBBase.format_dec(sets, 3)}w{ways}"
                        f"_m{TBBase.format_dec(mshr, 2)}v{victim}"
                        f"_{pol_name}_full")
            else:
                name = (f"test_jet_core"
                        f"_s{TBBase.format_dec(sets, 3)}w{ways}"
                        f"_{test_level}")

            def make(s=sets, w=ways, m=mshr, v=victim, r=repl,
                     lvl=test_level, n=name):
                def _cell(request):
                    _run_cell(request, s, w, m, v, r, lvl)
                _cell.__name__ = n
                _cell.__doc__ = (f"jet_core {n}: jet_top event-stream "
                                 f"lockstep (geometry s{s}/w{w}, "
                                 f"MSHR={m}, VICTIM={v}, policy "
                                 f"{pol_name}, level {lvl})")
                return _cell

            globals()[name] = make()


_generate_cells()
