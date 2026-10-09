"""
amber_core test runner

First end-to-end cache top (Task 9): the shipping amber_core composes all
nine landed FUBs with no stubs. The DUT is amber_core itself (no test
harness -- the core's external shape IS the boundary: CPU GAXI slave,
fub_axi_* rd/wr master sides, ACE snoop port, MonBus, coh_req sideband).
The TB closes the memory side with the house AXI4 slave responders on the
raw fub_axi_* pins and the house ACE snoop master on the snoop port, and
scores against the Task 2 gem5-derived oracle.

Geometries: the bring-up smoke config from the Task 9 brief (4 sets / 2
ways / 32 B lines / 32-bit bus, FIFO replacement), the tiny formal config
(16/2/64/64), and the pkg default (128/4/64/64). Levels: gate = InitWalk +
FirstHitLatency + directed CPU/snoop sequences; func = + randomized oracle
lockstep with mid-miss snoops, MonBus tally cross-check, monbus congestion;
full = + 5k-transaction soak. Seeds are pinned per test node by the
repo-root conftest.

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

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_core_tb import AmberCoreTB

FILELIST_DIR = 'projects/components/cache-ip/amber-mesi-l1/rtl/filelists'
DUT_TOP = 'amber_core'
TEST_PREFIX = 'amber_core'

# (sets, ways, line_bytes, bus_width, repl_policy): amber_repl_t encodings
GEOMS = [
    (4, 2, 32, 32, 2),      # bring-up smoke, FIFO
    (16, 2, 64, 64, 0),     # tiny (formal config), LRU
    (128, 4, 64, 64, 0),    # pkg default, LRU
]
REPL_NAMES = {0: 'lru', 1: 'tplru', 2: 'fifo', 3: 'rand'}


@cocotb.test(timeout_time=900, timeout_unit="ms")
async def cocotb_test_amber_core(dut):
    tb = AmberCoreTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"amber_core: {report['mismatches']} mismatches in {report['checks']} checks"


def _run_cell(request, sets, ways, line_bytes, bus_width, repl_policy, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    # amber_core.f closes the whole core: the nine landed FUBs plus their
    # house deps (reset macros, monitor pkgs, gaxi_fifo_sync). No harness.
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'{FILELIST_DIR}/amber_core.f')

    pol = REPL_NAMES[repl_policy]
    test_name_plus_params = (
        f"test_{TEST_PREFIX}"
        f"_s{TBBase.format_dec(sets, 3)}w{ways}l{line_bytes}b{bus_width}"
        f"_{pol}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {'SETS': str(sets), 'WAYS': str(ways),
                      'LINE_BYTES': str(line_bytes), 'BUS_WIDTH': str(bus_width),
                      'REPL_POLICY': str(repl_policy)}
    extra_env = level_env(test_level, SETS=sets, WAYS=ways,
                          LINE_BYTES=line_bytes, BUS_WIDTH=bus_width,
                          REPL_POLICY=repl_policy,
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
            testcase="cocotb_test_amber_core",
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
    for sets, ways, line_bytes, bus_width, repl_policy in GEOMS:
        for test_level in reg_level_grid():
            pol = REPL_NAMES[repl_policy]
            name = (f"test_{TEST_PREFIX}"
                    f"_s{TBBase.format_dec(sets, 3)}w{ways}l{line_bytes}b{bus_width}"
                    f"_{pol}_{test_level}")

            def make(s=sets, w=ways, lb=line_bytes, bw=bus_width, rp=repl_policy,
                     lvl=test_level, n=name):
                def _cell(request):
                    _run_cell(request, s, w, lb, bw, rp, lvl)
                _cell.__name__ = n
                _cell.__doc__ = (f"amber_core {n}: end-to-end top vs oracle "
                                 f"(geometry s{s}/w{w}/l{lb}/b{bw} pol={pol}, "
                                 f"level {lvl})")
                return _cell

            globals()[name] = make()


_generate_cells()
