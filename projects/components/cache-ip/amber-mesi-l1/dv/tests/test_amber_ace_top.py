"""
amber ACE-rig test runner

Task 12: `amber_ace_issue` + `amber_ace_top` -- the onyx-rig top on ACE
masters. Two DUTs:

  * amber_ace_top (the rig): one cache against a Python onyx-D2 manager
    model on the ACE master pins. Grid: tiny formal config (16/2) + pkg
    default (128/4); 64-bit bus / 64 B lines; levels gate/func/full; a
    USE_MONITOR=0 gate cell per geometry re-runs the suite asserting
    observer non-perturbation (cells named test_amber_ace_top_*).

  * amber_ace_issue_th (pure wiring over the new combinational mapping
    block): the MAS ch02/08 Table 2.8.1 row suite -- per row, drive the
    cache event, capture ARSNOOP/AWSNOOP + address + burst, prove
    CleanUnique/MakeUnique are AW-only (no W beats) and the AW-only B
    responses are swallowed by the AWONLY_ID BID mux (cells named
    test_amber_ace_issue_rows_*).

Sign-off runs: FUNC default + FULL tiny, plus the whole local grid.

Author: RTL Design Sherpa
Created: 2026-10-09
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

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_ace_top_tb import (
    AmberAceTopTB,
)
from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_ace_issue_tb import (
    AmberAceIssueTB,
)

FILELIST_DIR = 'projects/components/cache-ip/amber-mesi-l1/rtl/filelists'
# unit-side wrapper for the ace_issue row suite (pure wiring; lives with
# the test, the same sanctioned pattern as the other *_th harnesses)
ISSUE_HARNESS = 'projects/components/cache-ip/amber-mesi-l1/dv/tb/amber_ace_issue_th.sv'

# (sets, ways, line_bytes, bus_width): tiny formal config + pkg default
GEOMS = [
    (16, 2, 64, 64),
    (128, 4, 64, 64),
]


@cocotb.test(timeout_time=1800, timeout_unit="ms")
async def cocotb_test_amber_ace_top(dut):
    tb = AmberAceTopTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"amber_ace_top: {report['mismatches']} mismatches in {report['checks']} checks"


@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_amber_ace_issue_rows(dut):
    tb = AmberAceIssueTB(dut)
    await tb.setup()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"amber_ace_issue rows: {report['mismatches']} mismatches in {report['checks']} checks"


def _merge_sources(*filelists):
    """Merge filelist closures, dedup'ing order-preserving (the macro-suite
    merge idiom)."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    verilog_sources = []
    includes = []
    for fl in filelists:
        srcs, incs = get_sources_from_filelist(
            repo_root=repo_root,
            filelist_path=f'{FILELIST_DIR}/{fl}.f')
        for s in srcs:
            if s not in verilog_sources:
                verilog_sources.append(s)
        for i in incs:
            if i not in includes:
                includes.append(i)
    return verilog_sources, includes


def _run_cell(py_module, top_module, testcase, verilog_sources, includes,
              tests_dir, log_dir, name, rtl_parameters, extra_env):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    results_path = os.path.join(log_dir, f'results_{name}.xml')

    compile_args = ["--trace-fst", "--trace-structs", "--trace-depth", "99"] if enable_waves else []
    sim_args = ["--trace-fst", "--trace-structs"] if enable_waves else []
    plusargs = ["+trace"] if enable_waves else []

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, top_module, name)
    print(f"\n{'='*60}\nRunning {name}\nLog: {log_path}\n{'='*60}")
    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=top_module,
            module=py_module,
            testcase=testcase,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"PASS {name}")
    except Exception as e:
        print(f"FAIL {name}: {e}\nLog: {log_path}\nView: {cmd_filename}")
        raise


def _run_rig_cell(request, sets, ways, line_bytes, bus_width, test_level,
                  use_monitor):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    verilog_sources, includes = _merge_sources('amber_ace_top')
    mon = 'mon' if use_monitor else 'nomon'
    test_name_plus_params = (
        f"test_amber_ace_top"
        f"_s{TBBase.format_dec(sets, 3)}w{ways}l{line_bytes}b{bus_width}"
        f"_{mon}_{test_level}")
    rtl_parameters = {'SETS': str(sets), 'WAYS': str(ways),
                      'LINE_BYTES': str(line_bytes), 'BUS_WIDTH': str(bus_width),
                      'USE_MONITOR': '1' if use_monitor else '0'}
    extra_env = level_env(test_level, SETS=sets, WAYS=ways,
                          LINE_BYTES=line_bytes, BUS_WIDTH=bus_width,
                          USE_MONITOR='1' if use_monitor else '0',
                          DUT='amber_ace_top', LOG_PATH=os.path.join(
                              log_dir, f'{test_name_plus_params}.log'),
                          COCOTB_LOG_LEVEL='INFO')
    _run_cell(module, 'amber_ace_top', 'cocotb_test_amber_ace_top',
              verilog_sources, includes, tests_dir, log_dir,
              test_name_plus_params, rtl_parameters, extra_env)


def _run_issue_cell(request, sets, ways, line_bytes, bus_width, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    verilog_sources, includes = _merge_sources('amber_ace_issue')
    verilog_sources = verilog_sources + [os.path.join(repo_root, ISSUE_HARNESS)]
    test_name_plus_params = (
        f"test_amber_ace_issue_rows"
        f"_s{TBBase.format_dec(sets, 3)}w{ways}l{line_bytes}b{bus_width}"
        f"_{test_level}")
    rtl_parameters = {'ADDR_WIDTH': '32', 'BUS_WIDTH': str(bus_width)}
    extra_env = level_env(test_level, SETS=sets, WAYS=ways,
                          LINE_BYTES=line_bytes, BUS_WIDTH=bus_width,
                          DUT='amber_ace_issue', LOG_PATH=os.path.join(
                              log_dir, f'{test_name_plus_params}.log'),
                          COCOTB_LOG_LEVEL='INFO')
    _run_cell(module, 'amber_ace_issue_th', 'cocotb_test_amber_ace_issue_rows',
              verilog_sources, includes, tests_dir, log_dir,
              test_name_plus_params, rtl_parameters, extra_env)


def _generate_cells():
    """One test function per cell -> exact node ids."""
    for sets, ways, line_bytes, bus_width in GEOMS:
        for use_monitor in (True, False):
            for test_level in reg_level_grid():
                if not use_monitor and test_level != 'gate':
                    continue   # the pva cell re-runs the gate suite
                mon = 'mon' if use_monitor else 'nomon'
                name = (f"test_amber_ace_top"
                        f"_s{TBBase.format_dec(sets, 3)}w{ways}l{line_bytes}b{bus_width}"
                        f"_{mon}_{test_level}")

                def make(s=sets, w=ways, lb=line_bytes, bw=bus_width,
                         um=use_monitor, lvl=test_level, n=name):
                    def _cell(request):
                        _run_rig_cell(request, s, w, lb, bw, lvl, um)
                    _cell.__name__ = n
                    _cell.__doc__ = (f"amber_ace_top {n}: the onyx-rig top on "
                                     f"ACE masters (geometry s{s}/w{w}/l{lb}/b{bw} "
                                     f"monitor={'on' if um else 'off'}, level {lvl})")
                    return _cell

                globals()[name] = make()

        # the Table 2.8.1 row suite rides at gate depth (fast combinational
        # unit checks); it runs alongside every rig geometry
        for test_level in ('gate',):
            name = (f"test_amber_ace_issue_rows"
                    f"_s{TBBase.format_dec(sets, 3)}w{ways}l{line_bytes}b{bus_width}"
                    f"_{test_level}")

            def make(s=sets, w=ways, lb=line_bytes, bw=bus_width,
                     lvl=test_level, n=name):
                def _cell(request):
                    _run_issue_cell(request, s, w, lb, bw, lvl)
                _cell.__name__ = n
                _cell.__doc__ = (f"amber_ace_issue rows {n}: Table 2.8.1 "
                                 f"event->transaction map (geometry "
                                 f"s{s}/w{w}/l{lb}/b{bw}, level {lvl})")
                return _cell

            globals()[name] = make()


_generate_cells()
