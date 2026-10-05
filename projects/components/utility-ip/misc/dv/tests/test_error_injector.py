"""
error_injector test runner

Unified bit/symbol error injector.  Exercises all eight injection modes
(NONE, COUNT, BURST, RATE, CLUSTERS, LOCALIZED, BADBLOCK, DEBUG), keep gating,
erasure marking, full backpressure, and statistics counters.
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

from projects.components.utility_ip.misc.dv.tbclasses.error_injector_tb import ErrorInjectorTB

FILELIST = 'projects/components/utility-ip/misc/rtl/filelists/error_injector.f'

# (symbol_width, t_symbols, n_symbols, symbols_per_beat)
CONFIGS = [
    (1, 2, 63, 8),       # fast bit
    (1, 8, 4224, 32),    # board-shaped bit
    (8, 2, 15, 4),       # fast symbol
    (8, 8, 255, 1),      # board-shaped symbol
]


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_error_injector(dut):
    tb = ErrorInjectorTB(dut)
    await tb.setup_clocks_and_reset()
    ok = True
    ok &= await tb.run_none_mode()
    ok &= await tb.run_count_mode()
    ok &= await tb.run_burst_mode()
    ok &= await tb.run_debug_mode()
    ok &= await tb.run_mark_phase()
    ok &= await tb.run_rate_mode()
    ok &= await tb.run_keep_awareness()
    ok &= await tb.run_clusters_mode()
    ok &= await tb.run_localized_mode()
    ok &= await tb.run_badblock_mode()
    ok &= await tb.run_backpressure()
    ok &= await tb.run_stats()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"error_injector: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("symbol_width, t_symbols, n_symbols, symbols_per_beat", CONFIGS)
def test_error_injector(request, symbol_width, t_symbols, n_symbols, symbols_per_beat, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_misc': 'projects/components/utility-ip/misc/rtl',
    })
    dut_name = "error_injector"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=FILELIST)

    test_name_plus_params = (f"test_{dut_name}_m{TBBase.format_dec(symbol_width, 2)}"
                             f"_n{TBBase.format_dec(n_symbols, 4)}"
                             f"_t{TBBase.format_dec(t_symbols, 2)}"
                             f"_s{TBBase.format_dec(symbols_per_beat, 2)}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        'SYMBOL_WIDTH': str(symbol_width),
        'T_SYMBOLS': str(t_symbols),
        'N_SYMBOLS': str(n_symbols),
        'SYMBOLS_PER_BEAT': str(symbols_per_beat),
    }
    extra_env = level_env(test_level, DUT=dut_name, LOG_PATH=log_path, COCOTB_LOG_LEVEL='INFO')

    base_compile_args = []
    compile_args = (base_compile_args + ["--trace-fst", "--trace-structs", "--trace-depth", "99"]) if enable_waves else base_compile_args
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
            testcase="cocotb_test_error_injector",
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
