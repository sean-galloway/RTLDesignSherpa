"""
l1_monlite test runner

Drop-and-count MonBus observer across the geometry grid (64-bit bus /
64 B lines and 32-bit bus / 32 B lines): the DUT is the harness
l1_monlite_th (the l1_cpu_frontend_th closure -- REAL l1_cpu_frontend
+ REAL l1_control + landed arrays -- plus l1_monlite tapped at the
MAS ch04 emit points). The observer drives nothing in the closure; its
only outputs are the monbus handshake pins, consumed by direct pin
observation (the house MonbusSlave BFM family is the reference consumer;
this suite scores the packet stream against an independent event model).

A second dimension, mon_mode, selects the observer configuration:
  tap   -- USE_MONITOR=1 (the observer live; drop-and-count exercised)
  notap -- USE_MONITOR=0 (house gen_no_monitor tie-off; asserted silent)

Levels: gate = Table 4.1.1 EventClassMatrix + per-packet format +
present-vs-absent; func = + directed DropAndCount; full = + randomized
soak with randomized monbus backpressure and the accounting identity.

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

from projects.components.cache_ip.common_ip.dv.tbclasses.l1_monlite_tb import L1MonliteTB

FILELIST_DIR = 'projects/components/cache-ip/common-ip/rtl/filelists'
# test-side harness wrappers (pure wiring + observer taps; live with the
# test, not in an RTL filelist -- the same sanctioned pattern as
# l1_control_th.sv). l1_cpu_frontend_th is the closure under
# observation; l1_monlite_th wraps it with the observer taps.
HARNESS_CORE = 'projects/components/cache-ip/common-ip/dv/tb/l1_cpu_frontend_th.sv'
HARNESS = 'projects/components/cache-ip/common-ip/dv/tb/l1_monlite_th.sv'

# (addr_width, data_width, line_bytes)
GEOMS = [
    (32, 64, 64),
    (32, 32, 32),
]

# observer configuration: tap (USE_MONITOR=1) / notap (USE_MONITOR=0)
MON_MODES = ['tap', 'notap']

DUT_TOP = 'l1_monlite_th'
TEST_PREFIX = 'l1_monlite'


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_l1_monlite(dut):
    tb = L1MonliteTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"l1_monlite: {report['mismatches']} mismatches in {report['checks']} checks"


def _run_cell(request, addr_width, data_width, line_bytes, test_level, mon_mode):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_common': 'projects/components/cache-ip/common-ip/rtl/fub',
    })
    # Merge the closure filelists (monlite + frontend + control + the
    # landed arrays/repl), dedup'ing the shared packages order-preserving.
    verilog_sources = []
    includes = []
    for fl in ('l1_monlite', 'l1_frontend', 'l1_control',
               'l1_tag_array', 'l1_data_array', 'l1_repl'):
        srcs, incs = get_sources_from_filelist(
            repo_root=repo_root,
            filelist_path=f'{FILELIST_DIR}/{fl}.f')
        for s in srcs:
            if s not in verilog_sources:
                verilog_sources.append(s)
        for i in incs:
            if i not in includes:
                includes.append(i)
    verilog_sources = verilog_sources + [os.path.join(repo_root, HARNESS_CORE),
                                         os.path.join(repo_root, HARNESS)]

    use_monitor = '1' if mon_mode == 'tap' else '0'
    test_name_plus_params = f"test_{TEST_PREFIX}_{mon_mode}_b{data_width}_{test_level}"
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {'ADDR_WIDTH': str(addr_width), 'BUS_WIDTH': str(data_width),
                      'LINE_BYTES': str(line_bytes), 'USE_MONITOR': use_monitor}
    extra_env = level_env(test_level, ADDR_WIDTH=addr_width, DATA_WIDTH=data_width,
                          LINE_BYTES=line_bytes, MON_CFG=mon_mode,
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
            testcase="cocotb_test_l1_monlite",
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


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("mon_mode", MON_MODES)
@pytest.mark.parametrize("addr_width,data_width,line_bytes", GEOMS)
def test_l1_monlite(request, addr_width, data_width, line_bytes, test_level,
                       mon_mode):
    _run_cell(request, addr_width, data_width, line_bytes, test_level, mon_mode)
