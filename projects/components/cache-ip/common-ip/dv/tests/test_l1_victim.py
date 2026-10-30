"""
l1_victim test runner

Depth-1 victim buffer leaf: reset values, load/clear handshake, the
load-while-busy ignore path (not stimulus-reachable in integration),
clear-wins coincidence, and a randomized strobe soak -- scored every
settled cycle against a Python golden model of the register.

Author: RTL Design Sherpa
Created: 2026-10-30
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

from projects.components.cache_ip.common_ip.dv.tbclasses.l1_victim_tb import L1VictimTB

FILELIST_DIR = 'projects/components/cache-ip/common-ip/rtl/filelists'

# (addr_width, sets, line_bytes, bus_width): proposed geometry, tiny
# formal config, narrow-bus config (16 fill beats)
GEOMS = [
    (32, 128, 64, 64),
    (32, 16, 32, 64),
    (32, 64, 64, 32),
]


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_l1_victim(dut):
    tb = L1VictimTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"l1_victim: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("addr_width,sets,line_bytes,bus_width", GEOMS)
def test_l1_victim(request, addr_width, sets, line_bytes, bus_width, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_common': 'projects/components/cache-ip/common-ip/rtl/fub',
    })
    dut_name = "l1_victim"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=f'{FILELIST_DIR}/l1_victim.f')

    test_name_plus_params = (f"test_{dut_name}"
                             f"_a{addr_width}s{TBBase.format_dec(sets, 3)}"
                             f"l{line_bytes}b{bus_width}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {'ADDR_WIDTH': str(addr_width), 'SETS': str(sets),
                      'LINE_BYTES': str(line_bytes), 'BUS_WIDTH': str(bus_width)}
    extra_env = level_env(test_level, ADDR_WIDTH=addr_width, SETS=sets,
                          LINE_BYTES=line_bytes, BUS_WIDTH=bus_width,
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
            testcase="cocotb_test_l1_victim",
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
