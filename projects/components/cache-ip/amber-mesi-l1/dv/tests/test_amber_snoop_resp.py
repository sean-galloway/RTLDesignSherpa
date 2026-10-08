"""
amber_snoop_resp test runner

ACE snoop responder across the geometry grid (proposed 64-bit bus / 64 B
lines and a narrow 32-bit bus / 32 B lines, both 8 fill beats), closed loop
with the real control (Task 7): the DUT is the harness amber_snoop_resp_th
(REAL amber_control + landed tag/data/repl arrays + REAL amber_snoop_resp on
the house axi4ace_snoop_slave transport). The AXI4ACESnoopMaster drives the
ACE pins; the TB keeps random CPU traffic flowing on the second port.

Levels: gate runs every reachable HAS Table 3.0 cell as a directed
transaction; func/full are randomized soaks over an evolving line-state
model (refill = the CPU re-acquiring the line) plus the
SnoopVictimLineDuringGather composition and the real_control_loop
(randomized snoops against an amber simultaneously serving random CPU
traffic -- both ports live, per-transaction ACE compliance).

Author: RTL Design Sherpa
Created: 2026-10-06 (closed-loop integration 2026-10-08, Task 7)
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

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_snoop_resp_tb import AmberSnoopRespTB

FILELIST_DIR = 'projects/components/cache-ip/amber-mesi-l1/rtl/filelists'
# test-side harness wrapper (pure wiring; lives with the test, not in an RTL
# filelist -- the same sanctioned pattern as amber_control_th.sv)
HARNESS = 'projects/components/cache-ip/amber-mesi-l1/dv/tb/amber_snoop_resp_th.sv'

# (addr_width, data_width, line_bytes)
GEOMS = [
    (32, 64, 64),
    (32, 32, 32),
]

DUT_TOP = 'amber_snoop_resp_th'
TEST_PREFIX = 'amber_snoop_resp'


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_amber_snoop_resp(dut):
    tb = AmberSnoopRespTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"amber_snoop_resp: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("addr_width,data_width,line_bytes", GEOMS)
def test_amber_snoop_resp(request, addr_width, data_width, line_bytes, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amber': 'projects/components/cache-ip/amber-mesi-l1/rtl/fub',
    })
    # Merge the closure filelists (snoop responder + control + the landed
    # arrays/repl it drives), dedup'ing the shared package include
    # order-preserving.
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

    test_name_plus_params = f"test_{TEST_PREFIX}_b{data_width}_{test_level}"
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
                      'LINE_BYTES': str(line_bytes)}
    extra_env = level_env(test_level, ADDR_WIDTH=addr_width, DATA_WIDTH=data_width,
                          LINE_BYTES=line_bytes, DUT=TEST_PREFIX, LOG_PATH=log_path,
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
            testcase="cocotb_test_amber_snoop_resp",
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
