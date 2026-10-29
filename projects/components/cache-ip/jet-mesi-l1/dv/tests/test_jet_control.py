"""
jet_control lookup+commit+snoop test runner

The jet control core (MAS ch02_blocks/01): one request, one window classify
(tag read + MSHR CAM + WB match + set claims) into HIT / MERGE / MISS_ALLOC
/ STALL, hit-under-miss (J2), merge join (J3), the J6 stall story, the
commit pipeline (Task 6: fill_done triggers the D-4 store merge, tag
install, deferred snoop effect, per-tag deposits, retire -- all scored from
the taps), and the snoop path under concurrency (Task 7: the three answer
sources -- WB snarf / pending-fill bypass with PF_GUARD / array port B --
the bounded anti-livelock hold-off, and snoop priority over new CPU
accepts, driven through the l1_snoop_resp core-facing contract).  The
harness (dv/tb/jet_control_th.sv) wires the DUT to the REAL l1_tag_array /
l1_data_array / l1_repl / jet_mshr / jet_wb_buffer / jet_rsp_seq; the TB
models the fill/drain engines' handshake timing only.  Single geometry cell
(the J1 default: MSHR_COUNT=8, VICTIM_DEPTH=2, SETS=128, WAYS=4); the J7
sweeps are experiments, not unit-TB cells.

Author: RTL Design Sherpa
Created: 2026-10-28
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

from projects.components.cache_ip.jet_mesi_l1.dv.tbclasses.jet_control_tb import JetControlTB

JET_FL = 'projects/components/cache-ip/jet-mesi-l1/rtl/filelists'
COMMON_FL = 'projects/components/cache-ip/common-ip/rtl/filelists'
# test-side harness wrapper (pure wiring; lives with the test, not in an RTL
# filelist -- the same sanctioned pattern as other tb_*.sv harnesses)
HARNESS = 'projects/components/cache-ip/jet-mesi-l1/dv/tb/jet_control_th.sv'

# (sets, ways): single cell, the J1 default geometry.
GEOMS = [
    (128, 4),
]


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_jet_control(dut):
    tb = JetControlTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"jet_control: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("sets,ways", GEOMS)
def test_jet_control(request, sets, ways, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    dut_name = "jet_control_th"
    # Merge the closure filelists (control + the blocks it drives), dedup'ing
    # the shared package/reset includes order-preserving.
    verilog_sources = []
    includes = []
    for fl in ('jet_control', 'jet_mshr', 'jet_wb_buffer', 'jet_rsp_seq'):
        srcs, incs = get_sources_from_filelist(
            repo_root=repo_root, filelist_path=f'{JET_FL}/{fl}.f')
        for s in srcs:
            if s not in verilog_sources:
                verilog_sources.append(s)
        for i in incs:
            if i not in includes:
                includes.append(i)
    for fl in ('l1_tag_array', 'l1_data_array', 'l1_repl'):
        srcs, incs = get_sources_from_filelist(
            repo_root=repo_root, filelist_path=f'{COMMON_FL}/{fl}.f')
        for s in srcs:
            if s not in verilog_sources:
                verilog_sources.append(s)
        for i in incs:
            if i not in includes:
                includes.append(i)
    verilog_sources = verilog_sources + [os.path.join(repo_root, HARNESS)]

    test_name_plus_params = (f"test_{dut_name}"
                             f"_s{TBBase.format_dec(sets, 3)}w{ways}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)

    rtl_parameters = {'SETS': str(sets), 'WAYS': str(ways)}
    extra_env = level_env(test_level, SETS=sets, WAYS=ways,
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
            testcase="cocotb_test_jet_control",
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
