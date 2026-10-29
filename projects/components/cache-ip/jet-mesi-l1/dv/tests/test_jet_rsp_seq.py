"""
jet_rsp_seq test runner

Response sequencer: CAM-free ring of per-tag completion records that keeps
GAXI responses in request-accept order while fills/merges complete out of
order (MAS ch02_blocks/04 contract).  Pin-level stimulus scored against the
TB's Python golden model at the J4 default geometry (RSP_DEPTH=10,
BUS_WIDTH=64).

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

from projects.components.cache_ip.jet_mesi_l1.dv.tbclasses.jet_rsp_seq_tb import JetRspSeqTB

FILELIST_DIR = 'projects/components/cache-ip/jet-mesi-l1/rtl/filelists'
HARNESS = 'projects/components/cache-ip/jet-mesi-l1/dv/tb/jet_rsp_seq_th.sv'

# Single geometry cell (J4 default).  The {2,4,8,16} RSP_DEPTH sweep is a
# later J7 experiment, not the unit grid.
GEOMS = [
    (10, 64),
]


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_jet_rsp_seq(dut):
    tb = JetRspSeqTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"jet_rsp_seq: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("rsp_depth,bus_width", GEOMS)
def test_jet_rsp_seq(request, rsp_depth, bus_width, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    dut_name = "jet_rsp_seq_th"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=f'{FILELIST_DIR}/jet_rsp_seq.f')
    verilog_sources = verilog_sources + [os.path.join(repo_root, HARNESS)]

    test_name_plus_params = (f"test_{dut_name}_d{rsp_depth}"
                             f"_bw{TBBase.format_dec(bus_width, 3)}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)

    rtl_parameters = {'RSP_DEPTH': str(rsp_depth),
                      'BUS_WIDTH': str(bus_width)}
    extra_env = level_env(test_level, RSP_DEPTH=rsp_depth,
                          BUS_WIDTH=bus_width,
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
            testcase="cocotb_test_jet_rsp_seq",
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
