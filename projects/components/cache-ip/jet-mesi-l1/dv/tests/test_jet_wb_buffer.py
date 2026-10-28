"""
jet_wb_buffer test runner

Decoupled writeback buffer: VICTIM_DEPTH-deep FIFO of dirty victims,
captured beat-serial and drained oldest-first.  Pin-level stimulus scored
against the TB's Python golden model (MAS ch02_blocks/03 contract), at the
J5 default geometry (VICTIM_DEPTH=2, LINE_BYTES=64, BUS_WIDTH=64).

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

from projects.components.cache_ip.jet_mesi_l1.dv.tbclasses.jet_wb_buffer_tb import JetWbBufferTB

FILELIST_DIR = 'projects/components/cache-ip/jet-mesi-l1/rtl/filelists'
HARNESS = 'projects/components/cache-ip/jet-mesi-l1/dv/tb/jet_wb_buffer_th.sv'

# Single geometry cell (J5 default).  The VICTIM_DEPTH {1,2,4} sweep is a
# later J7 experiment, not the unit grid.
GEOMS = [
    (2, 64, 64),
]


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_jet_wb_buffer(dut):
    tb = JetWbBufferTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"jet_wb_buffer: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("victim_depth,line_bytes,bus_width", GEOMS)
def test_jet_wb_buffer(request, victim_depth, line_bytes, bus_width, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    dut_name = "jet_wb_buffer_th"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=f'{FILELIST_DIR}/jet_wb_buffer.f')
    verilog_sources = verilog_sources + [os.path.join(repo_root, HARNESS)]

    test_name_plus_params = (f"test_{dut_name}_d{victim_depth}"
                             f"_lb{TBBase.format_dec(line_bytes, 3)}"
                             f"_bw{TBBase.format_dec(bus_width, 3)}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)

    rtl_parameters = {'VICTIM_DEPTH': str(victim_depth),
                      'LINE_BYTES': str(line_bytes),
                      'BUS_WIDTH': str(bus_width)}
    extra_env = level_env(test_level, VICTIM_DEPTH=victim_depth,
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
            testcase="cocotb_test_jet_wb_buffer",
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
