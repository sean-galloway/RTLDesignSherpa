"""
bch_axi4_read_engine / bch_axi4_write_engine test runner

The fixture (dv/tb/bch_axi4_engines_tb_top.sv) is one real sdpram memory with
the write engine on its write channels and the read engine on its read
channels, so a pattern written and read back exercises both engines and the
memory together. No AXI4 BFM is involved: the real memory is the far end, and
the only BFMs are GAXI on the two valid/ready stream ports.

Author: RTL Design Sherpa
Created: 2026-10-03
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

from projects.components.ecc_ip.bch.dv.tbclasses.bch_axi4_engines_tb import BCHAxi4EnginesTB

FILELIST = 'projects/components/ecc-ip/bch/rtl/filelists/bch_axi4_engines_tb.f'

# (data_width, id_width, mem_depth)
PROFILES = [
    (32, 4, 2048),    # the board-profile width
    (64, 4, 1024),    # a wider bus
]


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_bch_axi4_engines(dut):
    tb = BCHAxi4EnginesTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run_bursts()
    ok &= await tb.run_blocks()
    ok &= await tb.run_backpressure()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, (f"bch_axi4 engines: {report['mismatches']} mismatches in "
                f"{report['checks']} checks")


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("data_width, id_width, mem_depth", PROFILES)
def test_bch_axi4_engines(request, data_width, id_width, mem_depth, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, _ = get_paths({
        'rtl_bch': 'projects/components/ecc-ip/bch/rtl',
    })
    dut_name = "bch_axi4_engines_tb_top"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root,
                                                          filelist_path=FILELIST)
    name = (f"test_bch_axi4_engines_d{TBBase.format_dec(data_width, 3)}"
            f"_m{TBBase.format_dec(mem_depth, 4)}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)

    rtl_parameters = {'DATA_WIDTH': str(data_width), 'ID_WIDTH': str(id_width),
                      'MEM_DEPTH': str(mem_depth), 'ADDR_WIDTH': '32',
                      'MAX_OUTSTANDING': '4'}
    extra_env = level_env(test_level, DUT=dut_name, LOG_PATH=log_path,
                          COCOTB_LOG_LEVEL='INFO', DATA_WIDTH=str(data_width))

    compile_args = ["--trace-fst", "--trace-structs", "--trace-depth", "99"] if enable_waves else []
    sim_args = ["--trace-fst", "--trace-structs"] if enable_waves else []
    plusargs = ["+trace"] if enable_waves else []
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, name)
    print(f"\n{'='*60}\nRunning {name}\nLog: {log_path}\n{'='*60}")
    try:
        run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
            toplevel=dut_name, module=module, testcase="cocotb_test_bch_axi4_engines",
            parameters=rtl_parameters, sim_build=sim_build, extra_env=extra_env,
            waves=enable_waves, keep_files=True, compile_args=compile_args,
            sim_args=sim_args, plusargs=plusargs)
        print(f"PASS {name}")
    except Exception as e:
        print(f"FAIL {name}: {e}\nLog: {log_path}\nView: {cmd_filename}")
        raise
