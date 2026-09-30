"""
rs_encoder / rs_decoder test runner (the AXI4-Stream integration tops)

The cores are verified through their bare valid/ready ports elsewhere. These
cells cover what the wrappers add: the tstrb-to-symbol-keep mapping, tlast
placement, the held tid/tdest across a block whose beat count changes, and the
two skid wrappers under backpressure.

Profiles are chosen so a PARTIAL final beat actually occurs. RS(255,239) at
4 symbols per beat gives k = 239 = 59 beats + 3, so the encoder's data phase
and the decoder's output both end on a 3-of-4 beat -- which is where a wrong
strobe mapping shows up. A profile whose k is a multiple of S would pass with
tstrb hardwired to all ones, so one is included deliberately as a control.

Author: RTL Design Sherpa
Created: 2026-09-30
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

from projects.components.ecc_ip.reed_solomon.dv.tbclasses.rs_axis_tb import RSAxisTB

# (symbol_width, prim_poly, t, n, symbols_per_beat)
PROFILES = [
    (8, 0x11D, 8, 255, 4),   # k = 239 = 59 beats + 3: a PARTIAL final beat
    (8, 0x11D, 8, 204, 4),   # DVB shortened, k = 188 = 47 beats exactly: control
    (8, 0x11D, 2, 32, 4),    # short codeword, k = 28 = 7 beats
]


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_rs_encoder_axis(dut):
    tb = RSAxisTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run_stream()
    ok &= await tb.run_backpressure()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"rs_encoder: {report['mismatches']} mismatches in {report['checks']} checks"


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_rs_decoder_axis(dut):
    tb = RSAxisTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run_stream()
    ok &= await tb.run_backpressure()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"rs_decoder: {report['mismatches']} mismatches in {report['checks']} checks"


def _run(dut_name, role, testcase, symbol_width, prim_poly, t, n, spb, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, _ = get_paths({
        'rtl_rs': 'projects/components/ecc-ip/reed-solomon/rtl',
    })
    filelist = f'projects/components/ecc-ip/reed-solomon/rtl/filelists/{dut_name}.f'
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root,
                                                          filelist_path=filelist)
    idw, destw = 4, 2
    name = (f"test_{dut_name}_m{TBBase.format_dec(symbol_width, 2)}"
            f"_n{TBBase.format_dec(n, 3)}_t{TBBase.format_dec(t, 2)}_s{spb}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)

    rtl_parameters = {'SYMBOL_WIDTH': str(symbol_width), 'PRIM_POLY': str(prim_poly),
                      'T_SYMBOLS': str(t), 'N_SYMBOLS': str(n),
                      'DATA_WIDTH': str(symbol_width * spb),
                      'AXIS_ID_WIDTH': str(idw), 'AXIS_DEST_WIDTH': str(destw),
                      'AXIS_USER_WIDTH': '1'}
    extra_env = level_env(test_level, DUT=dut_name, LOG_PATH=log_path,
                          COCOTB_LOG_LEVEL='INFO', RS_AXIS_ROLE=role,
                          SYMBOL_WIDTH=str(symbol_width), PRIM_POLY=hex(prim_poly),
                          T_SYMBOLS=str(t), N_SYMBOLS=str(n),
                          DATA_WIDTH=str(symbol_width * spb),
                          AXIS_ID_WIDTH=str(idw), AXIS_DEST_WIDTH=str(destw))

    compile_args = ["--trace-fst", "--trace-structs", "--trace-depth", "99"] if enable_waves else []
    sim_args = ["--trace-fst", "--trace-structs"] if enable_waves else []
    plusargs = ["+trace"] if enable_waves else []
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, name)
    print(f"\n{'='*60}\nRunning {name}\nLog: {log_path}\n{'='*60}")
    try:
        run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
            toplevel=dut_name, module=module, testcase=testcase,
            parameters=rtl_parameters, sim_build=sim_build, extra_env=extra_env,
            waves=enable_waves, keep_files=True, compile_args=compile_args,
            sim_args=sim_args, plusargs=plusargs)
        print(f"PASS {name}")
    except Exception as e:
        print(f"FAIL {name}: {e}\nLog: {log_path}\nView: {cmd_filename}")
        raise


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("symbol_width, prim_poly, t, n, spb", PROFILES)
def test_rs_encoder(request, symbol_width, prim_poly, t, n, spb, test_level):
    _run("rs_encoder", "encoder", "cocotb_test_rs_encoder_axis",
         symbol_width, prim_poly, t, n, spb, test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("symbol_width, prim_poly, t, n, spb", PROFILES)
def test_rs_decoder(request, symbol_width, prim_poly, t, n, spb, test_level):
    _run("rs_decoder", "decoder", "cocotb_test_rs_decoder_axis",
         symbol_width, prim_poly, t, n, spb, test_level)
