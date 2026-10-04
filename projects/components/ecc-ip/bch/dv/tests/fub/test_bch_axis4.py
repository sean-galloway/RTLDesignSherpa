"""
bch_encoder_axis4 / bch_decoder_axis4 test runner

The cores are verified through their bare valid/ready ports elsewhere. These
cells cover what the wrappers add: the keep-to-tstrb/tuser mapping, tlast
placement, the held tid/tdest across a block, the two skid wrappers under
backpressure, and the decoder verdict realigned to m_axis_tlast.

Profiles include the three standing BCH configurations plus the wide-beat
board profile (B=32) so both tstrb and tuser keep modes are exercised.

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

from projects.components.ecc_ip.bch.dv.tbclasses.bch_axis_tb import BCHAxisTB

# (field_dim, prim_poly, t_bits, n_bits, first_root, bits_per_beat)
CONFIGS = [
    (6, 0x43, 1, 63, 0, 8),       # CCSDS (63,56) modified BCH: tuser mode
    (13, 0x201B, 8, 4224, 1, 8),  # flash-class BCH(4224,4120): tstrb mode
    (6, 0x43, 2, 63, 1, 8),       # narrow-sense BCH(63,51): tuser mode
    (13, 0x201B, 8, 4224, 1, 32), # board profile, tstrb mode
]


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bch_encoder_axis4(dut):
    tb = BCHAxisTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run_stream()
    ok &= await tb.run_backpressure()
    ok &= await tb.run_no_dead_cycles()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"bch_encoder_axis4: {report['mismatches']} mismatches in {report['checks']} checks"


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bch_decoder_axis4(dut):
    tb = BCHAxisTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run_stream()
    ok &= await tb.run_backpressure()
    # The BCH decoder core is single-outstanding, so the RS-style no-dead-cycles
    # slope test (which assumes line-rate back-to-back blocks) does not apply.
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"bch_decoder_axis4: {report['mismatches']} mismatches in {report['checks']} checks"


def _run(dut_name, role, testcase, field_dim, prim_poly, t_bits, n_bits, first_root,
         bits_per_beat, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, _ = get_paths({
        'rtl_bch': 'projects/components/ecc-ip/bch/rtl',
    })
    filelist = f'projects/components/ecc-ip/bch/rtl/filelists/{dut_name}.f'
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root,
                                                          filelist_path=filelist)
    # K is derived by the RTL from the polynomial; the wrapper needs it for the
    # name and expected-beat counts, so compute it the same way here.
    from projects.components.ecc_ip.bch.dv.tbclasses.bch_model import BCHModel
    k_bits = BCHModel(field_dim, prim_poly, t_bits, n_bits, first_root).k()

    byte_aligned = (k_bits % 8 == 0) and (n_bits % 8 == 0)
    axis_user_width = 1 if byte_aligned else bits_per_beat
    idw, destw = 4, 2

    name = (f"test_{dut_name}_m{TBBase.format_dec(field_dim, 2)}"
            f"_n{TBBase.format_dec(n_bits, 4)}"
            f"_t{TBBase.format_dec(t_bits, 2)}"
            f"_b{TBBase.format_dec(first_root, 2)}"
            f"_s{TBBase.format_dec(bits_per_beat, 2)}"
            f"_{test_level}")
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)

    rtl_parameters = {
        'FIELD_DIM': str(field_dim),
        'PRIM_POLY': str(prim_poly),
        'T_BITS': str(t_bits),
        'N_BITS': str(n_bits),
        'FIRST_ROOT': str(first_root),
        'BITS_PER_BEAT': str(bits_per_beat),
        'AXIS_ID_WIDTH': str(idw),
        'AXIS_DEST_WIDTH': str(destw),
        'AXIS_USER_WIDTH': str(axis_user_width),
    }
    extra_env = level_env(test_level, DUT=dut_name, LOG_PATH=log_path,
                          COCOTB_LOG_LEVEL='INFO', BCH_AXIS_ROLE=role,
                          FIELD_DIM=str(field_dim), PRIM_POLY=hex(prim_poly),
                          T_BITS=str(t_bits), N_BITS=str(n_bits),
                          FIRST_ROOT=str(first_root),
                          BITS_PER_BEAT=str(bits_per_beat),
                          AXIS_ID_WIDTH=str(idw), AXIS_DEST_WIDTH=str(destw),
                          AXIS_USER_WIDTH=str(axis_user_width))

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
@pytest.mark.parametrize("field_dim, prim_poly, t_bits, n_bits, first_root, bits_per_beat", CONFIGS)
def test_bch_encoder_axis4(request, field_dim, prim_poly, t_bits, n_bits, first_root,
                           bits_per_beat, test_level):
    _run("bch_encoder_axis4", "encoder", "cocotb_test_bch_encoder_axis4",
         field_dim, prim_poly, t_bits, n_bits, first_root, bits_per_beat, test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("field_dim, prim_poly, t_bits, n_bits, first_root, bits_per_beat", CONFIGS)
def test_bch_decoder_axis4(request, field_dim, prim_poly, t_bits, n_bits, first_root,
                           bits_per_beat, test_level):
    _run("bch_decoder_axis4", "decoder", "cocotb_test_bch_decoder_axis4",
         field_dim, prim_poly, t_bits, n_bits, first_root, bits_per_beat, test_level)
