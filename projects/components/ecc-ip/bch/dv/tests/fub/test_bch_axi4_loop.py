"""
bch_encoder_axi4 / bch_decoder_axi4 test runner (full memory-to-memory loop)

The fixture (dv/tb/bch_axi4_loop_tb_top.sv) wires messages -> M1 -> encode ->
M2 -> decode -> M3 -> messages through three real sdpram memories.

Profiles are chosen for coverage:

  BCH(4224,4120) t=8 B=32   the flash-class board profile; CW_BEATS=132 (no
                            tail), K_BEATS=129 with K_TAIL=24, so the encoder
                            beat-packer is exercised.
  BCH(63,51) t=2 B=8        a narrow-sense primitive code; both K_TAIL and
                            N_TAIL non-zero, exercising decoder keep rebuild.

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

from projects.components.ecc_ip.bch.dv.tbclasses.bch_axi4_loop_tb import BCHAxi4LoopTB

FILELIST = 'projects/components/ecc-ip/bch/rtl/filelists/bch_axi4_loop_tb.f'

# (field_dim, prim_poly, t_bits, n_bits, first_root, bits_per_beat)
PROFILES = [
    (13, 0x201B, 8, 4224, 1, 32),   # flash-class board profile
    (6, 0x43, 2, 63, 1, 8),          # narrow-sense primitive BCH(63,51)
]


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bch_axi4_loop(dut):
    tb = BCHAxi4LoopTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run_bursts()
    ok &= await tb.run_backpressure()
    ok &= await tb.run_valid_hold(burst_lens=(16, 64))
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, (f"bch_axi4 loop: {report['mismatches']} mismatches in "
                f"{report['checks']} checks ({report['beats']})")


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("field_dim, prim_poly, t_bits, n_bits, first_root, bits_per_beat", PROFILES)
def test_bch_axi4_loop(request, field_dim, prim_poly, t_bits, n_bits, first_root,
                       bits_per_beat, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, _ = get_paths({
        'rtl_bch': 'projects/components/ecc-ip/bch/rtl',
    })
    dut_name = "bch_axi4_loop_tb_top"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root,
                                                          filelist_path=FILELIST)
    name = (f"test_bch_axi4_loop_m{TBBase.format_dec(field_dim, 2)}"
            f"_n{TBBase.format_dec(n_bits, 4)}"
            f"_t{TBBase.format_dec(t_bits, 2)}"
            f"_b{TBBase.format_dec(first_root, 2)}"
            f"_s{TBBase.format_dec(bits_per_beat, 2)}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)

    rtl_parameters = {
        'FIELD_DIM': str(field_dim),
        'PRIM_POLY': str(prim_poly),
        'T_BITS': str(t_bits),
        'N_BITS': str(n_bits),
        'FIRST_ROOT': str(first_root),
        'DATA_WIDTH': str(bits_per_beat),
        'ADDR_WIDTH': '32',
        'ID_WIDTH': '4',
        'MEM_DEPTH': '2048',
        'MAX_OUTSTANDING': '4',
    }
    extra_env = level_env(test_level, DUT=dut_name, LOG_PATH=log_path,
                          COCOTB_LOG_LEVEL='INFO',
                          FIELD_DIM=str(field_dim), PRIM_POLY=hex(prim_poly),
                          T_BITS=str(t_bits), N_BITS=str(n_bits),
                          FIRST_ROOT=str(first_root),
                          DATA_WIDTH=str(bits_per_beat))

    compile_args = ["--trace-fst", "--trace-structs", "--trace-depth", "99"] if enable_waves else []
    sim_args = ["--trace-fst", "--trace-structs"] if enable_waves else []
    plusargs = ["+trace"] if enable_waves else []
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, name)
    print(f"\n{'='*60}\nRunning {name}\nLog: {log_path}\n{'='*60}")
    try:
        run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
            toplevel=dut_name, module=module, testcase="cocotb_test_bch_axi4_loop",
            parameters=rtl_parameters, sim_build=sim_build, extra_env=extra_env,
            waves=enable_waves, keep_files=True, compile_args=compile_args,
            sim_args=sim_args, plusargs=plusargs)
        print(f"PASS {name}")
    except Exception as e:
        print(f"FAIL {name}: {e}\nLog: {log_path}\nView: {cmd_filename}")
        raise
