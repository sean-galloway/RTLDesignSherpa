"""
rs_encoder_axi4 / rs_decoder_axi4 test runner (full memory-to-memory loop)

The fixture (dv/tb/rs_axi4_loop_tb_top.sv) wires messages -> M1 -> encode ->
M2 -> decode -> M3 -> messages through three real sdpram memories, each with
one writer on its write channels and one reader on its read channels.

This test is what found PRD D9b. rs_encoder_core starts parity on a FRESH
beat, so at K % S != 0 its data phase ends on a partial beat MID-codeword, and
rs_decoder_core accepts a partial beat only on a block's LAST one -- it flags
every block mis-framed instead. The two had never been chained before, because
the standalone decoder test feeds it a codeword packed contiguously in Python.
rs_encoder_axi4 now generates rs_beat_packer in its output path when the core's
layout needs it, so a codeword reaches memory as ceil(N/S) packed beats and
every profile below chains.

Profiles are chosen for what they break:

  RS(252,236) S=4    the Nexys A7 loop's code. Nothing partial anywhere and no
                     packer built, so it is the transparency control.
  RS(255,239) S=4    k = 239 = 59 beats + 3. The packer IS built here, and
                     without it the decoder framed every block wrong.
  RS(15,9) t=3 S=4   BOTH phases end mid-beat: the core emits 5 beats and the
                     packer turns them into 4. A packer that only re-aligned
                     without re-counting would be caught here.
  RS(30,24) t=3 S=4  k fills its beats but 2t does not, so the partial is the
                     parity tail and it already lands last. No packer, but the
                     decoder's keep reconstruction is exercised.
  RS(204,188) S=4    DVB shortened, with Euclid, so the solver is not held
                     constant across the matrix.

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

from projects.components.ecc_ip.reed_solomon.dv.tbclasses.rs_axi4_loop_tb import RSAxi4LoopTB

FILELIST = 'projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_axi4_loop_tb.f'

# (symbol_width, prim_poly, t, n, symbols_per_beat, kes)
PROFILES = [
    (8, 0x11D, 8, 252, 4, "RIBM"),     # no partial beat at all; no packer
    (8, 0x11D, 8, 255, 4, "RIBM"),     # k ends mid-beat; the packer is built
    (8, 0x11D, 3, 15,  4, "EUCLID"),   # both phases mid-beat: 5 beats -> 4
    (8, 0x11D, 3, 30,  4, "EUCLID"),   # parity tail, already last; no packer
    (8, 0x11D, 8, 204, 4, "EUCLID"),   # DVB shortened, the other solver
]


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_rs_axi4_loop(dut):
    tb = RSAxi4LoopTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run_bursts()
    ok &= await tb.run_backpressure()
    ok &= await tb.run_erasures()
    ok &= await tb.run_valid_hold(burst_lens=(16, 64))
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, (f"rs_axi4 loop: {report['mismatches']} mismatches in "
                f"{report['checks']} checks ({report['beats']})")


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("erasure", [0, 1])   # TASK-002: an axis, not flipped cells
@pytest.mark.parametrize("symbol_width, prim_poly, t, n, spb, kes", PROFILES)
def test_rs_axi4_loop(request, symbol_width, prim_poly, t, n, spb, kes, erasure,
                      test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, _ = get_paths({
        'rtl_rs': 'projects/components/ecc-ip/reed-solomon/rtl',
    })
    dut_name = "rs_axi4_loop_tb_top"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root,
                                                          filelist_path=FILELIST)
    name = (f"test_rs_axi4_loop_m{TBBase.format_dec(symbol_width, 2)}"
            f"_n{TBBase.format_dec(n, 3)}_t{TBBase.format_dec(t, 2)}_s{spb}"
            f"_{kes.lower()}_e{erasure}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)

    rtl_parameters = {'SYMBOL_WIDTH': str(symbol_width), 'PRIM_POLY': str(prim_poly),
                      'T_SYMBOLS': str(t), 'N_SYMBOLS': str(n),
                      'DATA_WIDTH': str(symbol_width * spb),
                      'ADDR_WIDTH': '32', 'ID_WIDTH': '4', 'MEM_DEPTH': '2048',
                      'MAX_OUTSTANDING': '4', 'KES_ALGO': f'"{kes}"',
                      'ERASURE_SUPPORT': str(erasure)}
    extra_env = level_env(test_level, DUT=dut_name, LOG_PATH=log_path,
                          COCOTB_LOG_LEVEL='INFO',
                          SYMBOL_WIDTH=str(symbol_width), PRIM_POLY=hex(prim_poly),
                          T_SYMBOLS=str(t), N_SYMBOLS=str(n),
                          DATA_WIDTH=str(symbol_width * spb),
                          ERASURE_SUPPORT=str(erasure))

    compile_args = ["--trace-fst", "--trace-structs", "--trace-depth", "99"] if enable_waves else []
    sim_args = ["--trace-fst", "--trace-structs"] if enable_waves else []
    plusargs = ["+trace"] if enable_waves else []
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, name)
    print(f"\n{'='*60}\nRunning {name}\nLog: {log_path}\n{'='*60}")
    try:
        run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
            toplevel=dut_name, module=module, testcase="cocotb_test_rs_axi4_loop",
            parameters=rtl_parameters, sim_build=sim_build, extra_env=extra_env,
            waves=enable_waves, keep_files=True, compile_args=compile_args,
            sim_args=sim_args, plusargs=plusargs)
        print(f"PASS {name}")
    except Exception as e:
        print(f"FAIL {name}: {e}\nLog: {log_path}\nView: {cmd_filename}")
        raise
