"""
rs_beat_packer test runner

Profiles are the ones the packer exists for. The encoder's layout and the
decoder's contract only disagree when k does not fill a beat, so the matrix
leads with those and keeps an aligned profile as the control.

  RS(255,239) S=4   k = 239 = 59 beats + 3: a partial beat MID-codeword, and
                    the encoder's 64 beats pack to 64. The common shortened
                    case.
  RS(15,9) t=3 S=4  BOTH phases end mid-beat: 5 encoder beats pack to 4. A
                    packer that only re-aligned without re-counting would be
                    caught here and nowhere else.
  RS(7,5) t=1 S=4   3 encoder beats pack to 2, with a block shorter than the
                    accumulator is deep -- the degenerate case for the flush.
  RS(252,236) S=4   nothing partial anywhere. The control: a pass here proves
                    the packer is transparent when there is nothing to do.

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

from projects.components.ecc_ip.reed_solomon.dv.tbclasses.rs_beat_packer_tb import RSBeatPackerTB

FILELIST = 'projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_beat_packer.f'

# (symbol_width, t, n, symbols_per_beat)
PROFILES = [
    (8, 8, 255, 4),   # k ends mid-beat
    (8, 3, 15,  4),   # BOTH phases end mid-beat: 5 beats -> 4
    (8, 1, 7,   4),   # tiny block: 3 beats -> 2
    (8, 8, 252, 4),   # nothing partial: the transparency control
]


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_rs_beat_packer(dut):
    tb = RSBeatPackerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_blocks()
    ok = await tb.run_backpressure()
    ok &= (tb.mismatches == 0)
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, (f"rs_beat_packer: {report['mismatches']} mismatches in "
                f"{report['checks']} checks ({report['layout']})")


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("symbol_width, t, n, spb", PROFILES)
def test_rs_beat_packer(request, symbol_width, t, n, spb, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, _ = get_paths({
        'rtl_rs': 'projects/components/ecc-ip/reed-solomon/rtl',
    })
    dut_name = "rs_beat_packer"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root,
                                                          filelist_path=FILELIST)
    k = n - 2 * t
    name = (f"test_rs_beat_packer_m{TBBase.format_dec(symbol_width, 2)}"
            f"_n{TBBase.format_dec(n, 3)}_t{TBBase.format_dec(t, 2)}_s{spb}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)

    rtl_parameters = {'SYMBOL_WIDTH': str(symbol_width), 'SYMBOLS_PER_BEAT': str(spb)}
    extra_env = level_env(test_level, DUT=dut_name, LOG_PATH=log_path,
                          COCOTB_LOG_LEVEL='INFO',
                          SYMBOL_WIDTH=str(symbol_width), SYMBOLS_PER_BEAT=str(spb),
                          K_SYMBOLS=str(k), T_SYMBOLS=str(t))

    compile_args = ["--trace-fst", "--trace-structs", "--trace-depth", "99"] if enable_waves else []
    sim_args = ["--trace-fst", "--trace-structs"] if enable_waves else []
    plusargs = ["+trace"] if enable_waves else []
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, name)
    print(f"\n{'='*60}\nRunning {name}\nLog: {log_path}\n{'='*60}")
    try:
        run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
            toplevel=dut_name, module=module, testcase="cocotb_test_rs_beat_packer",
            parameters=rtl_parameters, sim_build=sim_build, extra_env=extra_env,
            waves=enable_waves, keep_files=True, compile_args=compile_args,
            sim_args=sim_args, plusargs=plusargs)
        print(f"PASS {name}")
    except Exception as e:
        print(f"FAIL {name}: {e}\nLog: {log_path}\nView: {cmd_filename}")
        raise
