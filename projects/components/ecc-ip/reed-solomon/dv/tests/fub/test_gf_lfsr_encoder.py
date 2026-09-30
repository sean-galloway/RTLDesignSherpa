"""
gf_lfsr_encoder test runner

The systematic encoder's LFSR driven directly: k steps in, 2t shifts out,
parity compared with reedsolo and the register checked clear after the drain.

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

from projects.components.ecc_ip.reed_solomon.dv.tbclasses.gf_tb import GFLFSRTB

FILELIST = 'projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_lfsr_encoder.f'

# (symbol_width, prim_poly, t, first_root, k)
CONFIGS = [
    (8, 0x11D, 8, 0, 239),
    (8, 0x11D, 1, 0, 19),
    (8, 0x187, 16, 112, 223),   # CCSDS field and first root (dual basis NOT applied here)
    (4, 0x13, 2, 0, 11),
    (10, 0x409, 15, 0, 514),
]


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_gf_lfsr_encoder(dut):
    tb = GFLFSRTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run_blocks()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"gf_lfsr_encoder: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("symbol_width, prim_poly, t, first_root, k", CONFIGS)
def test_gf_lfsr_encoder(request, symbol_width, prim_poly, t, first_root, k, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_gf': 'projects/components/ecc-ip/reed-solomon/rtl/gf',
    })
    dut_name = "gf_lfsr_encoder"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=FILELIST)

    test_name_plus_params = (f"test_{dut_name}_m{TBBase.format_dec(symbol_width, 2)}"
                             f"_t{TBBase.format_dec(t, 2)}_b{TBBase.format_dec(first_root, 3)}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {'SYMBOL_WIDTH': str(symbol_width), 'PRIM_POLY': str(prim_poly),
                      'T_SYMBOLS': str(t), 'FIRST_ROOT': str(first_root)}
    extra_env = level_env(test_level, K_SYMBOLS=k, DUT=dut_name, LOG_PATH=log_path,
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
            testcase="cocotb_test_gf_lfsr_encoder",
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
