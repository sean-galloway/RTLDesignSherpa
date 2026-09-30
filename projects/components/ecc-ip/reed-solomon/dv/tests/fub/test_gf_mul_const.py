"""
gf_mul_const test runner

Constant multiplier in GF(2^m) against the reedsolo golden model, exhaustive
over the operand at every level (2^m checks). Constants cover alpha, the
polynomial's low byte, all-ones, and one arbitrary element per field.

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

from projects.components.ecc_ip.reed_solomon.dv.tbclasses.gf_tb import GFTB

FILELIST_DIR = 'projects/components/ecc-ip/reed-solomon/rtl/filelists'

# (symbol_width, prim_poly): the reference field, a small field that is
# exhaustive in a blink, and the 802.3 RS-FEC field.
FIELDS = [
    (8, 0x11D),
    (4, 0x13),
    (10, 0x409),
]

# (symbol_width, prim_poly, const)
CONSTS = [
    (8, 0x11D, 0x02),   # alpha: the multiply-by-x step
    (8, 0x11D, 0x1D),   # the reduction polynomial's low byte
    (8, 0x11D, 0xFF),   # all ones
    (8, 0x11D, 0x00),   # zero: the product is always zero
    (4, 0x13, 0x07),
    (10, 0x409, 0x123),
]


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_gf_mul_const(dut):
    tb = GFTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run_mul_const()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"gf_mul_const: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("symbol_width, prim_poly, const", CONSTS)
def test_gf_mul_const(request, symbol_width, prim_poly, const, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_gf': 'projects/components/ecc-ip/reed-solomon/rtl/gf',
    })
    dut_name = "gf_mul_const"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=f'{FILELIST_DIR}/gf_mul_const.f')

    test_name_plus_params = (f"test_{dut_name}_m{TBBase.format_dec(symbol_width, 2)}"
                             f"_c{const:03x}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {'SYMBOL_WIDTH': str(symbol_width), 'PRIM_POLY': str(prim_poly),
                      'CONST': str(const)}
    extra_env = level_env(test_level, SYMBOL_WIDTH=symbol_width, PRIM_POLY=hex(prim_poly),
                          CONST=const, DUT=dut_name, LOG_PATH=log_path, COCOTB_LOG_LEVEL='INFO')

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
            testcase="cocotb_test_gf_mul_const",
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
