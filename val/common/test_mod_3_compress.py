# SPDX-License-Identifier: MIT
# Exhaustive test for rtl/common/mod_3_compress.sv (d_in mod 3 over all 16-bit
# inputs), the compressor-style mod-3 used by the monbus burst writer.

import os
import pytest
import cocotb
from cocotb.triggers import Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_repo_root

repo_root = get_repo_root()


@cocotb.test()
async def mod_3_compress_test(dut):
    """Check rem_out == d_in % 3 across the 16-bit input space.

    TEST_LEVEL sets the stride: full is exhaustive (all 65536), func samples
    every 8th value and gate every 64th. The module is purely combinational,
    so a strided sweep still exercises every carry-save path -- what it gives
    up is exhaustiveness, which is exactly what the level knob is for.
    """
    _lvl = os.environ.get('TEST_LEVEL', 'gate').lower()
    if _lvl not in ('gate', 'func', 'full'):
        _lvl = 'gate'
    _stride = {'gate': 64, 'func': 8, 'full': 1}[_lvl]
    dut._log.info(f"mod_3_compress: TEST_LEVEL={_lvl}, stride={_stride}")
    for d in range(0, 1 << 16, _stride):
        dut.d_in.value = d
        await Timer(1, units="ns")
        got = int(dut.rem_out.value)
        exp = d % 3
        assert got == exp, f"d_in={d}: rem_out={got}, expected {exp}"


def _mod3_grid():
    """REG_LEVEL grid. The module has no parameters to sweep, so the grid is
    the set of depths that run -- the same shape hex_to_7seg uses."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return ['gate']
    if reg_level == 'FULL':
        return ['gate', 'func', 'full']
    return ['func']


@pytest.mark.parametrize("test_level", _mod3_grid())
def test_mod_3_compress(request, test_level):
    module, repo_root_l, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_common': 'rtl/common',
        'rtl_math': 'rtl/math',
    })
    dut_name = "mod_3_compress"
    verilog_sources = [
        os.path.join(rtl_dict['rtl_math'], "math_adder_carry_save_nbit.sv"),
        os.path.join(rtl_dict['rtl_common'], "mod_3_compress.sv"),
    ]
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        toplevel=dut_name,
        module=os.path.splitext(os.path.basename(__file__))[0],
        sim_build=os.path.join(log_dir, f"sim_build_{dut_name}_{test_level}"),
        extra_env={'TEST_LEVEL': test_level},
        timescale="1ns/1ps",
    )
