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
    """Check rem_out == d_in % 3 for every 16-bit d_in."""
    for d in range(1 << 16):
        dut.d_in.value = d
        await Timer(1, units="ns")
        got = int(dut.rem_out.value)
        exp = d % 3
        assert got == exp, f"d_in={d}: rem_out={got}, expected {exp}"


def test_mod_3_compress(request):
    module, repo_root_l, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_common': 'rtl/common',
    })
    dut_name = "mod_3_compress"
    verilog_sources = [
        os.path.join(rtl_dict['rtl_common'], "math_adder_carry_save_nbit.sv"),
        os.path.join(rtl_dict['rtl_common'], "mod_3_compress.sv"),
    ]
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        toplevel=dut_name,
        module=os.path.splitext(os.path.basename(__file__))[0],
        sim_build=os.path.join(log_dir, f"sim_build_{dut_name}"),
        timescale="1ns/1ps",
    )
