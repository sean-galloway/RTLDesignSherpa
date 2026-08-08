# SPDX-License-Identifier: MIT
# Exhaustive test for rtl/common/mod_3_compress.sv (d_in mod 3 over all 16-bit
# inputs), the compressor-style mod-3 used by the monbus burst writer.

import os
import pytest
import cocotb
from cocotb.triggers import Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_repo_root
from cov_utils.conftest_coverage import get_coverage_compile_args
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.common.mod_3_compress_tb import Mod3CompressTB

repo_root = get_repo_root()


@cocotb.test()
async def mod_3_compress_test(dut):
    """Check rem_out == d_in % 3 across the 16-bit input space."""
    tb = Mod3CompressTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.sweep()


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
    # Sources come from the filelist, never a hand-listed array: the array
    # here omitted the include dirs and reset_defs.svh the filelist carries,
    # and a dependency added to the module is invisible to it ([[filelists]]).
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/mod_3_compress.f')
    # This wrapper passed no compile args at all, so it could never collect
    # coverage even once COVERAGE=1 was honoured elsewhere.
    extra_args = get_coverage_compile_args()

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        extra_args=extra_args,
        includes=includes,
        toplevel=dut_name,
        module=os.path.splitext(os.path.basename(__file__))[0],
        # local_sim_build, like every other wrapper in this area. Under logs/
        # the build escaped both `make clean-all` AND the coverage merge glob
        # (**/local_sim_build/**/coverage.dat), so this module reported no
        # coverage at all while its stale .dat files accumulated.
        sim_build=os.path.join(tests_dir, "local_sim_build",
                               f"{dut_name}_{test_level}"),
        extra_env={'TEST_LEVEL': test_level},
        timescale="1ns/1ps",
    )
