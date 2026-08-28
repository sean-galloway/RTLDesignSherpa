# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axil5_opt_signals
# Purpose: AXI5-Lite optional signal groups, driven against real RTL
#
# Subsystem: tests

"""AXI5-Lite optional signal groups: USER, TRACE, LOOP, MPAM, MECID, NSAID,
POISON and exclusive access.

Runs the AXIL5 master BFMs with every optional group enabled against
``axil5_opt_slave``, a DUT built for this purpose whose ports actually carry
those signals. Before it existed the groups were declaration-only: the
framework unit tests compared field configs, and the other AXIL5 sim test
drives an AXI4-Lite DUT with every group switched OFF. Nothing put an optional
value on a wire and read it back, and two defects were hiding behind that --
the transaction methods had no way to SET an optional field (so a bound field
was driven as 0 forever), and EXOKAY was treated as an error (so exclusive
access could never succeed).

See ``bin/TBClasses/axil5/axil5_opt_slave_tb.py`` for what each group's check
proves.
"""

import os
import random

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.axil5.axil5_opt_slave_tb import (
    LOOP_WIDTH,
    MECID_WIDTH,
    MPAM_WIDTH,
    NSAID_WIDTH,
    USER_WIDTH,
    AXIL5OptSlaveTB,
)
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def axil5_opt_signals_test(dut):
    """Drive every AXI5-Lite optional group and verify echo, capture, poison."""
    tb = AXIL5OptSlaveTB(dut, aclk=dut.aclk, aresetn=dut.aresetn)

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)

    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
    counts = {'gate': 2, 'func': 4, 'full': 8}
    count = counts.get(test_level, 2)
    tb.log.info(f"AXIL5 optional-signal test, level={test_level}, "
                f"addresses={count}, seed={seed}")

    await tb.setup_clocks_and_reset()

    failures = await tb.run_all(count=count)
    assert not failures, (
        f"{len(failures)} AXI5-Lite optional-signal failure(s):\n  "
        + "\n  ".join(failures)
    )


def generate_axil5_opt_params():
    """Widths to sweep.

    Both legal AXI-Lite data widths (32 and 64) are covered, which exercises
    the address/data paths at each. Note what that does NOT prove: POISON is
    one bit per 64 data bits with a floor of one, so at 32 AND at 64 the width
    is 1. No legal AXI-Lite bus distinguishes the derivation from a hardcoded
    1 -- AXI-Lite does not allow 128-bit data. The derivation exists so the
    RTL and the field config apply the same rule, not because a Lite bus can
    ever show the difference; the multi-bit case belongs to full AXI5.
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [(32, 32, 'gate')]
    if reg_level == 'FUNC':
        return [(32, 32, 'gate'), (32, 64, 'func')]
    return [(32, 32, 'gate'), (32, 64, 'func'),
            (64, 32, 'func'), (64, 64, 'full')]


@pytest.mark.parametrize("addr_width, data_width, test_level",
                         generate_axil5_opt_params())
def test_axil5_opt_signals(request, addr_width, data_width, test_level):
    """AXI5-Lite optional signal groups against axil5_opt_slave."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axil5': 'rtl/amba/axil5/test-modules/',
        'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "axil5_opt_slave"

    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = (f"test_{worker_id}_{dut_name}_a{aw_str}_d{dw_str}"
                             f"_{test_level}_{reg_level}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axil5_opt_slave.f")
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # Widths MUST match the testbench constants: the BFM declares a field of
    # the width it is told and binds by name, so a mismatch truncates silently
    # rather than failing to bind.
    rtl_parameters = {
        'AXIL_ADDR_WIDTH': str(addr_width),
        'AXIL_DATA_WIDTH': str(data_width),
        'MEM_DEPTH':       str(256),
        'USER_WIDTH':      str(USER_WIDTH),
        'LOOP_WIDTH':      str(LOOP_WIDTH),
        'MPAM_WIDTH':      str(MPAM_WIDTH),
        'MECID_WIDTH':     str(MECID_WIDTH),
        'NSAID_WIDTH':     str(NSAID_WIDTH),
    }

    extra_env = {
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_LEVEL': test_level,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'DUT': dut_name,
    }

    compile_args = [
        "-Wall", "-Wno-DECLFILENAME", "-Wno-UNUSED",
        "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND",
        "-DUSE_ASYNC_RESET",
    ]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=os.path.splitext(os.path.basename(__file__))[0],
        testcase="axil5_opt_signals_test",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=False,
        keep_files=True,
        compile_args=compile_args,
    )
