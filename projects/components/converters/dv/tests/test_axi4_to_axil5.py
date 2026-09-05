# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_axi4_to_axil5
# Purpose: Test runner for the AXI4 -> AXI5-Lite converter sideband contract
#
# Author: sean galloway
# Created: 2026-09-05

"""AXI4 -> AXI5-Lite converter: the sideband contract.

Burst decomposition, address incrementing and response folding belong to
``axi4_to_axil4_{rd,wr}``, which this converter wraps unchanged; they are
covered by ``test_axi4_to_axil4_rd.py`` and ``test_axi4_to_axil4_wr.py``.
This suite covers the only behaviour the AXI5-Lite wrapper adds -- where each
sideband signal gets its value -- and is deliberately narrow for that reason.

Levels:
  gate  single-beat write and read: forwarded values arrive, tied signals are 0
  func  + a multi-beat burst: every decomposed beat carries the burst's USER
  full  + two overlapping bursts with different USER, which is the only shape
        that can catch a combinationally-passed AW sideband, and + the
        ENABLE_USER/ENABLE_LOCK=0 build, where the same traffic must produce
        zeros on the AXI5-Lite side.
"""

import os
import random
import sys

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_repo_root, get_paths, create_view_cmd, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.converters.dv.tbclasses.axi4_to_axil5_tb import (
    AXI4ToAXIL5TB,
    BUSER_CONST,
    RUSER_CONST,
)
from TBClasses.shared.filelist_utils import get_sources_from_filelist


BASE = 0x0000_1000


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_axil5_sideband(dut):
    """Audit every AXI5-Lite sideband signal the wrapper is responsible for."""
    tb = AXI4ToAXIL5TB(dut)

    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)

    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
    if test_level not in ('gate', 'func', 'full'):
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'gate'")
        test_level = 'gate'
    tb.log.info(f"Running {test_level.upper()} AXI5-Lite sideband suite (seed={seed})")

    await tb.setup_clocks_and_reset()
    cocotb.start_soon(tb.sideband_monitor())

    bytes_per_beat = tb.data_width // 8

    # ---- single beat: the forwarded values arrive, the tied ones are 0 ----
    mark = len(tb.aw_beats)
    await tb.axi4_wr.write_transaction(BASE, 0xA5A5_1111, burst_len=1,
                                       user=0x3, lock=1)
    await tb.wait_clocks(tb.clk_name, 10)
    tb.check_beats(tb.aw_beats[mark:], "single write", axi_user=0x3,
                   axi_lock=1, count=1)

    mark = len(tb.ar_beats)
    await tb.axi4_rd.read_transaction(BASE, burst_len=1, user=0x2, lock=1)
    await tb.wait_clocks(tb.clk_name, 10)
    tb.check_beats(tb.ar_beats[mark:], "single read", axi_user=0x2,
                   axi_lock=1, count=1)

    # ---- the response sideband comes back onto the AXI4 channels ----------
    tb.check_response_user(tb.b_user, "B", BUSER_CONST)
    tb.check_response_user(tb.r_user, "R", RUSER_CONST)

    if test_level in ('func', 'full'):
        # ---- a burst: every decomposed beat carries the burst's USER -----
        mark = len(tb.aw_beats)
        await tb.axi4_wr.write_transaction(
            BASE + 0x100, [0x1000 + i for i in range(4)], burst_len=4,
            user=0x7, lock=0)
        await tb.wait_clocks(tb.clk_name, 20)
        tb.check_beats(tb.aw_beats[mark:], "burst write", axi_user=0x7,
                       axi_lock=0, count=4)

        mark = len(tb.ar_beats)
        await tb.axi4_rd.read_transaction(BASE + 0x200, burst_len=4,
                                          user=0x5, lock=0)
        await tb.wait_clocks(tb.clk_name, 20)
        tb.check_beats(tb.ar_beats[mark:], "burst read", axi_user=0x5,
                       axi_lock=0, count=4)

    if test_level == 'full':
        # ---- overlapping bursts: the regression that motivated the hold ---
        #
        # The second write's AW sits on the AXI4 bus, with ITS user value,
        # while the first write is still emitting beats 2..8. A wrapper that
        # passes the AW sideband through combinationally stamps those later
        # beats with 0xC instead of 0x3, and only this shape shows it.
        mark = len(tb.aw_beats)
        first = cocotb.start_soon(tb.axi4_wr.write_transaction(
            BASE + 0x400, [0x2000 + i for i in range(8)], burst_len=8,
            user=0x3, lock=0))
        second = cocotb.start_soon(tb.axi4_wr.write_transaction(
            BASE + 0x800, [0x3000 + i for i in range(4)], burst_len=4,
            user=0xC, lock=1))
        await first
        await second
        await tb.wait_clocks(tb.clk_name, 30)

        overlapped = tb.aw_beats[mark:]
        if len(overlapped) != 12:
            tb._fail(f"overlapped writes: expected 12 AW beats, saw {len(overlapped)}")
        else:
            tb.check_beats(overlapped[:8], "overlapped write A", axi_user=0x3,
                           axi_lock=0, count=8)
            tb.check_beats(overlapped[8:], "overlapped write B", axi_user=0xC,
                           axi_lock=1, count=4)

        # ---- W beats track the AXI4 W channel 1:1, no hold involved -------
        expected_w = 1 + 4 + 8 + 4
        if len(tb.w_beats) != expected_w:
            tb._fail(f"expected {expected_w} W beats, saw {len(tb.w_beats)}")

    tb.log.info("=" * 72)
    tb.log.info(f"{test_level.upper()}: {len(tb.aw_beats)} AW / "
                f"{len(tb.ar_beats)} AR / {len(tb.w_beats)} W beats audited, "
                f"{len(tb.errors)} error(s)")
    tb.log.info("=" * 72)

    assert not tb.errors, (
        f"{len(tb.errors)} sideband violation(s):\n  " + "\n  ".join(tb.errors[:20]))


def generate_test_params():
    """Configurations to sweep, filtered by REG_LEVEL.

    The ``enable=0`` rows are not redundant with the ``enable=1`` rows: they
    are the only check that ``ENABLE_USER``/``ENABLE_LOCK`` actually gate,
    rather than the signal happening to read 0 because nothing drove it.
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    all_params = [
        {'data_width': 32, 'user_width': 4, 'enable': 1, 'test_level': 'gate'},
        {'data_width': 64, 'user_width': 4, 'enable': 1, 'test_level': 'gate'},

        {'data_width': 32, 'user_width': 4, 'enable': 1, 'test_level': 'func'},
        {'data_width': 64, 'user_width': 8, 'enable': 1, 'test_level': 'func'},

        {'data_width': 32, 'user_width': 4, 'enable': 1, 'test_level': 'full'},
        {'data_width': 64, 'user_width': 8, 'enable': 1, 'test_level': 'full'},
        {'data_width': 128, 'user_width': 4, 'enable': 1, 'test_level': 'full'},
        # Gating build: same traffic, everything must read 0 downstream.
        {'data_width': 32, 'user_width': 4, 'enable': 0, 'test_level': 'full'},
    ]

    if reg_level == 'GATE':
        return [p for p in all_params if p['test_level'] == 'gate']
    if reg_level == 'FUNC':
        return [p for p in all_params if p['test_level'] in ('gate', 'func')]
    return all_params


@pytest.mark.parametrize("params", generate_test_params())
def test_axi4_to_axil5(request, params):
    """AXI4 -> AXI5-Lite converter: sideband forwarding, tie-off and gating."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/converters/rtl',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "axi4_to_axil5"
    toplevel = dut_name

    data_width = params['data_width']
    user_width = params['user_width']
    enable = params['enable']
    test_level = params['test_level']
    addr_width = 32
    id_width = 8

    test_name_plus_params = (f"test_axi4_to_axil5_dw{data_width}_"
                             f"uw{user_width}_en{enable}_{test_level}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/converters/rtl/filelists/axi4_to_axil5.f'
    )

    # ENABLE_LOCK and ENABLE_USER are the only gates the converter has --
    # the other groups are tied unconditionally, so there is nothing to
    # enable. The `enable=0` row sweeps exactly the two that do something.
    rtl_parameters = {
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': str(user_width),
        'ENABLE_LOCK': str(enable),
        'ENABLE_USER': str(enable),
        'USER_WIDTH': str(user_width),
        'LOOP_WIDTH': '3',
        'MPAM_WIDTH': '11',
        'MECID_WIDTH': '16',
        'NSAID_WIDTH': '4',
    }

    timeout_ms = {'gate': 10000, 'func': 30000, 'full': 90000}[test_level]

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),
        'SEED': os.environ.get('SEED', str(random.randint(0, 1000000))),
        'TEST_LEVEL': test_level,
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_ID_WIDTH': str(id_width),
        'AXI_USER_WIDTH': str(user_width),
        'USER_WIDTH': str(user_width),
        'LOOP_WIDTH': '3',
        'ENABLE_USER': str(enable),
        'ENABLE_LOCK': str(enable),
    }

    compile_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
    sim_args = ["--trace", "--trace-structs", "--trace-depth", "99"]

    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module,
                                   test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"AXI4->AXI5-Lite sideband: {test_level.upper()}")
    print(f"DW={data_width} USER_WIDTH={user_width} ENABLE_USER/LOCK={enable}")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir, repo_root],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            testcase="cocotb_test_axil5_sideband",
            parameters=rtl_parameters,
            simulator='verilator',
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=['--trace'] if enable_waves else [],
        )
        print(f"PASSED {test_level.upper()} (DW={data_width}, enable={enable})")
    except Exception as e:
        print(f"FAILED {test_level.upper()}: {e}")
        print(f"   Logs: {log_path}")
        print(f"   Waveforms: {cmd_filename}")
        raise
