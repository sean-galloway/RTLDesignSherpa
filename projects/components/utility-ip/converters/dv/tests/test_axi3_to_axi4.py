# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: test_axi3_to_axi4
# Purpose: AXI3 to AXI4 top wrapper test runner (READ + WRITE smoke)
#
# Author: RTL Design Sherpa
# Created: 2026-10-10

"""AXI3 to AXI4 top wrapper smoke test.

Issues one read burst and one write burst concurrently through the combined
top-level wrapper (different IDs) and verifies completion and data integrity.
Deep read/write coverage lives in the submodule suites.
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

from projects.components.utility_ip.converters.dv.tbclasses.axi3_to_axi4_tb import AXI3ToAXI4TB
from TBClasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def axi3_to_axi4_smoke_test(dut):
    """Concurrent read + write burst smoke through the top wrapper."""
    tb = AXI3ToAXI4TB(dut)

    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
    if test_level not in ('gate', 'func', 'full'):
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'gate'")
        test_level = 'gate'
    tb.log.info(f"Running {test_level.upper()} AXI3->AXI4 top wrapper smoke test")

    await tb.setup_clocks_and_reset()
    monitor_task = cocotb.start_soon(tb.axi4_monitor())

    try:
        success = True

        if test_level == 'gate':
            success = await tb.run_smoke_test()
        elif test_level == 'func':
            success = await tb.run_smoke_test(burst_len=16)
        else:
            # AXI3 ARLEN/AWLEN are 4-bit (legal 1-16 beats). Use two legal
            # 16-beat bursts so the full cell exercises more beats than func
            # without requesting an illegal length.
            success = await tb.run_smoke_test(burst_len=16, bursts=2)

        await tb.wait_clocks('aclk', 50)

        final_stats = tb.get_statistics()
        tb.log.info("=" * 80)
        tb.log.info(f"FINAL {test_level.upper()} TEST RESULTS")
        tb.log.info("=" * 80)
        tb.log.info(f"Read bursts:   {final_stats['read_bursts']}")
        tb.log.info(f"Write bursts:  {final_stats['write_bursts']}")
        tb.log.info(f"Read errors:   {final_stats['read_errors']}")
        tb.log.info(f"Write errors:  {final_stats['write_errors']}")
        tb.log.info(f"Total errors:  {final_stats['errors']}")
        tb.log.info("=" * 80)

        assert success and final_stats['errors'] == 0, (
            f"Smoke test failed: success={success}, errors={final_stats['errors']}"
        )

    finally:
        if monitor_task is not None:
            monitor_task.cancel()
            try:
                await monitor_task
            except Exception:
                pass
        await tb.wait_clocks('aclk', 10)


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def axi3_to_axi4_early_w_test(dut):
    """Drive a full W burst before AW; verifies converter buffering path."""
    tb = AXI3ToAXI4TB(dut)

    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    await tb.setup_clocks_and_reset()
    monitor_task = cocotb.start_soon(tb.axi4_monitor())

    try:
        # Use the maximum legal AXI3 burst length to fully exercise the early-W
        # buffer and the monitor's all-W-before-AW cleanup path.
        success = await tb.early_w_before_aw(burst_len=16)
        await tb.wait_clocks('aclk', 50)

        final_stats = tb.get_statistics()
        tb.log.info("=" * 80)
        tb.log.info("FINAL EARLY-W TEST RESULTS")
        tb.log.info("=" * 80)
        tb.log.info(f"Write bursts:  {final_stats['write_bursts']}")
        tb.log.info(f"Write errors:  {final_stats['write_errors']}")
        tb.log.info(f"Total errors:  {final_stats['errors']}")
        tb.log.info("=" * 80)

        assert success and final_stats['errors'] == 0, (
            f"Early-W test failed: success={success}, errors={final_stats['errors']}"
        )

    finally:
        if monitor_task is not None:
            monitor_task.cancel()
            try:
                await monitor_task
            except Exception:
                pass
        await tb.wait_clocks('aclk', 10)


def generate_test_params():
    """Smoke-test configurations, filtered by REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    all_params = [
        {'data_width': 32, 'addr_width': 32, 'id_width': 8, 'test_level': 'gate'},
        {'data_width': 64, 'addr_width': 32, 'id_width': 8, 'test_level': 'gate'},
        {'data_width': 32, 'addr_width': 32, 'id_width': 8, 'test_level': 'func'},
        {'data_width': 64, 'addr_width': 32, 'id_width': 8, 'test_level': 'func'},
        {'data_width': 128, 'addr_width': 32, 'id_width': 8, 'test_level': 'full'},
    ]

    if reg_level == 'GATE':
        return [p for p in all_params if p['test_level'] == 'gate']
    if reg_level == 'FUNC':
        return [p for p in all_params if p['test_level'] in ('gate', 'func')]
    return all_params


@pytest.mark.parametrize("params", generate_test_params())
def test_axi3_to_axi4(request, params):
    """AXI3 -> AXI4 top wrapper: concurrent read+write smoke."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/utility-ip/converters/rtl',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "axi3_to_axi4"
    toplevel = dut_name

    data_width = params['data_width']
    addr_width = params['addr_width']
    id_width = params['id_width']
    test_level = params['test_level']

    test_name_plus_params = (
        f"test_axi3_to_axi4_dw{data_width}_aw{addr_width}_id{id_width}_{test_level}"
    )

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/utility-ip/converters/rtl/filelists/axi3_to_axi4.f',
    )

    rtl_parameters = {
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': '1',
    }

    base_timeout_ms = {'gate': 10000, 'func': 30000, 'full': 90000}
    timeout_ms = base_timeout_ms[test_level]

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
    }

    compile_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
    sim_args = ["--trace", "--trace-structs", "--trace-depth", "99"]

    if bool(int(os.environ.get('COVERAGE', '0'))):
        compile_args.extend(["--coverage-line", "--coverage-toggle"])
        sim_args.append("--coverage")

    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"AXI3->AXI4 top wrapper smoke: {test_level.upper()}")
    print(f"Configuration: DW={data_width}, AW={addr_width}, ID={id_width}")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir, repo_root],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
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
        print(f"{test_level.upper()} TEST PASSED")
    except Exception as e:
        print(f"{test_level.upper()} TEST FAILED: {e}")
        print(f"   Logs: {log_path}")
        print(f"   Waveforms: {cmd_filename}")
        raise
