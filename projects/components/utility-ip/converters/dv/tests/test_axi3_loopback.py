# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: test_axi3_loopback
# Purpose: AXI4 -> axi4_to_axi3 -> axi3_to_axi4 -> AXI4 loopback equivalence test runner
#
# Author: RTL Design Sherpa
# Created: 2026-10-10

"""AXI4/AXI3 loopback equivalence chain test runner.

Topology:
  AXI4MasterRead/Write (s_axi_) -> axi4_to_axi3 -> axi3_to_axi4
                                    -> AXI4SlaveRead/Write (m_axi_, shared memory model)

This is the integration proof that the converter pair is identity for legal
AXI4 traffic.  The write side serializes because axi3_to_axi4_wr enforces a
single-active-write contract; the read side pipelines.
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

from projects.components.utility_ip.converters.dv.tbclasses.axi3_loopback_tb import AXI3LoopbackTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def axi3_loopback_equivalence_test(dut):
    """Run the loopback equivalence chain scenarios."""
    tb = AXI3LoopbackTB(dut)

    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
    if test_level not in ('gate', 'func', 'full'):
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'gate'")
        test_level = 'gate'
    tb.log.info(f"Running {test_level.upper()} AXI3 loopback equivalence test")

    await tb.setup_clocks_and_reset()
    monitor_task = cocotb.start_soon(tb.far_side_monitor())

    try:
        if test_level == 'gate':
            success = await tb.run_gate_suite()
        elif test_level == 'func':
            success = await tb.run_func_suite()
        else:
            success = await tb.run_full_suite()

        await tb.wait_clocks('aclk', 100)

        stats = tb.get_statistics()
        tb.log.info("=" * 80)
        tb.log.info(f"FINAL {test_level.upper()} LOOPBACK STATS")
        tb.log.info("=" * 80)
        for k, v in stats.items():
            tb.log.info(f"  {k:30s} {v}")

        if success and stats['errors'] == 0:
            tb.log.info(f"ALL {test_level.upper()} LOOPBACK TESTS PASSED")
        else:
            err = []
            if not success:
                err.append("suite failures")
            if stats['errors']:
                err.append(f"{stats['errors']} errors")
            tb.log.error(f"{test_level.upper()} LOOPBACK TESTS FAILED: {', '.join(err)}")
            assert False, f"Loopback test failures: {', '.join(err)}"
    finally:
        if monitor_task is not None:
            monitor_task.cancel()
            try:
                await monitor_task
            except BaseException:
                pass
        await tb.wait_clocks('aclk', 10)


def generate_test_params():
    """Loopback equivalence configurations, filtered by REG_LEVEL."""
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
def test_axi3_loopback(request, params):
    """AXI4 -> AXI3 -> AXI4 loopback equivalence chain."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/utility-ip/converters/rtl',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "axi3_loopback"
    toplevel = dut_name

    data_width = params['data_width']
    addr_width = params['addr_width']
    id_width = params['id_width']
    test_level = params['test_level']

    test_name_plus_params = (
        f"test_axi3_loopback_dw{data_width}_aw{addr_width}_id{id_width}_{test_level}"
    )

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/utility-ip/converters/rtl/filelists/axi3_loopback.f',
    )

    rtl_parameters = {
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': '1',
    }

    base_timeout_ms = {'gate': 20000, 'func': 60000, 'full': 180000}
    timeout_ms = base_timeout_ms[test_level]

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),
        'SEED': os.environ.get('SEED', '42'),
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
    print(f"AXI3 loopback equivalence chain: {test_level.upper()}")
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
        print(f"PASS: AXI3 loopback {test_level.upper()}")
    except Exception as e:
        print(f"FAIL: AXI3 loopback {test_level.upper()}: {e}")
        print(f"   Logs: {log_path}")
        print(f"   Waveforms: {cmd_filename}")
        raise
