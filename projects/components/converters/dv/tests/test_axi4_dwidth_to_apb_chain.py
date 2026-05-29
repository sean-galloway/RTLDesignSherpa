# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: test_axi4_dwidth_to_apb_chain
# Purpose: FUB-level test for the axi4_dwidth_converter_rd → axi4_to_apb_shim chain.
#
# This is the chain the bridge instantiates between a wide master and a
# narrow APB peripheral. The b2b page-probe scenarios here exist to
# surface the bridge's 1x5_rd_boundary_probe failure at the FUB level.

"""
AXI4 dwidth+apb read chain test runner.

Test Levels:
- gate: Quick smoke (single bursts + b2b smoke).
- func: Page-probe b2b reads (this is where the bridge bug shows up).
- full: Full coverage (page probes + random bursts + larger b2b sweep).
"""

import os
import random
import sys
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_repo_root, get_paths, create_view_cmd

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.converters.dv.tbclasses.axi4_dwidth_to_apb_chain_tb import (
    AXI4DWidthToAPBChainTB,
)
from TBClasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_axi4_dwidth_to_apb_chain(dut):
    """Chain test: wide AXI4 master → dwidth(rd) → axi4_to_apb_shim → narrow APB."""
    tb = AXI4DWidthToAPBChainTB(dut)

    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
    if test_level not in ('gate', 'func', 'full'):
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'gate'")
        test_level = 'gate'

    tb.log.info(f"Running {test_level.upper()} chain test")

    await tb.setup_clocks_and_reset()
    monitor_task = cocotb.start_soon(tb.apb_transaction_monitor())

    try:
        if test_level == 'gate':
            success = await tb.run_basic_test()
        elif test_level == 'func':
            success = await tb.run_medium_test()
        else:
            success = await tb.run_full_test()

        await tb.wait_clocks('aclk', 100)

        stats = tb.get_statistics()
        tb.log.info("=" * 80)
        tb.log.info(f"FINAL {test_level.upper()} CHAIN STATS")
        tb.log.info("=" * 80)
        for k, v in stats.items():
            tb.log.info(f"  {k:30s} {v}")

        if success and stats['errors'] == 0:
            tb.log.info(f"ALL {test_level.upper()} CHAIN TESTS PASSED")
        else:
            err = []
            if not success:
                err.append("suite failures")
            if stats['errors']:
                err.append(f"{stats['errors']} errors")
            tb.log.error(f"{test_level.upper()} CHAIN TESTS FAILED: {', '.join(err)}")
            assert False, f"Chain test failures: {', '.join(err)}"
    finally:
        await tb.wait_clocks('aclk', 10)


def generate_test_params():
    """
    Param sweep:
      - (S_AXI=64,  APB=32) ratio 2:1
      - (S_AXI=128, APB=32) ratio 4:1
      - (S_AXI=128, APB=64) ratio 2:1
    All with id_width=8.
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    base = [
        {'s_data_width': 64,  'apb_data_width': 32, 'id_width': 8, 'test_level': 'gate'},
        {'s_data_width': 128, 'apb_data_width': 32, 'id_width': 8, 'test_level': 'gate'},
        {'s_data_width': 128, 'apb_data_width': 64, 'id_width': 8, 'test_level': 'gate'},

        {'s_data_width': 64,  'apb_data_width': 32, 'id_width': 8, 'test_level': 'func'},
        {'s_data_width': 128, 'apb_data_width': 32, 'id_width': 8, 'test_level': 'func'},
        {'s_data_width': 128, 'apb_data_width': 64, 'id_width': 8, 'test_level': 'func'},

        {'s_data_width': 64,  'apb_data_width': 32, 'id_width': 8, 'test_level': 'full'},
        {'s_data_width': 128, 'apb_data_width': 32, 'id_width': 8, 'test_level': 'full'},
        {'s_data_width': 128, 'apb_data_width': 64, 'id_width': 8, 'test_level': 'full'},
    ]

    if reg_level == 'GATE':
        return [p for p in base if p['test_level'] == 'gate']
    if reg_level == 'FUNC':
        return [p for p in base if p['test_level'] in ('gate', 'func')]
    return base


@pytest.mark.parametrize("params", generate_test_params())
def test_axi4_dwidth_to_apb_chain(request, params):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/converters/rtl',
        'rtl_amba_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_apb': 'rtl/amba/apb',
        'rtl_amba_axi4': 'rtl/amba/axi4',
        'rtl_amba_shared': 'rtl/amba/shared',
        'rtl_amba_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
    })

    dut_name = "axi4_dwidth_to_apb_chain"
    toplevel = dut_name

    s_data_width = params['s_data_width']
    apb_data_width = params['apb_data_width']
    id_width = params['id_width']
    test_level = params['test_level']
    ratio = s_data_width // apb_data_width

    test_name_plus_params = (
        f"test_axi4_dwidth_to_apb_chain_"
        f"s{s_data_width}_apb{apb_data_width}_id{id_width}_{test_level}"
    )

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/converters/rtl/filelists/axi4_dwidth_to_apb_chain.f',
    )

    rtl_parameters = {
        'S_AXI_DATA_WIDTH':  str(s_data_width),
        'APB_DATA_WIDTH':    str(apb_data_width),
        'AXI_ID_WIDTH':      str(id_width),
        'AXI_ADDR_WIDTH':    '32',
        'APB_ADDR_WIDTH':    '32',
        'AXI_USER_WIDTH':    '1',
    }

    base_timeout_ms = {'gate': 15000, 'func': 45000, 'full': 120000}
    timeout_ms = base_timeout_ms[test_level]

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),
        'SEED': os.environ.get('SEED', str(random.randint(0, 1000000))),
        'TEST_LEVEL': test_level,
        'S_AXI_DATA_WIDTH':  str(s_data_width),
        'APB_DATA_WIDTH':    str(apb_data_width),
        'AXI_ID_WIDTH':      str(id_width),
        'AXI_ADDR_WIDTH':    '32',
        'APB_ADDR_WIDTH':    '32',
        'AXI_USER_WIDTH':    '1',
    }

    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    sim_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Chain (dwidth+apb) RD Test: {test_level.upper()}")
    print(f"S_AXI={s_data_width}b -> APB={apb_data_width}b (ratio {ratio}:1), id={id_width}")
    print(f"Expected Duration: {timeout_ms/1000:.1f}s")
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
        print(f"PASS: Chain {test_level.upper()} (S={s_data_width} APB={apb_data_width})")
    except Exception as e:
        print(f"FAIL: Chain {test_level.upper()} (S={s_data_width} APB={apb_data_width}): {e}")
        print(f"   Logs: {log_path}")
        print(f"   Waveforms: {cmd_filename}")
        raise
