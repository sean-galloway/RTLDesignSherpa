"""axi4ace_master_rd_monlite: the lite-monitor sibling of axi4ace_master_rd_mon.

Derived 2026-10-05 from val/amba/test_axi4ace_master_rd.py: same ACE read TB,
same scenarios, the DUT swapped for the _monlite wrapper. The TB guards every
cfg write with hasattr, so the lite's smaller cfg set is driven and nothing
else is touched.

WaveDrom tests are omitted because TBClasses.wavedrom_user.ace does not exist
yet; this is noted as future work.
"""
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi4ace_master_rd_monlite
# Purpose: AXI4-ACE Master Read Monitor-lite Integration Test
#
# Documentation: PRD.md
# Subsystem: tests

import os
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.ace.monitor.axi4ace_master_monitor_tb import AXI4ACEMonitorTB
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axi4ace_master_rd_monlite_test(dut):
    """AXI4-ACE master read monitor-lite integration test."""
    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()

    tb = AXI4ACEMonitorTB(
        dut,
        is_write=False,
        is_slave=False,
        aclk=dut.aclk,
        aresetn=dut.aresetn
    )

    await tb.initialize()
    await tb.run_integration_tests(test_level=test_level)


def validate_addr_width(addr_width):
    """Validate address width meets AXI4 specification constraints."""
    addr_w = int(addr_width)
    if addr_w > 64:
        raise ValueError(
            f"Invalid AXI4 configuration: AXI_ADDR_WIDTH={addr_w} exceeds maximum of 64-bits. "
            f"AXI4 specification limits address width to 64-bits."
        )


def generate_axi4ace_monitor_params():
    """
    Generate AXI4-ACE master read monitor-lite parameter combinations.

    Parameter tuple:
        (id_width, addr_width, data_width, user_width, max_trans,
         skid_ar, skid_r, test_level)

    REG_LEVEL values:
        GATE: 1 test - Quick smoke test
        FUNC: 3 tests - Functional validation with variations
        FULL: 9 tests - Comprehensive testing
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        params = [
            (8, 32, 32, 1, 16, 2, 4, 'gate'),
        ]
    elif reg_level == 'FUNC':
        params = [
            (8, 32, 32, 1, 16, 2, 4, 'gate'),   # Standard config
            (8, 32, 32, 1, 16, 4, 8, 'func'),  # Deeper skid buffers
            (8, 32, 32, 1, 32, 2, 4, 'func'),  # More transactions
        ]
    else:  # FULL
        test_levels = ['gate', 'func', 'full']
        configs = [
            (8, 32, 32, 1, 16, 2, 4),  # Standard
            (8, 32, 32, 1, 16, 4, 8),  # Deep skid
            (8, 32, 32, 1, 32, 2, 4),  # Many transactions
        ]
        params = [
            (id_w, addr_w, data_w, user_w, max_t, skid_ar, skid_r, level)
            for (id_w, addr_w, data_w, user_w, max_t, skid_ar, skid_r) in configs
            for level in test_levels
        ]

    for param in params:
        _, addr_w, _, _, _, _, _, _ = param
        validate_addr_width(addr_w)

    return params


# ============================================================================
# PyTest Test Runner
# ============================================================================
@pytest.mark.parametrize(
    "id_width, addr_width, data_width, user_width, max_trans, skid_ar, skid_r, test_level",
    generate_axi4ace_monitor_params()
)
def test_axi4ace_master_rd_monlite(
    id_width, addr_width, data_width, user_width, max_trans, skid_ar, skid_r, test_level
):
    """
    Integration test runner for AXI4-ACE master read monitor-lite.

    Controlled by REG_LEVEL environment variable:
        GATE: 1 test  - Quick smoke test
        FUNC: 3 tests - Functional validation (default)
        FULL: 9 tests - Comprehensive testing
    """
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_ace': 'rtl/amba/ace/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
        'rtl_shared': 'rtl/amba/shared',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    dut_name = "axi4ace_master_rd_monlite"
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()

    test_name = (
        f"test_{worker_id}_{dut_name}_iw{id_width}_aw{addr_width}_dw{data_width}_"
        f"uw{user_width}_mt{max_trans}_sk{skid_ar}x{skid_r}_{test_level}_{reg_level}"
    )

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        module=dut_name
    )

    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # Core calculated sizes (must match the wrapper's ARSize/RSize defaults).
    ar_size = (
        id_width + addr_width + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + user_width + 4
    )
    r_size = id_width + data_width + 2 + 1 + user_width

    rtl_parameters = {
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': str(user_width),
        # Note: axi4ace_master_rd (and therefore the lite wrapper) does NOT
        # declare AXI_WSTRB_WIDTH/SW; omit them.
        'UNIT_ID': '1',
        'AGENT_ID': '10',
        'MAX_TRANSACTIONS': str(max_trans),
        'SKID_DEPTH_AR': str(skid_ar),
        'SKID_DEPTH_R': str(skid_r),
        'AW': str(addr_width),
        'DW': str(data_width),
        'IW': str(id_width),
        'UW': str(user_width),
        'ARSize': str(ar_size),
        'RSize': str(r_size),
    }

    validate_addr_width(rtl_parameters['AXI_ADDR_WIDTH'])

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_LEVEL': test_level,
        'TEST_ID_WIDTH': str(id_width),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_USER_WIDTH': str(user_width),
        'TEST_CLK_PERIOD': '10',
        'TIMEOUT_CYCLES': '2000',
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }

    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED", "-Wno-DECLFILENAME", "-Wno-PINMISSING",
        "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC",
        "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE", "-Wno-TIMESCALEMOD",
    ]

    print(f"\n{'='*80}")
    print(f"AXI4-ACE Master Read Monitor-lite Integration Test")
    print(f"Test Level: {test_level}")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes + [rtl_dict['rtl_common'], sim_build],
            toplevel=dut_name,
            module="test_axi4ace_master_rd_monlite",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            plus_args=(['--trace'] if enable_waves else []),
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"PASSED: {test_name}")
    except Exception as e:
        print(f"FAILED: {test_name}")
        print(f"Error: {str(e)}")
        raise
