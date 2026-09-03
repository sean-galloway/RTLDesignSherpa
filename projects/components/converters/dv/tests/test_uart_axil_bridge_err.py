# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 RTL Design Sherpa
#
# Module: test_uart_axil_bridge_err
# Purpose: Prove the bridge reports a non-OKAY AXI response instead of "OK"
#
# Subsystem: tests

"""UART to AXI4-Lite bridge: error-response reporting.

The main test suite only ever sees OKAY, so it passed both before and after
the fix that made the bridge look at bresp/rresp. This drives a slave that
answers SLVERR and asserts the bridge says "ERR" -- it fails against the
pre-fix RTL, which answered "OK" to a rejected write and formatted stale bus
data as a normal read result.
"""

import os
import random
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_repo_root, get_paths, create_view_cmd, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.converters.dv.tbclasses.uart_axil_bridge_tb import UARTAXILBridgeTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist

SLVERR = 2


@cocotb.test(timeout_time=500, timeout_unit="ms")
async def uart_axil_bridge_err_test(dut):
    tb = UARTAXILBridgeTB(dut)
    await tb.setup_clocks_and_reset()

    # Make every access on the master side answer SLVERR.
    tb.axil4_slave_wr.resp_override = lambda _addr: SLVERR
    tb.axil4_slave_rd.resp_override = lambda _addr: SLVERR

    failures = []

    got = await tb.send_uart_command_raw("W 100 DEADBEEF\n", 4)
    if got != "ERR\n":
        failures.append(f"write with SLVERR answered {got!r}, expected 'ERR\\n'")

    got = await tb.send_uart_command_raw("R 100\n", 4)
    if got != "ERR\n":
        failures.append(f"read with SLVERR answered {got!r}, expected 'ERR\\n'")

    # And the healthy path still works once the override is lifted, so the
    # test cannot pass by the bridge simply answering ERR to everything.
    tb.axil4_slave_wr.resp_override = None
    tb.axil4_slave_rd.resp_override = None

    got = await tb.send_uart_command_raw("W 200 12345678\n", 3)
    if got != "OK\n":
        failures.append(f"write with OKAY answered {got!r}, expected 'OK\\n'")

    assert not failures, "; ".join(failures)


@pytest.mark.parametrize("params", [
    {'axil_data_width': 32, 'axil_addr_width': 32, 'clks_per_bit': 868, 'test_level': 'gate'},
])
def test_uart_axil_bridge_err(request, params):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/converters/rtl',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    dut_name = "uart_axil_bridge"
    toplevel = dut_name

    axil_data_width = params['axil_data_width']
    axil_addr_width = params['axil_addr_width']
    clks_per_bit = params['clks_per_bit']
    test_level = params['test_level']

    test_name_plus_params = (f"test_uart_axil_bridge_err_"
                             f"dw{axil_data_width}_aw{axil_addr_width}_"
                             f"baud{clks_per_bit}_{test_level}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/converters/rtl/filelists/uart_axil_bridge.f'
    )

    rtl_parameters = {
        'AXIL_ADDR_WIDTH': str(axil_addr_width),
        'AXIL_DATA_WIDTH': str(axil_data_width),
        'CLKS_PER_BIT': str(clks_per_bit),
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'COCOTB_TEST_TIMEOUT': '30000',
        'SEED': os.environ.get('SEED', str(random.randint(0, 1000000))),
        'TEST_LEVEL': test_level,
        'AXIL_DATA_WIDTH': str(axil_data_width),
        'AXIL_ADDR_WIDTH': str(axil_addr_width),
        'CLKS_PER_BIT': str(clks_per_bit),
    }

    create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    run(
        python_search=[tests_dir, repo_root],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=toplevel,
        module=module,
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=False,
        keep_files=True,
    )
