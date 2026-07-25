# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_dma_slave_monitors
# Purpose: FUB validation of dma_slave_monitors — drive the wrapper's AXI4 slave
#          interface with an AXI4 master BFM and confirm the slave monitors
#          observe the traffic and the tally counts it (COMPLETION bin > 0).
#
# Pattern B (projects/): cocotb_test_* + pytest wrapper.

import os
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_dma_slave_monitors(dut):
    """Drive AXI reads+writes through the wrapper; the tally must count them."""
    from tbclasses.dma_slave_monitors_tb import (
        DmaSlaveMonitorsTB, bin_of, PKT_COMPLETION)

    tb = DmaSlaveMonitorsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_traffic(n_writes=8, n_reads=8, burst_len=4)
    await tb.freeze_flush()

    compl = await tb.read_bin(bin_of(0, PKT_COMPLETION, 0))  # AXI/COMPLETION/0x00
    dut._log.info(f"[dma_slave_monitors] COMPLETION bin 0x0100 = {compl}")
    assert compl > 0, (
        "no COMPLETION packets tabulated — the slave-monitor -> arbiter -> tally "
        "path is not counting traffic through the wrapper")


# ----------------------------------------------------------------------------
def test_dma_slave_monitors(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba_shared':  'rtl/amba/shared',
        'rtl_amba_monitor': 'rtl/amba/monitor',
        'rtl_amba_inc':     'rtl/amba/includes',
    })
    dut_name = "dma_slave_monitors"
    dv_dir = os.path.abspath(os.path.join(tests_dir, '..'))  # flows-stream-monitor/dv
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name = f"test_{worker_id}_{dut_name}"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/NexysA7/stream_characterization/flows-stream-monitor/"
                      "rtl/filelists/dma_slave_monitors.f")
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # Small config: 1 channel, 64-bit data (axi4_dma_slaves default), 8-entry cache.
    rtl_parameters = {
        'NUM_CHANNELS': '1', 'AXI_ID_WIDTH': '8', 'AXI_ADDR_WIDTH': '32',
        'AXI_DATA_WIDTH': '64', 'AXI_USER_WIDTH': '1', 'MAX_TRANSACTIONS': '16',
        'TALLY_COUNT_WIDTH': '32', 'TALLY_CACHE_DEPTH': '8',
        'TALLY_ADDR_BITS': '16', 'TALLY_NUM_LATCH': '4',
    }
    extra_env = {
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'PARAM_AXI_ID_WIDTH': '8', 'PARAM_AXI_ADDR_WIDTH': '32',
        'PARAM_AXI_DATA_WIDTH': '64', 'PARAM_AXI_USER_WIDTH': '1',
    }
    compile_args = [
        '+define+SIMULATION', '-Wno-DECLFILENAME', '-Wno-WIDTHEXPAND',
        '-Wno-WIDTHTRUNC', '-Wno-UNUSEDPARAM', '-Wno-TIMESCALEMOD',
        '-Wno-UNUSEDSIGNAL', '-Wno-PINCONNECTEMPTY',
    ]
    create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    run(
        python_search=[tests_dir, dv_dir],
        verilog_sources=verilog_sources,
        includes=includes + [rtl_dict['rtl_amba_shared'], sim_build],
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_dma_slave_monitors",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        keep_files=True,
        compile_args=compile_args,
    )
