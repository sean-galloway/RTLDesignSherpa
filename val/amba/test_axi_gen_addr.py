# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axi_gen_addr
# Purpose: Test runner for axi_gen_addr — next-address generation for AXI bursts
#
# Documentation: docs/markdown/rtl-amba/shared/axi_gen_addr.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-08-18

"""Runner for axi_gen_addr.

Test intelligence lives in the TB class
(`bin/TBClasses/amba/axi_gen_addr_tb.py`) per rtl/amba/CLAUDE.md Rule #0
and GLOBAL_REQUIREMENTS 2.1/2.3/2.4; this file holds only the parameter
grid and the cocotb_test.run() call.
"""

import os
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.amba.axi_gen_addr_tb import AxiGenAddrTB
from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def axi_gen_addr_test(dut):
    tb = AxiGenAddrTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_all()


# ODW == DW is the plain case; ODW < DW exercises the increment cap the
# width converters depend on. AW=40 covers a non-32 address width.
params = [
    (32,  32,  32,  8),
    (32,  64,  64,  8),
    (32,  64,  32,  8),
    (32, 128,  32,  8),
    (40,  64,  64,  8),
    (32,  32,  32,  4),
]


@pytest.mark.parametrize("aw, dw, odw, len_w", params)
def test_axi_gen_addr(request, aw, dw, odw, len_w):
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba_shared': 'rtl/amba/shared',
    })

    dut_name = "axi_gen_addr"
    toplevel = dut_name
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi_gen_addr.f")

    test_level = os.environ.get('TEST_LEVEL', 'gate')
    test_name_plus_params = (f"test_{worker_id}_{dut_name}_aw{aw:03d}"
                             f"_dw{dw:03d}_odw{odw:03d}_len{len_w:02d}"
                             f"_{test_level}")
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    seed = int(os.environ.get('SEED', str(random.randint(0, 100000))))

    rtl_parameters = {
        'AW': str(aw), 'DW': str(dw), 'ODW': str(odw), 'LEN': str(len_w),
    }
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_LEVEL': test_level,
        'TEST_AW': str(aw), 'TEST_DW': str(dw),
        'TEST_ODW': str(odw), 'TEST_LEN': str(len_w),
        'SEED': str(seed),
    }

    compile_args = ["-Wall", "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"]
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module,
                                   test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
        )
    except Exception as e:
        print(f"axi_gen_addr test failed: {e}")
        print(f"Logs at: {log_path}")
        print(f"View waveforms: {cmd_filename}")
        raise
