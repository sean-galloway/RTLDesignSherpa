# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: test_axi4_dwidth_converter_rd_ooo_r
# Purpose: BUG-008 TDD cocotb test for cross-ID out-of-order R RID carry.
#
# Isolated in its own module so it does not run as part of the general
# test_axi4_dwidth_converter_rd regression (the normal regression and the
# OOO-R scenario create/destroy BFMs differently, and running them back-to-back
# in the same cocotb module caused callback/BFM state pollution).

import os
import random
import cocotb
from cocotb_test.simulator import run
from TBClasses.axi4.axi4_dwidth_converter_rd_tb import AXI4DWidthConverterReadTB
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def axi4_dwidth_converter_rd_ooo_r_test(dut):
    """BUG-008 TDD: cross-ID out-of-order R response RID/ruser carry."""
    os.environ['DWIDTH_RD_OOO_R_TEST'] = '1'
    tb = AXI4DWidthConverterReadTB(dut)

    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    await tb.setup_clocks_and_reset()

    try:
        ok = await tb.run_ooo_r_test()
        await tb.wait_clocks('aclk', 50)
        stats = tb.get_statistics()
        if ok and stats['errors'] == 0:
            tb.log.info("BUG-008 OOO-R TEST PASSED")
        else:
            tb.log.error("BUG-008 OOO-R TEST FAILED")
            assert False, "OOO-R RID-carry test failed"
    finally:
        await tb.wait_clocks('aclk', 10)


def test_axi4_dwidth_converter_rd_ooo_r(request):
    """BUG-008 TDD: run the OOO-R RID-carry cocotb test standalone."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba_shared': 'rtl/amba/shared',
        'rtl_converters': 'projects/components/utility-ip/converters/rtl',
        'rtl_amba_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "axi4_dwidth_converter_rd"
    toplevel = dut_name
    s_data_width, m_data_width = 128, 32
    test_name_plus_params = "test_axi4_dwidth_converter_rd_ooo_r"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/utility-ip/converters/rtl/filelists/axi4_dwidth_converter_rd.f'
    )
    rtl_parameters = {
        'S_AXI_DATA_WIDTH': str(s_data_width),
        'M_AXI_DATA_WIDTH': str(m_data_width),
        'AXI_ID_WIDTH': '8',
        'AXI_ADDR_WIDTH': '32',
        'AXI_USER_WIDTH': '1',
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'COCOTB_TEST_TIMEOUT': '30000',
        'TESTCASE': 'axi4_dwidth_converter_rd_ooo_r_test',
        'SEED': os.environ.get('SEED', str(random.randint(0, 1000000))),
        'S_AXI_DATA_WIDTH': str(s_data_width),
        'M_AXI_DATA_WIDTH': str(m_data_width),
        'AXI_ID_WIDTH': '8',
        'AXI_ADDR_WIDTH': '32',
        'AXI_USER_WIDTH': '1',
        'TEST_CLK_PERIOD': '10',
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
    print(f"BUG-008 OOO-R RID-carry test")
    print(f"Conversion: {s_data_width}-bit -> {m_data_width}-bit (downsize 4:1)")
    print(f"{'='*80}")

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
            sim_args=sim_args,
            plus_args=['--trace'] if enable_waves else [],
        )
        print("OOO-R TEST PASSED")
    except Exception as e:
        print(f"OOO-R TEST FAILED: {str(e)}")
        print(f"   Logs: {log_path}")
        print(f"   Waveforms: {cmd_filename}")
        raise
