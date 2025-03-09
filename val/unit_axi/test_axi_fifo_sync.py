import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from TBClasses.tbbase import TBBase
from TBClasses.gaxi_buffer import GaxiBufferTB
from TBClasses.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def fifo_test(dut):
    '''Test the Skid Buffer as thoroughly as possible'''
    tb = GaxiBufferTB(dut, dut.i_axi_aclk, dut.i_axi_aresetn)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)
    await tb.start_clock('i_axi_aclk', 10, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('i_axi_aclk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('i_axi_aclk', 5)
    tb.log.info("Starting test...")
    await tb.simple_incremental_loops(count=10*tb.TEST_DEPTH, use_fast=True, delay_clks_after=20)
    await tb.simple_incremental_loops(count=100*tb.TEST_DEPTH, use_fast=False, delay_clks_after=20)


def generate_width_depth_mode_params():
    widths = [8]
    depths = [2, 4, 6, 8]
    modes = ['mux', 'flopped']
    return list(product(widths, depths, modes))

params = generate_width_depth_mode_params()

@pytest.mark.parametrize("data_width, depth, mode", params)
def test_axi_fifo_sync(request, data_width, depth, mode):

    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_axi': 'rtl/axi'})

    # set up all of the test names
    dut_name = "axi_fifo_sync"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv"),
    ]

    # create a human readable test identifier
    w_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_fifo_sync_w{w_str}_d{d_str}_{mode}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # use it int he simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters
    rtl_parameters = {k.upper(): str(v) for k, v in locals().items() if k in ["data_width", "depth"]}

    # Environment variables
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        # 'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000))
    }

    # Add test parameters; these are passed t the environment, but not the RTL
    extra_env['TEST_WIDTH'] = str(data_width)
    extra_env['TEST_DEPTH'] = str(depth)
    extra_env['TEST_MODE'] = str(mode)

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=True,
            keep_files=True
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
