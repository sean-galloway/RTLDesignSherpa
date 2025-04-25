import os
import random
from itertools import product

import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer import GaxiBufferTB
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_configs import RANDOMIZER_CONFIGS


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def skid_buffer_test(dut):
    '''Test the Skid Buffer as thoroughly as possible'''
    tb = GaxiBufferTB(dut, wr_clk=dut.i_axi_aclk, wr_rstn=dut.i_axi_aresetn)
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

    for delay_key in RANDOMIZER_CONFIGS.keys():
        await tb.simple_incremental_loops(count=10*tb.TEST_DEPTH, delay_key=delay_key,  delay_clks_after=20)


def generate_width_depth_mode_params():
    widths = [8]
    # depths = [2, 4, 6, 8, 10]
    depths = [4]
    modes = ['skid']
    return list(product(widths, depths, modes))

params = generate_width_depth_mode_params()

# @pytest.mark.parametrize("data_width, depth", [(8,2)])
@pytest.mark.parametrize("data_width, depth, mode", params)
def test_skid_buffer(request, data_width, depth, mode):

    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_axi': 'rtl/axi'})

    # set up all of the test names
    dut_name = "gaxi_skid_buffer"
    toplevel = dut_name

    # get the verilog sources
    verilog_sources = [
        os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv"),
    ]

    # create a human readable test identifier
    w_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{dut_name}_w{w_str}_d{d_str}"
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
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
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


    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    sim_args = [
        "--trace-fst",  # Tell Verilator to use FST
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = [
        "+trace",
    ]

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
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure