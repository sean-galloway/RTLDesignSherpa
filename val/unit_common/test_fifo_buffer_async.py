import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.fifo.fifo_buffer import FifoBufferTB
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.fifo.fifo_buffer_configs import RANDOMIZER_CONFIGS


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def fifo_async_test(dut):
    '''Test the Asynchronous FIFO Buffer as thoroughly as possible'''
    # Create testbench with separate write and read clocks and reset signals
    tb = FifoBufferTB(
        dut, 
        wr_clk=dut.i_wr_clk, 
        wr_rstn=dut.i_wr_rst_n,
        rd_clk=dut.i_rd_clk,
        rd_rstn=dut.i_rd_rst_n
    )
    
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)
    
    # Start both clocks with possibly different periods
    await tb.start_clock('i_wr_clk', tb.TEST_CLK_WR, 'ns')
    await tb.start_clock('i_rd_clk', tb.TEST_CLK_RD, 'ns')
    
    # Reset sequence
    await tb.assert_reset()
    await tb.wait_clocks('i_wr_clk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('i_wr_clk', 5)
    tb.log.info("Starting test...")

    # Run tests with different randomizer configurations
    delay_keys = ['fixed', 'constrained', 'burst_pause']
    for delay_key in delay_keys:
        await tb.simple_incremental_loops(count=10*tb.TEST_DEPTH, delay_key=delay_key, delay_clks_after=30)
        # Add extra delay between test iterations to allow for clock domain crossing
        await tb.wait_clocks('i_wr_clk', 30)


def generate_width_depth_clk_params():
    widths = [8]
    depths = [4, 8]  # Async FIFOs typically need slightly larger depths
    wr_clk_periods = [10]
    rd_clk_periods = [8, 12]  # Different read clock periods to test async behavior
    modes = ['fifo_mux', 'fifo_flop']

    return list(product(widths, depths, wr_clk_periods, rd_clk_periods, modes))

params = generate_width_depth_clk_params()

@pytest.mark.parametrize("data_width, depth, wr_clk_period, rd_clk_period, mode", params)
def test_fifo_async(request, data_width, depth, wr_clk_period, rd_clk_period, mode):

    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common'})

    # set up all of the test names
    dut_name = "fifo_async"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "glitch_free_n_dff_arn.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "gray2bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_bingray.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv"),
    ]

    # create a human readable test identifier
    w_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    wcl_str = TBBase.format_dec(wr_clk_period, 3)
    rcl_str = TBBase.format_dec(rd_clk_period, 3)
    test_name_plus_params = f"test_buffer_async_w{w_str}_d{d_str}_wcl{wcl_str}_rcl{rcl_str}_{mode}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # use it in the simbuild path
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

    # Add test parameters; these are passed to the environment, but not the RTL
    extra_env['TEST_DATA_WIDTH'] = str(data_width)
    extra_env['TEST_DEPTH'] = str(depth)
    extra_env['TEST_CLK_WR'] = str(wr_clk_period)
    extra_env['TEST_CLK_RD'] = str(rd_clk_period)
    extra_env['TEST_MODE'] = mode
    extra_env['TEST_KIND'] = 'sync'

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
