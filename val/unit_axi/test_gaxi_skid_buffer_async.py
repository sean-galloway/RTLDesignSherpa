import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.TBClasses.tbbase import TBBase
from CocoTBFramework.TBClasses.gaxi_buffer import GaxiBufferTB
from CocoTBFramework.TBClasses.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=500, timeout_unit="us")
async def fifo_test(dut):
    '''Test the Skid Buffer as thoroughly as possible'''
    tb = GaxiBufferTB(
                dut,
                wr_clk=dut.i_axi_wr_aclk,
                wr_rstn=dut.i_axi_wr_aresetn,
                rd_clk=dut.i_axi_rd_aclk,
                rd_rstn=dut.i_axi_rd_aresetn
    )

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)
    await tb.start_clock('i_axi_wr_aclk', tb.TEST_CLK_WR, 'ns')
    await tb.start_clock('i_axi_rd_aclk', tb.TEST_CLK_RD, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('i_axi_wr_aclk', 6)
    await tb.deassert_reset()
    await tb.wait_clocks('i_axi_wr_aclk', 6)
    tb.log.info("Starting test...")
    await tb.simple_incremental_loops(count=10*tb.TEST_DEPTH, use_fast=True, delay_clks_after=20)
    await tb.simple_incremental_loops(count=100*tb.TEST_DEPTH, use_fast=False, delay_clks_after=20)

    # debug parameters if needed
    # (8, 2, "mux", 10, 15),
    # (8, 2, "mux", 15, 10),
    # (8, 2, "delay", 10, 15),
    # (8, 2, "delay", 15, 10),

def generate_test_params():
    widths = [8]
    depths = [2, 4, 6, 8]
    modes = ["fifo_mux", "fifo_flop"]
    clk_pairs = [(10, 15), (15, 10)]  # Clock write/read variations

    # Generate all permutations
    params = list(product(widths, depths, modes, clk_pairs))
    
    # Flatten each tuple to match the required structure
    params = [(w, d, m, clk_wr, clk_rd) for (w, d, m, (clk_wr, clk_rd)) in params]

    return params

params = generate_test_params()

# @pytest.mark.parametrize("data_width, depth, mode, clk_wr, clk_rd", params)
@pytest.mark.parametrize("data_width, depth, mode, clk_wr, clk_rd", [(8, 2, "fifo_flop", 10, 15), (8, 2, "fifo_mux", 10, 15)])
def test_skid_buffer_async(request, data_width, depth, mode, clk_wr, clk_rd):
    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_axi': 'rtl/axi'})

    # set up all of the test names
    dut_name = "gaxi_skid_buffer_async"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "find_first_set.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "find_last_set.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "leading_one_trailing_one.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_johnson.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "grayj2bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "glitch_free_n_dff_arn.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_axi'], "gaxi_fifo_async.sv"),
        os.path.join(rtl_dict['rtl_axi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv"),
    ]

    # create a human readable test identifier
    w_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{dut_name}_w{w_str}_d{d_str}_{mode}_clkwr{clk_wr}_clkrd{clk_rd}"
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
    extra_env['TEST_CLK_WR'] = str(clk_wr)
    extra_env['TEST_CLK_RD'] = str(clk_rd)

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
