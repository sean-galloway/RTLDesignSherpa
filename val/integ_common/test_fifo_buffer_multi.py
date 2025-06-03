import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.fifo.fifo_buffer_multi import FifoMultiBufferTB
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.fifo.fifo_buffer_configs import RANDOMIZER_CONFIGS


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def fifo_async_test(dut):
    '''Test the Asynchronous FIFO Buffer as thoroughly as possible'''
    # Create testbench with separate write and read clocks and reset signals
    tb = FifoMultiBufferTB(
        dut,
        wr_clk=dut.i_clk,
        wr_rstn=dut.i_rst_n
    )

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)

    # Start both clocks with possibly different periods
    await tb.start_clock('i_clk', tb.TEST_CLK_WR, 'ns')

    # Reset sequence
    await tb.assert_reset()
    await tb.wait_clocks('i_clk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('i_clk', 5)
    tb.log.info("Starting test...")

    # Run tests with different randomizer configurations
    for delay_key in RANDOMIZER_CONFIGS.keys():
        await tb.simple_incremental_loops(count=10*tb.TEST_DEPTH, delay_key=delay_key,  delay_clks_after=20)


def generate_width_depth_clk_params():
    addr_widths = [4, 6, 8]
    ctrl_widths = [3, 5, 7]
    data_widths = [8]
    depths = [6]
    modes = ['fifo_mux', 'fifo_flop']
    wr_clk_periods = [10]
    rd_clk_periods = [10]

    addr_widths = [4]  # You can add more address widths if needed
    ctrl_widths = [5]
    # modes = ['fifo_mux']
    return list(product(addr_widths, ctrl_widths, data_widths, depths, wr_clk_periods, rd_clk_periods, modes))

params = generate_width_depth_clk_params()

@pytest.mark.parametrize("addr_width, ctrl_width, data_width, depth, wr_clk_period, rd_clk_period, mode", params)
def test_fifo_buffer_mulit(request, addr_width, ctrl_width, data_width, depth, wr_clk_period, rd_clk_period, mode):

    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn': 'rtl/common',
            'rtl_cmn_test': 'rtl/common/testcode'
        }
    )

    # set up all of the test names
    dut_name = "fifo_sync_multi"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_cmn_test'], f"{dut_name}.sv"),
    ]

    # create a human readable test identifier
    aw_str = TBBase.format_dec(addr_width, 3)
    cw_str = TBBase.format_dec(ctrl_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    wcl_str = TBBase.format_dec(wr_clk_period, 3)
    rcl_str = TBBase.format_dec(rd_clk_period, 3)
    test_name_plus_params = f"test_fifo_buffer_multi_aw{aw_str}_cw{cw_str}_dw{dw_str}_d{d_str}_wcl{wcl_str}_rcl{rcl_str}_{mode}"
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
    rtl_parameters = {
        'ADDR_WIDTH': str(addr_width),
        'CTRL_WIDTH': str(ctrl_width),
        'DATA_WIDTH': str(data_width),
        'DEPTH': str(depth),
    }

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

    # Add test parameters; these are passed to the environment, but not the RTL
    extra_env['TEST_ADDR_WIDTH'] = str(addr_width)
    extra_env['TEST_CTRL_WIDTH'] = str(ctrl_width)
    extra_env['TEST_DATA_WIDTH'] = str(data_width)
    extra_env['TEST_DEPTH'] = str(depth)
    extra_env['TEST_CLK_WR'] = str(wr_clk_period)
    extra_env['TEST_CLK_RD'] = str(rd_clk_period)
    extra_env['TEST_MODE'] = mode


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