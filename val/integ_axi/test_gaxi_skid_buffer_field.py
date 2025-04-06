import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_field import GaxiFieldBufferTB
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_configs import RANDOMIZER_CONFIGS


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def skid_buffer_field_test(dut):
    '''Test the gaxi_skid_buffer_field component'''
    tb = GaxiFieldBufferTB(dut, wr_clk=dut.i_axi_aclk, wr_rstn=dut.i_axi_aresetn)
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


def generate_params():
    addr_widths = [4, 6, 8]
    ctrl_widths = [3, 5, 7]
    data_widths = [8]
    depths = [2]
    modes = ['skid']  # Skid buffer has only one mode

    addr_widths = [8]  # You can add more address widths if needed
    ctrl_widths = [7]

    return list(product(addr_widths, ctrl_widths, data_widths, depths, modes))

params = generate_params()

# Single test configuration for initial debugging
# @pytest.mark.parametrize("data_width, depth, mode, addr_width", [(8, 2, 'skid', 4)])
@pytest.mark.parametrize("addr_width, ctrl_width, data_width, depth, mode", params)
def test_gaxi_skid_buffer_field(request, addr_width, ctrl_width, data_width, depth, mode):
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_axi': 'rtl/axi'})

    # Set up all of the test names
    dut_name = "gaxi_skid_buffer"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv"),
    ]

    # Create a human readable test identifier
    aw_str = TBBase.format_dec(addr_width, 3)
    cw_str = TBBase.format_dec(ctrl_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{dut_name}_field_aw{aw_str}_cw{cw_str}_dw{dw_str}_d{d_str}_{mode}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters
    rtl_parameters = {
        'DATA_WIDTH': str(addr_width+ctrl_width+data_width+data_width),
        'DEPTH': str(depth),
    }

    # Environment variables
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        # 'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000))
    }

    # Add test parameters
    extra_env['TEST_ADDR_WIDTH'] = str(addr_width)
    extra_env['TEST_CTRL_WIDTH'] = str(ctrl_width)
    extra_env['TEST_DATA_WIDTH'] = str(data_width)
    extra_env['TEST_DEPTH'] = str(depth)
    extra_env['TEST_MODE'] = 'skid'  # Always 'skid' mode for skid buffer

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