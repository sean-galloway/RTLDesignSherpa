import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_multi import GaxiMultiBufferTB
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def skid_buffer_multi_test(dut):
    '''Test the axi_skid_buffer_multi component'''
    tb = GaxiMultiBufferTB(dut, wr_clk=dut.i_axi_aclk, wr_rstn=dut.i_axi_aresetn)

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

    # Run legacy test for backward compatibility
    tb.log.info("Running legacy simple_incremental_loops test...")
    await tb.simple_incremental_loops(count=10, delay_key='fixed', delay_clks_after=20)

    # Run basic sequence test
    tb.log.info("Running basic sequence test...")
    await tb.run_sequence_test(tb.basic_sequence, delay_key='fixed', delay_clks_after=5)

    # Run walking ones pattern test
    tb.log.info("Running walking ones pattern test...")
    await tb.run_sequence_test(tb.walking_ones_sequence, delay_key='constrained', delay_clks_after=5)

    # Run alternating patterns test
    tb.log.info("Running alternating patterns test...")
    await tb.run_sequence_test(tb.alternating_sequence, delay_key='fast', delay_clks_after=5)

    # Run burst sequence test with back-to-back packets
    tb.log.info("Running burst sequence test...")
    await tb.run_sequence_test(tb.burst_sequence, delay_key='backtoback', delay_clks_after=5)

    # Run random data test
    tb.log.info("Running random data test...")
    await tb.run_sequence_test(tb.random_sequence, delay_key='constrained', delay_clks_after=5)

    # Run comprehensive test
    tb.log.info("Running comprehensive test...")
    await tb.run_sequence_test(tb.comprehensive_sequence, delay_key='constrained', delay_clks_after=10)

    # Run stress test with varied delays and patterns
    tb.log.info("Running stress test...")
    await tb.run_sequence_test(tb.stress_sequence, delay_key='burst_pause', delay_clks_after=20)

    # Test with different randomizer configurations
    tb.log.info("Testing with different randomizer configurations...")

    # Test with slow consumer
    tb.log.info("Testing with slow consumer...")
    await tb.run_sequence_test(tb.basic_sequence, delay_key='slow_consumer', delay_clks_after=20)

    # Test with slow producer
    tb.log.info("Testing with slow producer...")
    await tb.run_sequence_test(tb.basic_sequence, delay_key='slow_producer', delay_clks_after=20)

    tb.log.info("All tests completed successfully!")


def generate_params():
    addr_widths = [4, 6, 8]
    ctrl_widths = [3, 5, 7]
    data_widths = [8]
    depths = [2]
    modes = ['skid']  # Skid buffer has only one mode

    return [(6, 3, 8, 2, 'skid')]
    # return list(product(addr_widths, ctrl_widths, data_widths, depths, modes))

params = generate_params()

@pytest.mark.parametrize("addr_width, ctrl_width, data_width, depth, mode", params)
def test_axi_skid_buffer_multi(request, addr_width, ctrl_width, data_width, depth, mode):
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn': 'rtl/common',
            'rtl_amba': 'rtl/amba',
            'rtl_amba_test': 'rtl/amba/testcode',
        })

    # Set up all of the test names
    dut_name = "gaxi_skid_buffer_multi"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba_test'], f"{dut_name}.sv"),
    ]

    # Create a human readable test identifier
    aw_str = TBBase.format_dec(addr_width, 3)
    cw_str = TBBase.format_dec(ctrl_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{dut_name}_aw{aw_str}_cw{cw_str}_dw{dw_str}_d{d_str}"
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

    # Add test parameters
    extra_env['TEST_ADDR_WIDTH'] = str(addr_width)
    extra_env['TEST_CTRL_WIDTH'] = str(ctrl_width)
    extra_env['TEST_DATA_WIDTH'] = str(data_width)
    extra_env['TEST_DEPTH'] = str(depth)
    extra_env['TEST_MODE'] = 'skid'  # Always 'skid' mode for skid buffer


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
