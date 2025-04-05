"""
Test file for gaxi_data_collect module
"""
import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.gaxi.gaxi_data_collect_tb import DataCollectTB


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def gaxi_data_collect_simple_test(dut):
    """Run a simple test with equal weights on all channels"""
    tb = DataCollectTB(dut)

    # Use a fixed seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    # Start clock
    await tb.start_clock('i_axi_aclk', 10, 'ns')

    # Set moderate randomizer behavior
    delay = 'fixed'
    tb.set_master_randomizers(delay, delay, delay, delay)
    tb.set_slave_randomizer(delay)

    # Run simple test with equal weights
    await tb.run_simple_test(packets_per_channel=40, expected_outputs=10)

    # Add a delay to ensure all transactions complete
    await tb.wait_clocks('i_axi_aclk', 100)

    # Final check
    assert tb.total_errors == 0, f"Test found {tb.total_errors} errors"
    tb.log.info("Simple test passed!")


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def gaxi_data_collect_weighted_arbiter_test(dut):
    """Test different weight configurations for the arbiter"""
    tb = DataCollectTB(dut)

    # Use a fixed seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    # Start clock
    await tb.start_clock('i_axi_aclk', 10, 'ns')

    # Run weighted arbiter tests
    result = await tb.run_weighted_arbiter_test()

    # Add a delay to ensure all transactions complete
    await tb.wait_clocks('i_axi_aclk', 100)

    # Final check
    assert result, "Weighted arbiter test failed"
    tb.log.info("Weighted arbiter test passed!")


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def gaxi_data_collect_stress_test(dut):
    """Run a stress test with high throughput"""
    tb = DataCollectTB(dut)

    # Use a fixed seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    # Start clock
    await tb.start_clock('i_axi_aclk', 10, 'ns')

    # Run stress test with fast randomizers
    result = await tb.run_stress_test(duration_clocks=5000)

    # Add a delay to ensure all transactions complete
    await tb.wait_clocks('i_axi_aclk', 100)

    # Final check
    assert result, "Stress test failed"
    tb.log.info("Stress test passed!")


def generate_test_params():
    """Generate parameters for different test configurations"""
    data_widths = [8]
    id_widths = [8]
    fifo_depths = [8]
    # fifo_depths = [8, 16, 32]
    return list(product(data_widths, id_widths, fifo_depths))


params = generate_test_params()


@pytest.mark.parametrize("data_width, id_width, fifo_depth", params)
def test_gaxi_data_collect(request, data_width, id_width, fifo_depth):
    """Run the full test suite with different parameters"""
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_axi': 'rtl/axi',
        'rtl_intaxi': 'rtl/integ_axi',
    })

    # Set up test names
    dut_name = "gaxi_data_collect"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_round_robin_weighted_fixed_priority.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_round_robin_weighted_subinst.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_round_robin_weighted.sv"),

        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_axi'], "gaxi_fifo_sync.sv"),

        os.path.join(rtl_dict['rtl_axi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_intaxi'], f"{dut_name}.sv"),
    ]

    # Create a human-readable test identifier
    dw_str = TBBase.format_dec(data_width, 2)
    idw_str = TBBase.format_dec(id_width, 2)
    fifo_str = TBBase.format_dec(fifo_depth, 2)
    test_name_plus_params = f"test_{dut_name}_dw{dw_str}_idw{idw_str}_fifo{fifo_str}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters
    rtl_parameters = {
        'DATA_WIDTH': str(data_width),
        'ID_WIDTH': str(id_width),
        'OUTPUT_FIFO_DEPTH': str(fifo_depth),
    }

    # Environment variables
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        # 'SEED': str(random.randint(0, 100000)),
        'SEED': str(0x4739),
        'DATA_WIDTH': str(data_width),
        'ID_WIDTH': str(id_width),
        'OUTPUT_FIFO_DEPTH': str(fifo_depth),
    }

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
