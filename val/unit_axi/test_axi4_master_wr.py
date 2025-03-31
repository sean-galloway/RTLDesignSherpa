"""
Main Testbench for AXI4 Master Write with Splitting functionality

This module provides the top-level testbench for the AXI4
write master module with support for burst splitting and FIFO-based error detection.
"""
import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.components.memory_model import MemoryModel
from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd

# Import our interface and test classes
from CocoTBFramework.tbclasses.axi4.axi4_master_wr_usr_intf import Axi4MasterWrUserIntf
from CocoTBFramework.tbclasses.axi4.axi4_master_wr_slv_intf import Axi4MasterWrAxi4Intf
from CocoTBFramework.tbclasses.axi4.axi4_master_wr_test import Axi4MasterWrTests


class AXI4MasterWRTB(TBBase):
    """
    Top-level testbench for AXI4 Master Write with Splitting functionality and FIFO-based error reporting
    """
    def __init__(self, dut):
        super().__init__(dut)

        # Extract parameters from environment or use defaults
        self.ID_WIDTH = self.convert_to_int(os.environ.get('TEST_ID_WIDTH', '8'))
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.USER_WIDTH = self.convert_to_int(os.environ.get('TEST_USER_WIDTH', '1'))
        self.ALIGNMENT_WIDTH = self.convert_to_int(os.environ.get('TEST_ALIGNMENT_WIDTH', '12'))
        self.SKID_DEPTH_AW = self.convert_to_int(os.environ.get('TEST_SKID_DEPTH_AW', '2'))
        self.SKID_DEPTH_W = self.convert_to_int(os.environ.get('TEST_SKID_DEPTH_W', '4'))
        self.SKID_DEPTH_B = self.convert_to_int(os.environ.get('TEST_SKID_DEPTH_B', '2'))
        self.TIMEOUT_AW = self.convert_to_int(os.environ.get('TEST_TIMEOUT_AW', '32'))
        self.TIMEOUT_W = self.convert_to_int(os.environ.get('TEST_TIMEOUT_W', '32'))
        self.TIMEOUT_B = self.convert_to_int(os.environ.get('TEST_TIMEOUT_B', '32'))
        self.ERROR_FIFO_DEPTH = self.convert_to_int(os.environ.get('TEST_ERROR_FIFO_DEPTH', '4'))

        # Calculate derived parameters
        self.STRB_WIDTH = self.DATA_WIDTH // 8

        # Test configuration
        self.memory_size = 32768  # Number of lines in memory model

        # Create memory model
        self.mem = MemoryModel(
            num_lines=self.memory_size,
            bytes_per_line=self.STRB_WIDTH,
            log=self.log
        )

        # Initialize memory with pattern data
        self._initialize_memory()

        # Create interface classes
        self.user_intf = Axi4MasterWrUserIntf(dut)
        self.axi4_intf = Axi4MasterWrAxi4Intf(dut, self.mem)

        # Create test implementation
        self.tests = Axi4MasterWrTests(dut, self.user_intf, self.axi4_intf)

    def _initialize_memory(self):
        """Initialize memory with a pattern."""
        # Use a simple pattern: address + 0xA5A5A5A5
        for addr in range(0, self.memory_size * self.STRB_WIDTH, self.STRB_WIDTH):
            value = (addr + 0xA5A5A5A5) & ((1 << (8 * self.STRB_WIDTH)) - 1)
            data_bytes = self.mem.integer_to_bytearray(value, self.STRB_WIDTH)
            self.mem.write(addr, data_bytes, 0xFF)  # All bytes enabled

        self.log.info(f"Memory initialized with pattern: addr + 0xA5A5A5A5")

    async def run_test(self):
        """Main test sequence"""
        # Keep track of test results
        test_results = []

        try:
            # Start the clock
            self.log.info('Starting clock')
            await self.start_clock('aclk', 10, 'ns')

            # Reset the DUT
            self.log.info('Resetting DUT')
            await self.tests.reset_dut()

            # Start the command handler to process write requests
            self.log.info('Starting AXI4 write command handler')
            await self.axi4_intf.start_command_handler()

            # Test 1: Basic write transactions
            self.log.info('# Test 1: Basic write transactions')
            result = await self.tests.test_01_basic_write()
            test_results.append(("Basic write transactions", result))

            # Wait longer between tests to ensure full cleanup
            await self.wait_clocks('aclk', 50)

            # Test 2: Alignment boundary splitting
            self.log.info('# Test 2: Alignment boundary splitting')
            result = await self.tests.test_02_split_test()
            test_results.append(("Alignment boundary splitting", result))

            # Wait longer between tests
            await self.wait_clocks('aclk', 50)

            # # Test 3: Error handling (with FIFO-based reporting)
            # self.log.info('# Test 3: Error handling with FIFO-based reporting')
            # result = await self.tests.test_03_response_error_test()
            # test_results.append(("Response error handling", result))

            # # Wait longer between tests
            # await self.wait_clocks('aclk', 50)

            # # Test 4: AW Timeout Test
            # self.log.info('# Test 4: AW Timeout Test')
            # result = await self.tests.test_04_aw_timeout_test()
            # test_results.append(("AW channel timeout handling", result))

            # # Wait longer between tests
            # await self.wait_clocks('aclk', 50)

            # # Test 5: W Timeout Test
            # self.log.info('# Test 5: W Timeout Test')
            # result = await self.tests.test_05_w_timeout_test()
            # test_results.append(("W channel timeout handling", result))

            # # Wait longer between tests
            # await self.wait_clocks('aclk', 50)

            # # Test 6: B Timeout Test
            # self.log.info('# Test 6: B Timeout Test')
            # result = await self.tests.test_06_b_timeout_test()
            # test_results.append(("B channel timeout handling", result))

            # # Wait longer between tests
            # await self.wait_clocks('aclk', 50)

            # # Test 7: Collision Cases
            # self.log.info('# Test 7: Collision Cases Test')
            # result = await self.tests.test_07_collision_cases()
            # test_results.append(("Error collision cases", result))

            # # Wait longer between tests
            # await self.wait_clocks('aclk', 50)

            # Print test summary
            self.log.info("=== Test Summary ===")
            all_passed = True
            for test_name, passed in test_results:
                status = "PASSED" if passed else "FAILED"
                self.log.info(f"  {test_name}: {status}")
                all_passed = all_passed and passed

            if all_passed:
                self.log.info("All tests passed!")
                print("AXI4 Master Write test completed successfully!")
            else:
                self.log.error("One or more tests failed!")
                print("AXI4 Master Write test had failures!")
                for test_name, passed in test_results:
                    if not passed:
                        print(f"  Failed test: {test_name}")
                # Make the test fail in pytest by raising an exception
                assert False, "One or more tests failed - see log for details"

        finally:
            # Ensure cleanup
            self.log.info("Test complete, performing cleanup")

            # Stop the command handler
            self.log.info('Stopping AXI4 write command handler')
            await self.axi4_intf.stop_command_handler()

            # Wait for tasks to complete
            await self.wait_clocks('aclk', 10)


@cocotb.test(timeout_time=5000, timeout_unit="us")
async def axi4_master_wr_test(dut):
    """Main test for AXI4 Master Write with Splitting module and FIFO-based error reporting"""
    # Create testbench
    tb = AXI4MasterWRTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)

    # Run the test sequence
    await tb.run_test()


@pytest.mark.parametrize(
    "id_width, addr_width, data_width, user_width, skid_depth_aw, skid_depth_w, skid_depth_b, error_fifo_depth, timeout_aw, timeout_w, timeout_b",
    [
        (
            8,   # id_width
            32,  # addr_width
            32,  # data_width
            1,   # user_width
            2,   # skid_depth_aw
            4,   # skid_depth_w
            2,   # skid_depth_b
            4,   # error_fifo_depth
            32,  # AW Timeout clocks
            32,  # W Timeout clocks
            32,  # B Timeout clocks
        ),
        (
            8,   # id_width
            64,  # addr_width
            64,  # data_width
            1,   # user_width
            2,   # skid_depth_aw
            4,   # skid_depth_w
            2,   # skid_depth_b
            4,   # error_fifo_depth
            32,  # AW Timeout clocks
            32,  # W Timeout clocks
            32,  # B Timeout clocks
        ),
        (
            8,   # id_width
            64,  # addr_width
            128, # data_width
            1,   # user_width
            2,   # skid_depth_aw
            4,   # skid_depth_w
            2,   # skid_depth_b
            4,   # error_fifo_depth
            32,  # AW Timeout clocks
            32,  # W Timeout clocks
            32,  # B Timeout clocks
        ),
        (
            8,   # id_width
            64,  # addr_width
            256, # data_width
            1,   # user_width
            2,   # skid_depth_aw
            4,   # skid_depth_w
            2,   # skid_depth_b
            4,   # error_fifo_depth
            32,  # AW Timeout clocks
            32,  # W Timeout clocks
            32,  # B Timeout clocks
        ),
        (
            8,   # id_width
            64,  # addr_width
            512, # data_width
            1,   # user_width
            2,   # skid_depth_aw
            4,   # skid_depth_w
            2,   # skid_depth_b
            4,   # error_fifo_depth
            32,  # AW Timeout clocks
            32,  # W Timeout clocks
            32,  # B Timeout clocks
        ),
    ]
)
def test_axi4_master_wr(request, id_width, addr_width, data_width, user_width,
                        skid_depth_aw, skid_depth_w, skid_depth_b, error_fifo_depth,
                        timeout_aw, timeout_w, timeout_b):
    """
    Run the test using pytest and cocotb.
    """
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_axi': 'rtl/axi'})

    dut_name = "axi_master_wr"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_axi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_axi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axi'], "axi_master_wr_splitter.sv"),
        os.path.join(rtl_dict['rtl_axi'], "axi_master_wr_errmon.sv"),
        os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv")
    ]

    # Create a human readable test identifier
    id_str = TBBase.format_dec(id_width, 2)
    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    uw_str = TBBase.format_dec(user_width, 1)
    al_str = TBBase.format_dec(12, 2)
    aw_skid_str = TBBase.format_dec(skid_depth_aw, 1)
    w_skid_str = TBBase.format_dec(skid_depth_w, 1)
    b_skid_str = TBBase.format_dec(skid_depth_b, 1)
    er_str = TBBase.format_dec(error_fifo_depth, 1)
    to_aw_str = TBBase.format_dec(timeout_aw, 2)
    to_w_str = TBBase.format_dec(timeout_w, 2)
    to_b_str = TBBase.format_dec(timeout_b, 2)

    test_name_plus_params = f"test_{dut_name}_id{id_str}_aw{aw_str}_dw{dw_str}_uw{uw_str}_al{al_str}_aw{aw_skid_str}_w{w_skid_str}_b{b_skid_str}_er{er_str}_to_aw{to_aw_str}_to_w{to_w_str}_to_b{to_b_str}"
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
        "SKID_DEPTH_AW": str(skid_depth_aw),
        "SKID_DEPTH_W": str(skid_depth_w),
        "SKID_DEPTH_B": str(skid_depth_b),
        "TIMEOUT_AW": str(timeout_aw),
        "TIMEOUT_W": str(timeout_w),
        "TIMEOUT_B": str(timeout_b),
        "ERROR_FIFO_DEPTH": str(error_fifo_depth),
        "AXI_ID_WIDTH": str(id_width),
        "AXI_ADDR_WIDTH": str(addr_width),
        "AXI_DATA_WIDTH": str(data_width),
        "AXI_USER_WIDTH": str(user_width)
    }

    # Environment variables
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000))
    }

    # Add test parameters to environment
    extra_env['TEST_ID_WIDTH'] = str(id_width)
    extra_env['TEST_ADDR_WIDTH'] = str(addr_width)
    extra_env['TEST_DATA_WIDTH'] = str(data_width)
    extra_env['TEST_USER_WIDTH'] = str(user_width)
    extra_env['TEST_SKID_DEPTH_AW'] = str(skid_depth_aw)
    extra_env['TEST_SKID_DEPTH_W'] = str(skid_depth_w)
    extra_env['TEST_SKID_DEPTH_B'] = str(skid_depth_b)
    extra_env['TEST_TIMEOUT_AW'] = str(timeout_aw)
    extra_env['TEST_TIMEOUT_W'] = str(timeout_w)
    extra_env['TEST_TIMEOUT_B'] = str(timeout_b)
    extra_env['TEST_ERROR_FIFO_DEPTH'] = str(error_fifo_depth)

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
