"""
Main Testbench for AXI4 Slave Read functionality

This module provides the top-level testbench for the AXI4
read slave module with support for FIFO-based error detection.
"""
import os
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

from CocoTBFramework.components.memory_model import MemoryModel
from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd

# Import our interface and test classes
from CocoTBFramework.tbclasses.axi4.axi4_slave_rd_mst_intf import Axi4SlaveRdMasterIntf
from CocoTBFramework.tbclasses.axi4.axi4_slave_rd_usr_intf import Axi4SlaveRdMemIntf
from CocoTBFramework.tbclasses.axi4.axi4_slave_rd_test import Axi4SlaveRdTests


class AXI4SlaveRDTB(TBBase):
    """
    Top-level testbench for AXI4 Slave Read module with FIFO-based error reporting
    """
    def __init__(self, dut):
        super().__init__(dut)

        # Extract parameters from environment or use defaults
        self.ID_WIDTH = self.convert_to_int(os.environ.get('TEST_ID_WIDTH', '8'))
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.USER_WIDTH = self.convert_to_int(os.environ.get('TEST_USER_WIDTH', '1'))
        self.SKID_DEPTH_AR = self.convert_to_int(os.environ.get('TEST_SKID_DEPTH_AR', '2'))
        self.SKID_DEPTH_R = self.convert_to_int(os.environ.get('TEST_SKID_DEPTH_R', '4'))
        self.TIMEOUT_AR = self.convert_to_int(os.environ.get('TEST_TIMEOUT_AR', '32'))
        self.TIMEOUT_R = self.convert_to_int(os.environ.get('TEST_TIMEOUT_R', '32'))
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
        self.master_intf = Axi4SlaveRdMasterIntf(dut)
        self.mem_intf = Axi4SlaveRdMemIntf(dut, self.mem)

        # Create test implementation
        self.tests = Axi4SlaveRdTests(dut, self.master_intf, self.mem_intf)

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

            # Test 1: Basic read transactions
            self.log.info('# Test 1: Basic read transactions')
            result = await self.tests.test_01_basic_read()
            test_results.append(("Basic read transactions", result))

            # Wait longer between tests to ensure full cleanup
            await self.wait_clocks('aclk', 50)

            # # Test 2: Concurrent reads with different IDs
            # self.log.info('# Test 2: Concurrent reads with different IDs')
            # result = await self.tests.test_02_concurrent_reads()
            # test_results.append(("Concurrent reads", result))

            # # Wait longer between tests
            # await self.wait_clocks('aclk', 50)

            # # Test 3: Error response handling
            # self.log.info('# Test 3: Error response handling')
            # result = await self.tests.test_03_error_response()
            # test_results.append(("Error response handling", result))

            # # Wait longer between tests
            # await self.wait_clocks('aclk', 50)

            # # Test 4: Timeout handling
            # self.log.info('# Test 4: Timeout handling')
            # result = await self.tests.test_04_timeout_handling()
            # test_results.append(("Timeout handling", result))

            # # Wait longer between tests
            # await self.wait_clocks('aclk', 50)

            # # Test 5: Performance with back-to-back transactions
            # self.log.info('# Test 5: Performance test')
            # result = await self.tests.test_05_performance()
            # test_results.append(("Performance", result))

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
                print("AXI4 Slave Read test completed successfully!")
            else:
                self.log.error("One or more tests failed!")
                print("AXI4 Slave Read test had failures!")
                for test_name, passed in test_results:
                    if not passed:
                        print(f"  Failed test: {test_name}")
                # Make the test fail in pytest by raising an exception
                assert False, "One or more tests failed - see log for details"

        finally:
            # Ensure cleanup
            self.log.info("Test complete, performing cleanup")

            # Wait for tasks to complete
            await self.wait_clocks('aclk', 10)


@cocotb.test(timeout_time=5000, timeout_unit="us")
async def axi_slave_rd_test(dut):
    """Main test for AXI4 Slave Read module"""
    # Create testbench
    tb = AXI4SlaveRDTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)

    # Run the test sequence
    await tb.run_test()


@pytest.mark.parametrize(
    "id_width, addr_width, data_width, user_width, skid_depth_ar, skid_depth_r, error_fifo_depth, timeout_ar, timeout_r",
    [
        (
            8,   # id_width
            32,  # addr_width
            32,  # data_width
            1,   # user_width
            2,   # skid_depth_ar
            4,   # skid_depth_r
            4,   # error_fifo_depth
            32,  # AR Timeout clocks
            32,  # R Timeout clocks
        )
    ]
)
def test_axi4_slave_rd(request, id_width, addr_width, data_width, user_width,
                      skid_depth_ar, skid_depth_r, error_fifo_depth,
                      timeout_ar, timeout_r):
    """
    Run the test using pytest and cocotb.
    """
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_axi': 'rtl/axi'})

    dut_name = "axi_slave_rd"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_axi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_axi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axi'], "axi_slave_rd_errmon.sv"),
        os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv")
    ]

    # Create a human readable test identifier
    id_str = TBBase.format_dec(id_width, 2)
    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    uw_str = TBBase.format_dec(user_width, 1)
    ar_str = TBBase.format_dec(skid_depth_ar, 1)
    r_str = TBBase.format_dec(skid_depth_r, 1)
    er_str = TBBase.format_dec(error_fifo_depth, 1)
    to_ar_str = TBBase.format_dec(timeout_ar, 2)
    to_r_str = TBBase.format_dec(timeout_r, 2)

    test_name_plus_params = f"test_{dut_name}_id{id_str}_aw{aw_str}_dw{dw_str}_uw{uw_str}_ar{ar_str}_r{r_str}_er{er_str}_to_ar{to_ar_str}_to_r{to_r_str}"
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
        "SKID_DEPTH_AR": str(skid_depth_ar),
        "SKID_DEPTH_R": str(skid_depth_r),
        "TIMEOUT_AR": str(timeout_ar),
        "TIMEOUT_R": str(timeout_r),
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
    extra_env['TEST_SKID_DEPTH_AR'] = str(skid_depth_ar)
    extra_env['TEST_SKID_DEPTH_R'] = str(skid_depth_r)
    extra_env['TEST_TIMEOUT_AR'] = str(timeout_ar)
    extra_env['TEST_TIMEOUT_R'] = str(timeout_r)
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