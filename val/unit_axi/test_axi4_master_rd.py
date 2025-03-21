"""
Main Testbench for AXI4 Master Read with Splitting functionality

This module provides the top-level testbench for the AXI4
read master module with support for burst splitting and error detection.
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

from CocoTBFramework.tbclasses.axi_master_rd_ctrl import AXI4MasterRDCtrl
from CocoTBFramework.tbclasses.axi_master_rd_test import AXI4MasterRDTests


class AXI4MasterRDTB(TBBase):
    """
    Top-level testbench for AXI4 Master Read with Splitting functionality
    """
    def __init__(self, dut):
        super().__init__(dut)

        # Extract parameters from environment or use defaults
        self.ID_WIDTH = self.convert_to_int(os.environ.get('TEST_ID_WIDTH', '8'))
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.USER_WIDTH = self.convert_to_int(os.environ.get('TEST_USER_WIDTH', '1'))
        self.ALIGNMENT_WIDTH = self.convert_to_int(os.environ.get('TEST_ALIGNMENT_WIDTH', '12'))
        self.SKID_DEPTH_AR = self.convert_to_int(os.environ.get('TEST_SKID_DEPTH_AR', '2'))
        self.SKID_DEPTH_R = self.convert_to_int(os.environ.get('TEST_SKID_DEPTH_R', '4'))
        self.TIMEOUT_AR = self.convert_to_int(os.environ.get('TEST_TIMEOUT_AR', '1000'))
        self.TIMEOUT_R = self.convert_to_int(os.environ.get('TEST_TIMEOUT_R', '1000'))

        # Calculate derived parameters
        self.STRB_WIDTH = self.DATA_WIDTH // 8

        # Test configuration
        self.memory_size = 32768  # Number of lines in memory model
        self.alignment_boundary = self.ALIGNMENT_WIDTH  # Alignment boundary

        # Create memory model
        self.mem = MemoryModel(
            num_lines=self.memory_size,
            bytes_per_line=self.STRB_WIDTH,
            log=self.log
        )

        # Create controller for signal driving and verification
        self.ctrl = AXI4MasterRDCtrl(dut)
        self.ctrl.tb = self  # Give the controller a reference to this TB
        
        # Create test implementations
        self.tests = AXI4MasterRDTests(self, self.ctrl)

        # Initialize memory with pattern data
        self.ctrl.initialize_memory(self.mem, self.memory_size, self.STRB_WIDTH)

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
            await self.ctrl.reset_dut(self.alignment_boundary)
            
            # Start the AR and R handlers
            await self.ctrl.start_ar_handler()
            await self.ctrl.start_r_handler()
            
            # Wait for handlers to stabilize
            await self.wait_clocks('aclk', 20)

            # Test 1: Basic read transactions
            self.log.info('# Test 1: Basic read transactions')
            result = await self.tests.basic_read_test()
            test_results.append(("Basic read transactions", result))
            
            # Wait longer between tests to ensure full cleanup
            await self.wait_clocks('aclk', 50)
            
            # Reset the controller state between tests
            self.ctrl.pending_reads.clear()
            self.ctrl.completed_reads.clear()
            
            # Test 2: Alignment boundary splitting
            self.log.info('# Test 2: Alignment boundary splitting')
            result = await self.tests.alignment_split_test()
            test_results.append(("Alignment boundary splitting", result))
            
            # Wait longer between tests
            await self.wait_clocks('aclk', 50)
            
            # Reset the controller state between tests
            self.ctrl.pending_reads.clear()
            self.ctrl.completed_reads.clear()
            
            # Test 3: Error handling
            self.log.info('# Test 3: Error handling')
            result = await self.tests.error_handling_test()
            test_results.append(("Error handling", result))
            
            # Wait longer between tests
            await self.wait_clocks('aclk', 50)
            
            # Reset the controller state between tests
            self.ctrl.pending_reads.clear()
            self.ctrl.completed_reads.clear()
            
            # Test 4: Performance metrics
            self.log.info('# Test 4: Performance metrics')
            result = await self.tests.performance_test()
            test_results.append(("Performance metrics", result))
            
            # Wait longer between tests
            await self.wait_clocks('aclk', 50)
            
            # Final verification
            result = await self.tests.verify_scoreboard()
            test_results.append(("Final verification", result))
            
            await self.wait_clocks('aclk', 50)

            # Print test summary
            self.log.info("=== Test Summary ===")
            all_passed = True
            for test_name, passed in test_results:
                status = "PASSED" if passed else "FAILED"
                self.log.info(f"  {test_name}: {status}")
                all_passed = all_passed and passed

            if all_passed:
                self.log.info("All tests passed!")
                print("AXI4 Master Read test completed successfully!")
            else:
                self.log.error("One or more tests failed!")
                print("AXI4 Master Read test had failures!")
                for test_name, passed in test_results:
                    if not passed:
                        print(f"  Failed test: {test_name}")
                # Make the test fail in pytest by raising an exception
                assert False, "One or more tests failed - see log for details"

        finally:
            # Set done flag to terminate all handlers
            self.ctrl.done = True
            
            # Wait for tasks to complete
            await self.wait_clocks('aclk', 10)


@cocotb.test(timeout_time=5000, timeout_unit="us")
async def axi_master_rd_test(dut):
    """Main test for AXI4 Master Read with Splitting module"""
    # Create testbench
    tb = AXI4MasterRDTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)

    # Run the test sequence
    await tb.run_test()


@pytest.mark.parametrize(
    "id_width, addr_width, data_width, user_width, alignment_width, skid_depth_ar, skid_depth_r",
    [
        (
            8,   # id_width
            32,  # addr_width
            32,  # data_width
            1,   # user_width
            12,  # alignment_width (4KB boundary)
            2,   # skid_depth_ar
            4,   # skid_depth_r
        )
    ]
)
def test_axi4_master_rd(request, id_width, addr_width, data_width, user_width, alignment_width, skid_depth_ar, skid_depth_r):
    """
    Run the test using pytest and cocotb.
    """
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_axi': 'rtl/axi'})

    dut_name = "axi_master_rd"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_axi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axi'], "axi_master_rd_splitter.sv"),
        os.path.join(rtl_dict['rtl_axi'], "axi_rd_error_monitor.sv"),
        os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv")
    ]

    # Create a human readable test identifier
    id_str = TBBase.format_dec(id_width, 2)
    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    uw_str = TBBase.format_dec(user_width, 1)
    al_str = TBBase.format_dec(alignment_width, 2)
    ar_str = TBBase.format_dec(skid_depth_ar, 1)
    r_str = TBBase.format_dec(skid_depth_r, 1)

    test_name_plus_params = f"test_{dut_name}_id{id_str}_aw{aw_str}_dw{dw_str}_uw{uw_str}_al{al_str}_ar{ar_str}_r{r_str}"
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
        "ALIGNMENT_WIDTH": str(alignment_width),
        "TIMEOUT_AR": "1000",
        "TIMEOUT_R": "1000",
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
    extra_env['TEST_ALIGNMENT_WIDTH'] = str(alignment_width)
    extra_env['TEST_SKID_DEPTH_AR'] = str(skid_depth_ar)
    extra_env['TEST_SKID_DEPTH_R'] = str(skid_depth_r)
    extra_env['TEST_TIMEOUT_AR'] = "1000"
    extra_env['TEST_TIMEOUT_R'] = "1000"

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
