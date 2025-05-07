"""
Scenario-based test for AXI4 Master Read module

This test implements multiple test scenarios for the AXI4 Master Read module:
- basic: Simple read transactions
- splits: Transaction splitting with different alignment masks
- error: Error detection and reporting
- full: Comprehensive test of all features

The test uses a single entry point with parameters to select the test type.
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb.triggers import Timer

from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.axi4.axi4_master_rd_tb import AXI4MasterReadTB
from CocoTBFramework.components.axi4.axi4_seq_transaction import AXI4TransactionSequence
from CocoTBFramework.components.axi4.axi4_seq_protocol import AXI4ProtocolSequence
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.randomization_config import RandomizationMode
from CocoTBFramework.tbclasses.axi4.axi4_random_configs import RANDOMIZER_CONFIGS


class AXI4MasterReadScenarioTB:
    """Test bench for running different test scenarios on AXI4 Master Read module"""

    def __init__(self, dut):
        """Initialize the scenario testbench"""
        self.dut = dut
        self.test_type = os.environ.get('TEST_TYPE', 'basic')

        # Create the base testbench
        self.tb = AXI4MasterReadTB(
            dut=dut,
            id_width=int(dut.AXI_ID_WIDTH.value),
            addr_width=int(dut.AXI_ADDR_WIDTH.value),
            data_width=int(dut.AXI_DATA_WIDTH.value),
            user_width=int(dut.AXI_USER_WIDTH.value),
            channels=int(dut.CHANNELS.value),
            error_fifo_depth=int(dut.ERROR_FIFO_DEPTH),
            skid_depth_ar=int(dut.SKID_DEPTH_AR),
            skid_depth_r=int(dut.SKID_DEPTH_R),
            alignment_mask=0xFFF  # Start with 4K boundary
        )

        # Note: The TB creates default randomizers during initialization
        # We'll override them in our test methods as needed for specific timing behavior

        # Setup logging
        self.log = self.tb.log
        self.log.info(f"Created AXI4MasterReadScenarioTB with test_type: {self.test_type}")

        # Use seed for reproducibility
        self.seed = int(os.environ.get('SEED', '0'))
        random.seed(self.seed)
        self.log.info(f"Using seed: {self.seed}")

    async def setup(self):
        """Setup the testbench"""
        await self.tb.start_clock('aclk', 10, 'ns')
        await self.tb.setup_components()
        await self.tb.reset_dut()
        await self.tb.start_components()

    async def cleanup(self):
        """Cleanup after tests"""
        await self.tb.stop_components()
        self.tb.log_summary()

    async def run_basic_test(self):
        """Run basic functionality tests without transaction splitting"""
        self.log.info("Running basic functionality test")

        # Test 1: Single-beat read transactions
        self.log.info("Test 1: Single-beat read transactions")
        for i in range(5):
            addr = i * 0x100  # Space out addresses
            result = await self.tb.perform_read(addr=addr, id_value=i)
            await self.tb.verify_read_data(result, addr)
            await self.tb.wait_clocks('aclk', 5)  # Wait between transactions

        # Test 2: Burst read transactions
        self.log.info("Test 2: Burst read transactions")
        for i, burst_len in enumerate([1, 3, 7]):  # 2, 4, 8 beats
            addr = 0x1000 + (i * 0x100)  # Ensure no boundary crossing
            result = await self.tb.perform_read(addr=addr, id_value=10+i, burst_len=burst_len)
            await self.tb.verify_read_data(result, addr, burst_len)
            await self.tb.wait_clocks('aclk', 10)  # Longer wait for burst transactions

        # Test 3: Different burst sizes
        self.log.info("Test 3: Different burst sizes")
        for i, burst_size in enumerate([0, 1, 2]):  # 1, 2, 4 bytes
            addr = 0x2000 + (i * 0x100)
            result = await self.tb.perform_read(addr=addr, id_value=20+i, burst_size=burst_size)
            await self.tb.verify_read_data(result, addr, burst_size=burst_size)
            await self.tb.wait_clocks('aclk', 5)

        return self.tb.get_test_result()

    async def run_clock_gating_test(self):
        """Run clock gating functionality tests"""
        self.log.info("Running clock gating test")

        # Check if DUT supports clock gating
        if not self.tb.has_cg_support():
            self.log.warning("DUT does not support clock gating, skipping test")
            return True

        # Run the comprehensive clock gating tests
        return await self.tb.run_clock_gating_tests()

    async def run_split_test(self):
        """Run transaction splitting tests with different alignment masks"""
        self.log.info("Running transaction splitting test")

        # Test with different alignment masks
        alignment_masks = [
            0xFFF,  # 4K boundary (default)
            0x7FF,  # 2K boundary
            0x3FF,  # 1K boundary
            0x1FF,  # 512-byte boundary
        ]

        # Manual tests for specific boundary cases
        for mask in alignment_masks:
            # Set alignment mask
            await self.tb.set_alignment_mask(mask)
            boundary = mask + 1

            self.log.info(f"Testing with alignment mask: 0x{mask:X}")

            # Test 1: Transaction directly before boundary
            addr = boundary - 16  # Place just before boundary
            burst_len = 7  # 8 beats

            # Execute the read
            result = await self.tb.perform_read(addr=addr, id_value=0, burst_len=burst_len)

            # Verify split and data
            expected_splits = self.tb.calculate_expected_splits(addr, burst_len, 2)
            await self.tb.verify_split_transaction(result, addr, 0, burst_len, 2, expected_splits)

            # Test 2: Transaction spanning multiple boundaries
            addr = boundary - 32
            burst_len = 15  # 16 beats (spans multiple boundaries)

            # Execute the read
            result = await self.tb.perform_read(addr=addr, id_value=1, burst_len=burst_len)

            # Verify split and data
            expected_splits = self.tb.calculate_expected_splits(addr, burst_len, 2)
            await self.tb.verify_split_transaction(result, addr, 1, burst_len, 2, expected_splits)

            # Wait between masks
            await self.tb.wait_clocks('aclk', 20)
            await self.tb.axi_slave.debug_dump_state()

        # Run the comprehensive boundary test with multiple pages
        page_addresses = [0, 0x10000, 0x20000]  # Test multiple pages
        await self.tb.run_boundary_test_sequence(masks=alignment_masks, page_addresses=page_addresses)

        # Return the test result
        return self.tb.get_test_result()

    async def run_error_test(self):
        """Run error detection and reporting tests with address verification"""
        self.log.info("Running error detection and address verification test")

        return await self.tb.run_error_monitor_tests()

    async def run_full_test(self):
        """Run comprehensive test of all features"""
        self.log.info("Running comprehensive test")
        await self.tb.configure_slave_response_order(inorder=True)

        # Part 1: Basic functionality
        self.log.info("Part 1: Basic functionality")
        basic_result = await self.run_basic_test()

        # Reset before next test
        await self.tb.reset_dut()
        await self.tb.start_components()

        # Part 2: Clock Gating
        self.log.info("Part 2: Clock Gating")
        cg_result = await self.run_clock_gating_test()

        # Reset before next test
        await self.tb.reset_dut()
        await self.tb.start_components()

        # Part 3: Transaction splitting
        self.log.info("Part 3: Transaction splitting")
        split_result = await self.run_split_test()

        # Reset before next test
        await self.tb.reset_dut()
        await self.tb.start_components()

        # Part 4: Error detection
        self.log.info("Part 4: Error detection")
        error_result = await self.run_error_test()

        # Reset before next test
        await self.tb.reset_dut()
        await self.tb.start_components()

        # Part 5: Out-of-order response handling
        self.log.info("Part 5: Out-of-order response handling")

        # Toggle to out-of-order responses
        await self.tb.configure_slave_response_order(inorder=False)

        # Create sequence with multiple IDs
        ooo_sequence = AXI4TransactionSequence(
            name="multi_id_sequence",
            id_width=self.tb.id_width,
            addr_width=self.tb.addr_width,
            data_width=self.tb.data_width
        )

        # Add reads with different IDs
        for i in range(8):
            addr = 0x2000 + (i * 0x40)
            ooo_sequence.add_read_transaction(
                addr=addr,
                id_value=i,
                burst_len=3  # 4 beats
            )

        # Run the sequence
        await self.tb.run_transaction_sequence(ooo_sequence)
        ooo_result = self.tb.get_test_result()

        # Part 5: Randomized testing
        self.log.info("Part 5: Randomized testing")

        # Create and run random transactions with different delay profiles
        delay_profiles = ['constrained', 'burst_pause', 'slow_consumer']
        for profile in delay_profiles:
            # Set randomizers for each channel
            # FUB master side (AR master, R slave)
            self.tb.fub_master.ar_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[profile]['write']))
            self.tb.fub_master.r_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[profile]['read']))
            # AXI slave side (AR slave, R master)
            self.tb.axi_slave.ar_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[profile]['read']))
            self.tb.axi_slave.r_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[profile]['write']))

            # Create random sequence
            rand_sequence = AXI4TransactionSequence.create_random_transactions(
                count=10,
                addr_range=(0x1000, 0x8FFF),
                id_range=(0, 7),
                data_width=self.tb.data_width,
                randomization_config=None
            )

            # Run sequence
            await self.tb.run_transaction_sequence(rand_sequence)
            await self.tb.wait_clocks('aclk', 30)

        random_result = self.tb.get_test_result()

        # Check all results
        return basic_result and cg_result and split_result and error_result and ooo_result and random_result

    async def run_selected_test(self):
        """Run the selected test type"""
        test_result = False

        if self.test_type == 'basic':
            return await self.run_basic_test()
        elif self.test_type == 'clock_gating':
            return await self.run_clock_gating_test()
        elif self.test_type == 'splits':
            return await self.run_split_test()
        elif self.test_type == 'error':
            return await self.run_error_test()
        elif self.test_type == 'full':
            return await self.run_full_test()
        else:
            self.log.error(f"Unknown test type: {self.test_type}")
            return False


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def axi4_master_read_scenario_test(dut):
    """Main entry point for scenario-based AXI4 Master Read tests"""
    # Create the scenario testbench
    scenario_tb = AXI4MasterReadScenarioTB(dut)

    # Setup the testbench
    await scenario_tb.setup()

    try:
        # Run the selected test
        result = await scenario_tb.run_selected_test()

        # Check result
        if result:
            scenario_tb.log.info("TEST PASSED")
        else:
            scenario_tb.log.error("TEST FAILED")
            assert False, "Test failed"

    finally:
        # Always cleanup
        await scenario_tb.cleanup()


def generate_params():
    """Generate test parameters"""
    clk_period_ns = [10]
    use_cg = [False, True]
    CG_IDLE_COUNT_WIDTH = [8]
    channels = [32]
    id_widths = [8]
    addr_widths = [32]
    data_widths = [32, 64]
    user_widths = [1]
    skid_depths = [2, 4]
    fifo_depths = [4]
    test_types = ['basic', 'clock_gating', 'splits', 'error', 'full']

    # use_cg = [False]
    data_widths = [32]
    # skid_depths = [4]
    # test_types = ['error']
    test_types = ['full']

    return list(product(
        clk_period_ns,
        use_cg,
        CG_IDLE_COUNT_WIDTH,
        channels,
        id_widths,
        addr_widths,
        data_widths,
        user_widths,
        skid_depths,
        fifo_depths,
        test_types
    ))

params = generate_params()

@pytest.mark.parametrize(
    "clk_period_ns, use_cg, CG_IDLE_COUNT_WIDTH, channels, id_width, addr_width, data_width, user_width, skid_depth, fifo_depth, test_type",
    params
)
def test_axi_master_read(request, clk_period_ns, use_cg, CG_IDLE_COUNT_WIDTH, channels, id_width, addr_width, data_width, user_width,
                            skid_depth, fifo_depth, test_type):
    """Main test function for AXI Master Read module"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn':  'rtl/common',
            'rtl_amba': 'rtl/amba',
        }
    )

    # Set up all of the test names
    post = '_cg' if use_cg else ''
    dut_name = f"axi_master_rd{post}"
    toplevel = dut_name

    verilog_sources_pre = [
        os.path.join(rtl_dict['rtl_cmn'],  "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "counter_freq_invariant.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_amba'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axi_errmon_base.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axi_master_rd_splitter.sv"),
        os.path.join(rtl_dict['rtl_amba'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba'], f"{dut_name}.sv"),
    ]
    verilog_sources_cg = [
        os.path.join(rtl_dict['rtl_cmn'],  "icg.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "clock_gate_ctrl.sv"),
        os.path.join(rtl_dict['rtl_amba'], "amba_clock_gate_ctrl.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axi_master_rd.sv"),
    ]

    # sourcery skip: no-conditionals-in-tests
    if use_cg:
        verilog_sources = verilog_sources_pre + verilog_sources_cg
    else:
        verilog_sources = verilog_sources_pre

    # Create a human readable test identifier
    t_clk = clk_period_ns
    ch_str = format(channels, '02d')
    id_str = format(id_width, '02d')
    addr_str = format(addr_width, '02d')
    data_str = format(data_width, '02d')
    user_str = format(user_width, '02d')
    skid_str = format(skid_depth, '02d')
    fifo_str = format(fifo_depth, '02d')
    test_type_str = f"{test_type}"

    test_name_plus_params = f"test_{dut_name}_clk{t_clk}_ch{ch_str}_id{id_str}_a{addr_str}_d{data_str}_u{user_str}_s{skid_str}_f{fifo_str}_{test_type_str}"
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
        'UNIT_ID': str(99),
        'AGENT_ID': str(99),
        'CHANNELS': str(channels),
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': str(user_width),
        'SKID_DEPTH_AR': str(skid_depth),
        'SKID_DEPTH_R': str(skid_depth),
        'SPLIT_FIFO_DEPTH': str(fifo_depth),
        'ERROR_FIFO_DEPTH': str(fifo_depth)
    }

    # sourcery skip: no-conditionals-in-tests
    if use_cg:
        rtl_parameters['CG_IDLE_COUNT_WIDTH'] = str(CG_IDLE_COUNT_WIDTH)

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        # 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(0x434749), # str(random.randint(0, 100000)),
        'TEST_TYPE': test_type,
        'CLK_PERIOD_NS': str(t_clk)
    }

    # Calculate timeout based on clock period
    timeout_factor = max(1.0, t_clk / 10) * 50
    extra_env['COCOTB_TIMEOUT_MULTIPLIER'] = str(timeout_factor)

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
        from cocotb_test.simulator import run
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