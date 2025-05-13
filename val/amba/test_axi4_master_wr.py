"""
Scenario-based test for AXI4 Master Write module

This test implements multiple test scenarios for the AXI4 Master Write module:
- basic: Simple write transactions
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
from CocoTBFramework.tbclasses.axi4.axi4_master_wr_tb import AXI4MasterWriteTB
from CocoTBFramework.components.axi4.axi4_seq_transaction import AXI4TransactionSequence
from CocoTBFramework.components.axi4.axi4_seq_protocol import AXI4ProtocolSequence
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.randomization_config import RandomizationMode
from CocoTBFramework.tbclasses.axi4.axi4_random_configs import RANDOMIZER_CONFIGS


class AXI4MasterWriteScenarioTB:
    """Test bench for running different test scenarios on AXI4 Master Write module"""

    def __init__(self, dut):
        """Initialize the scenario testbench"""
        self.dut = dut
        self.test_type = os.environ.get('TEST_TYPE', 'basic')

        # Create the base testbench
        self.tb = AXI4MasterWriteTB(
            dut=dut,
            id_width=int(dut.AXI_ID_WIDTH.value),
            addr_width=int(dut.AXI_ADDR_WIDTH.value),
            data_width=int(dut.AXI_DATA_WIDTH.value),
            user_width=int(dut.AXI_USER_WIDTH.value),
            channels=int(dut.CHANNELS.value),
            error_fifo_depth=int(dut.ERROR_FIFO_DEPTH),
            skid_depth_aw=int(dut.SKID_DEPTH_AW),
            skid_depth_w=int(dut.SKID_DEPTH_W),
            skid_depth_b=int(dut.SKID_DEPTH_B),
            alignment_mask=0xFFF  # Start with 4K boundary
        )

        # Set the test type
        self.tb.test_type = self.test_type

        # Setup logging
        self.log = self.tb.log
        self.log.info(f"Created AXI4MasterWriteScenarioTB with test_type: {self.test_type}")

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

    async def run_selected_test(self):
        """Run the selected test type"""
        return await self.tb.run_selected_test()


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def axi4_master_write_scenario_test(dut):
    """Main entry point for scenario-based AXI4 Master Write tests"""
    # Create the scenario testbench
    scenario_tb = AXI4MasterWriteScenarioTB(dut)

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

    # For faster testing, use a smaller subset
    use_cg = [False]
    data_widths = [32]
    skid_depths = [4]
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
def test_axi_master_write(request, clk_period_ns, use_cg, CG_IDLE_COUNT_WIDTH, channels, id_width, addr_width, data_width, user_width,
                            skid_depth, fifo_depth, test_type):
    """Main test function for AXI Master Write module"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn':  'rtl/common',
            'rtl_amba': 'rtl/amba',
        }
    )

    # Set up all of the test names
    post = '_cg' if use_cg else ''
    dut_name = f"axi_master_wr{post}"
    toplevel = dut_name

    verilog_sources_pre = [
        os.path.join(rtl_dict['rtl_cmn'],  "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "counter_freq_invariant.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_amba'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axi_errmon_base.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axi_master_wr_splitter.sv"),
        os.path.join(rtl_dict['rtl_amba'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba'], f"{dut_name}.sv"),
    ]
    verilog_sources_cg = [
        os.path.join(rtl_dict['rtl_cmn'],  "icg.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "clock_gate_ctrl.sv"),
        os.path.join(rtl_dict['rtl_amba'], "amba_clock_gate_ctrl.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axi_master_wr.sv"),
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
        'SKID_DEPTH_AW': str(skid_depth),
        'SKID_DEPTH_W': str(skid_depth),
        'SKID_DEPTH_B': str(skid_depth),
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
