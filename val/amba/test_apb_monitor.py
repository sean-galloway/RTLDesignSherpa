"""
APB Monitor Test Runner

Comprehensive test runner for the APB monitor module following
the patterns established in the test_axi_master_rd_splitter.py test runner.

Features:
- Parametrized testing with pytest
- Multiple test levels (basic, medium, full)
- Comprehensive parameter combinations
- Environment variable configuration
- Proper file and directory management
- Integration with CocoTB framework
- APB-specific monitoring capabilities
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.apb_monitor.apb_monitor_tb import APBMonitorTB


@cocotb.test(timeout_time=30, timeout_unit="us")
async def apb_monitor_test(dut):
    """Main test function for APB monitor"""
    tb = APBMonitorTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'APB Monitor test with seed: {seed}')

    # Get test parameters from environment
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    valid_levels = ['basic', 'medium', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'basic'. Valid: {valid_levels}")
        test_level = 'basic'

    # Setup clocks and reset
    await tb.setup_clocks_and_reset()

    tb.log.info(f"Starting {test_level.upper()} APB monitor test...")
    tb.log.info(f"Parameters: AW={tb.AW}, DW={tb.DW}, SW={tb.SW}")
    tb.log.info(f"IDs: UNIT=0x{tb.UNIT_ID:X}, AGENT=0x{tb.AGENT_ID:02X}")
    tb.log.info(f"Max Transactions: {tb.MAX_TRANSACTIONS}")

    # Run test based on level
    if test_level == 'basic':
        passed = await tb.test_basic_transactions()
        passed = passed and tb.scoreboard.verify_monitor_behavior()
    elif test_level == 'medium':
        # Run selected tests for medium level
        basic_result = await tb.test_basic_transactions()
        error_result = await tb.test_error_detection()
        timeout_result = await tb.test_timeout_detection()
        perf_result = await tb.test_performance_monitoring()

        passed = all([basic_result, error_result, timeout_result, perf_result])
        passed = passed and tb.scoreboard.verify_monitor_behavior()
    else:  # full
        passed = await tb.run_comprehensive_test_suite()


def generate_test_params():
    """Generate comprehensive test parameter combinations"""
    addr_widths = [8, 32]
    data_widths = [32, 64]
    unit_ids = [4]  # 4-bit values
    agent_ids = [8]  # 8-bit values
    max_transactions = [2, 4]
    test_levels = ['full']

    # For CI/testing, use a smaller subset
    debug = True
    if debug:
        return [
            (32, 32, 4, 8, 4, 'basic'),
        ]

    # Full parameter sweep for comprehensive testing
    return list(product(addr_widths, data_widths, unit_ids, agent_ids, max_transactions, test_levels))


@pytest.mark.parametrize("aw, dw, unit_id, agent_id, max_trans, test_level", generate_test_params())
def test_apb_monitor(request, aw, dw, unit_id, agent_id, max_trans, test_level):
    """Test APB monitor with parametrized configurations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':           'rtl/common',
        'rtl_gaxi':          'rtl/amba/gaxi',
        'rtl_apb':           'rtl/amba/apb',
        'rtl_amba_shared':   'rtl/amba/shared',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    # Set up test names and directories
    dut_name = "apb_monitor"

    # Create human-readable test identifier
    aw_str = TBBase.format_dec(aw, 2)
    dw_str = TBBase.format_dec(dw, 3)
    uid_str = f"{unit_id:02X}"
    aid_str = f"{agent_id:03d}"
    mt_str = TBBase.format_dec(max_trans, 2)

    test_name_plus_params = (f"test_apb_monitor_"
                            f"aw{aw_str}_dw{dw_str}_uid{uid_str}_aid{aid_str}_"
                            f"mt{mt_str}_{test_level}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Get verilog sources
    verilog_sources = [
        # Monitor package (must be first)
        os.path.join(rtl_dict['rtl_amba_includes'], "monitor_pkg.sv"),
        os.path.join(rtl_dict['rtl_cmn'],           "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'],           "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],          "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],          "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_apb'],          f"{dut_name}.sv")
    ]

    # RTL parameters
    rtl_parameters = {
        'ADDR_WIDTH': str(aw),
        'DATA_WIDTH': str(dw),
        'UNIT_ID': str(unit_id),
        'AGENT_ID': str(agent_id),
        'MAX_TRANSACTIONS': str(max_trans),
        'MONITOR_FIFO_DEPTH': '8',
        # Short names for convenience
        'AW': str(aw),
        'DW': str(dw),
        'SW': str(dw // 8),
    }

    # Calculate timeout based on test complexity
    timeout_multipliers = {'basic': 1, 'medium': 3, 'full': 6}
    complexity_factor = timeout_multipliers.get(test_level, 1)

    # Additional complexity factors
    data_complexity = max(1.0, dw / 32.0)  # Wider data = more complex
    trans_complexity = max(1.0, max_trans / 4.0)  # More transactions = more complex
    addr_complexity = max(1.0, aw / 32.0)  # Wider address = more complex

    total_complexity = complexity_factor * data_complexity * trans_complexity * addr_complexity
    timeout_s = int(20 * total_complexity)  # Base 20s timeout for APB monitor

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(4347), # str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'COCOTB_TEST_TIMEOUT': str(timeout_s * 1000),  # Convert to ms

        # DUT-specific parameters
        'TEST_AW': str(aw),
        'TEST_DW': str(dw),
        'TEST_UNIT_ID': str(unit_id),
        'TEST_AGENT_ID': str(agent_id),
        'TEST_MAX_TRANSACTIONS': str(max_trans),
        'TEST_CLOCK_PERIOD': '10',  # 10ns = 100MHz
        'TEST_TIMEOUT_CYCLES': '1000',

        # APB Monitor specific configurations
        'TEST_ENABLE_ERROR_DETECTION': '1',
        'TEST_ENABLE_TIMEOUT_DETECTION': '1',
        'TEST_ENABLE_PERFORMANCE_MONITORING': '1',
        'TEST_ENABLE_DEBUG_EVENTS': '1',
        'TEST_CMD_TIMEOUT_CYCLES': '100',
        'TEST_RSP_TIMEOUT_CYCLES': '200',
        'TEST_LATENCY_THRESHOLD': '1000',
        'TEST_THROUGHPUT_THRESHOLD': '10',
    }

    # Simulation settings
    includes = [sim_build]
    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "--trace-depth", "99",
        "-Wall",
        "-Wno-UNUSED",
        "-Wno-DECLFILENAME",
        "-Wno-PINMISSING",  # Allow unconnected ports for testbench
        "-Wno-WIDTH",       # Allow width mismatches in testbench
    ]
    sim_args = [
        "--trace-fst",
        "--trace-structs",
        "--trace-depth", "99"
    ]
    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(os.path.dirname(log_path), log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} APB Monitor test")
    print(f"Parameters: AW={aw}, DW={dw}, SW={dw//8}")
    print(f"IDs: UNIT=0x{unit_id:X}, AGENT=0x{agent_id:02X}")
    print(f"Max Transactions: {max_trans}")
    print(f"Expected duration: {timeout_s}s")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
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
        print(f"✓ {test_level.upper()} APB Monitor test PASSED")

    except Exception as e:
        print(f"✗ {test_level.upper()} APB Monitor test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")
        raise



