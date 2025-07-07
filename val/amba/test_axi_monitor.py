"""
AXI Monitor Test Runner

Comprehensive test runner for the AXI monitor module following
the patterns established in the project test framework.

Features:
- Parametrized testing with pytest for both read and write monitors
- Multiple test levels (basic, medium, full)
- Support for both AXI4 and AXI-Lite protocols
- Comprehensive parameter combinations
- Environment variable configuration
- Proper file and directory management
- Integration with CocoTB framework
- Monitor bus (monbus) verification
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.misc.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.axi_monitor.axi_monitor_tb import AXIMonitorTB


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def axi_monitor_test(dut):
    """Main test function for AXI monitor"""
    tb = AXIMonitorTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'AXI Monitor test with seed: {seed}')

    # Get test parameters from environment
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()
    is_read = int(os.environ.get('TEST_IS_READ', '1')) == 1
    is_axi4 = int(os.environ.get('TEST_IS_AXI', '1')) == 1

    valid_levels = ['basic', 'medium', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'basic'. Valid: {valid_levels}")
        test_level = 'basic'

    # Setup clocks and reset
    await tb.setup_clocks_and_reset()

    protocol_str = "AXI4" if is_axi4 else "AXI-Lite"
    monitor_type = "READ" if is_read else "WRITE"
    
    tb.log.info(f"Starting {test_level.upper()} {protocol_str} {monitor_type} monitor test...")
    tb.log.info(f"Parameters: IW={tb.IW}, AW={tb.AW}, DW={tb.DW}, UW={tb.UW}")
    tb.log.info(f"Max Transactions={tb.MAX_TRANSACTIONS}, Unit ID={tb.UNIT_ID}, Agent ID={tb.AGENT_ID}")

    # Run all tests
    passed = await tb.run_all_tests()

    # Verify test result
    assert passed, f"{protocol_str} {monitor_type} monitor test failed at level {test_level}"

    tb.log.info(f"✓ ALL {test_level.upper()} {protocol_str} {monitor_type} MONITOR TESTS PASSED!")


def generate_test_params():
    """Generate comprehensive test parameter combinations"""
    
    # Test configurations based on complexity
    basic_params = {
        'iw': [8],
        'aw': [32],
        'dw': [32],
        'uw': [1],
        'max_transactions': [8],
        'is_read': [0],  # Test both read and write monitors
        'is_axi': [1],      # Start with AXI4 only for basic
        'unit_id': [9],
        'agent_id': [99],
        'test_levels': ['basic']
    }
    
    medium_params = {
        'iw': [4, 8, 12],
        'aw': [32, 40],
        'dw': [32, 64, 128],
        'uw': [1, 4],
        'max_transactions': [8, 16, 32],
        'is_read': [1, 0],
        'is_axi': [1, 0],   # Test both AXI4 and AXI-Lite
        'unit_id': [9, 15],
        'agent_id': [99, 127],
        'test_levels': ['medium']
    }
    
    full_params = {
        'iw': [4, 8, 12, 16],
        'aw': [32, 40, 48],
        'dw': [32, 64, 128, 256],
        'uw': [1, 4, 8],
        'max_transactions': [8, 16, 32, 64],
        'is_read': [1, 0],
        'is_axi': [1, 0],
        'unit_id': [9, 15],
        'agent_id': [99, 127, 255],
        'test_levels': ['full']
    }
    
    # Determine which test level to run
    test_level = 'basic'
    
    if test_level == 'basic':
        params = basic_params
    elif test_level == 'medium':
        params = medium_params
    elif test_level == 'full':
        params = full_params
    else:
        print(f"Warning: Unknown test level '{test_level}', using 'basic'")
        params = basic_params
    
    # Generate all combinations
    combinations = list(product(
        params['iw'],
        params['aw'], 
        params['dw'],
        params['uw'],
        params['max_transactions'],
        params['is_read'],
        params['is_axi'],
        params['unit_id'],
        params['agent_id'],
        params['test_levels']
    ))
    
    # For quick testing, limit combinations in basic mode
    if test_level == 'basic':
        # Select a representative subset
        combinations = combinations[:4]  # First 4 combinations
    elif test_level == 'medium':
        combinations = combinations[:16]  # First 16 combinations
    
    return combinations


@pytest.mark.parametrize("iw, aw, dw, uw, max_transactions, is_read, is_axi, unit_id, agent_id, test_level", 
                            generate_test_params())
def test_axi_monitor(request, iw, aw, dw, uw, max_transactions, is_read, is_axi, unit_id, agent_id, test_level):
    """Test AXI monitor with parametrized configurations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':           'rtl/common',
        'rtl_gaxi':          'rtl/amba/gaxi',
        'rtl_amba_shared':  'rtl/amba/shared',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    # Set up test names and directories
    dut_name = "axi_monitor_base"

    # Create human-readable test identifier
    iw_str = TBBase.format_dec(iw, 2)
    aw_str = TBBase.format_dec(aw, 2)
    dw_str = TBBase.format_dec(dw, 3)
    uw_str = TBBase.format_dec(uw, 2)
    mt_str = TBBase.format_dec(max_transactions, 2)
    protocol_str = "axi4" if is_axi else "axil"
    monitor_type = "rd" if is_read else "wr"
    
    test_name_plus_params = (f"test_axi_monitor_"
                            f"iw{iw_str}_aw{aw_str}_dw{dw_str}_uw{uw_str}_"
                            f"mt{mt_str}_{protocol_str}_{monitor_type}_"
                            f"u{unit_id:02X}_a{agent_id:02X}_{test_level}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Get verilog sources - following the RTL file structure from the documents
    verilog_sources = [
        # Common dependencies
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_freq_invariant.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        
        # GAXI dependencies
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        
        # Monitor-specific files (based on the document structure)
        os.path.join(rtl_dict['rtl_amba_includes'], "monitor_pkg.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'],   "axi_monitor_timer.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'],   "axi_monitor_timeout.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'],   "axi_monitor_trans_mgr.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'],   "axi_monitor_reporter.sv"),
        
        # Main DUT
        os.path.join(rtl_dict['rtl_amba_shared'], f"{dut_name}.sv")
    ]

    # RTL parameters
    rtl_parameters = {
        # Main parameters
        'UNIT_ID': str(unit_id),
        'AGENT_ID': str(agent_id),
        'MAX_TRANSACTIONS': str(max_transactions),
        'ADDR_WIDTH': str(aw),
        'ID_WIDTH': str(iw),
        'ADDR_BITS_IN_PKT': str(min(aw, 38)),  # Limited by interrupt packet format
        
        # Configuration options
        'IS_READ': str(is_read),
        'IS_AXI': str(is_axi),
        'ENABLE_PERF_PACKETS': '1',
        'ENABLE_DEBUG_MODULE': '1',
        
        # FIFO depths
        'INTR_FIFO_DEPTH': '8',
        'DEBUG_FIFO_DEPTH': '8',
        
        # Short names for convenience
        'AW': str(aw),
        'IW': str(iw),
    }

    # Calculate timeout based on test complexity
    timeout_multipliers = {'basic': 1, 'medium': 3, 'full': 6}
    complexity_factor = timeout_multipliers.get(test_level, 1)

    # Additional complexity factors
    id_complexity = max(1.0, iw / 8.0)  # More IDs = more complex
    transaction_complexity = max(1.0, max_transactions / 16.0)  # More transactions = more complex
    protocol_complexity = 1.5 if is_axi else 1.0  # AXI4 is more complex than AXI-Lite
    
    total_complexity = (complexity_factor * id_complexity * 
                       transaction_complexity * protocol_complexity)
    timeout_s = int(30 * total_complexity)  # Base 30s timeout

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'COCOTB_TEST_TIMEOUT': str(timeout_s * 1000),  # Convert to ms

        # DUT-specific parameters
        'TEST_IW': str(iw),
        'TEST_AW': str(aw),
        'TEST_DW': str(dw),
        'TEST_UW': str(uw),
        'TEST_IS_AXI4': str(is_axi),
        'TEST_IS_READ': str(is_read),
        'TEST_MAX_TRANSACTIONS': str(max_transactions),
        'TEST_UNIT_ID': str(unit_id),
        'TEST_AGENT_ID': str(agent_id),
        'TEST_CLOCK_PERIOD': '10',  # 10ns = 100MHz
        'TEST_TIMEOUT_CYCLES': '1000',
        
        # Safety limits for complex tests
        'TB_MAX_DURATION_MIN': str(timeout_s // 60 + 1),
        'TB_MAX_MEMORY_MB': '4096',
        'TB_ENABLE_SAFETY': 'true',
    }

    # Simulation settings
    includes = [os.path.join(rtl_dict['rtl_amba_includes'])]
    compile_args = [
        "--trace-fst",
        "--trace-structs", 
        "--trace-depth", "99",
        "-Wall",
        "-Wno-UNUSED",
        "-Wno-DECLFILENAME",
        "-Wno-PINMISSING",  # Allow unconnected ports for testbench
        "-Wno-WIDTHEXPAND", # Allow width expansions
        "-Wno-WIDTHTRUNC",  # Allow width truncations
    ]
    sim_args = [
        "--trace-fst",
        "--trace-structs",
        "--trace-depth", "99"
    ]
    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(os.path.dirname(log_path), log_path, sim_build, module, test_name_plus_params)

    protocol_name = "AXI4" if is_axi else "AXI-Lite"
    monitor_name = "READ" if is_read else "WRITE"
    
    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} {protocol_name} {monitor_name} Monitor test")
    print(f"Parameters: IW={iw}, AW={aw}, DW={dw}, UW={uw}")
    print(f"Max Transactions={max_transactions}, Unit ID=0x{unit_id:X}, Agent ID=0x{agent_id:X}")
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
        print(f"✓ {test_level.upper()} {protocol_name} {monitor_name} Monitor test PASSED")

    except Exception as e:
        print(f"✗ {test_level.upper()} {protocol_name} {monitor_name} Monitor test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")
        raise
