"""
AXI4 Read Master Test Runner

Test runner for the AXI4 read master stub using the CocoTB framework.
Tests various AXI4 configurations and validates read transactions.

Based on the GAXI test runner pattern but simplified for AXI4 read-only testing.
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


# Import the testbench (assuming it's in the same directory structure)
from CocoTBFramework.tbclasses.axi4.axi4_master_read_tb import AXI4MasterReadTB


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def axi4_read_master_test(dut):
    """AXI4 read master test using the AXI4 framework components"""

    # Create testbench instance
    tb = AXI4MasterReadTB(dut, aclk=dut.aclk, aresetn=dut.aresetn)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'AXI4 read master test with seed: {seed}')

    # Get test parameters from environment
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    valid_levels = ['basic', 'medium', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'basic'. Valid: {valid_levels}")
        test_level = 'basic'

    # Start clock and reset sequence
    await tb.start_clock('aclk', tb.TEST_CLK_PERIOD, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('aclk', 10)
    await tb.deassert_reset()
    await tb.wait_clocks('aclk', 10)

    tb.log.info(f"Starting {test_level.upper()} AXI4 read master test...")
    tb.log.info(f"AXI4 widths: ID={tb.TEST_ID_WIDTH}, ADDR={tb.TEST_ADDR_WIDTH}, DATA={tb.TEST_DATA_WIDTH}")

    # Define test configurations based on test level
    if test_level == 'basic':
        timing_profiles = ['normal', 'fast']
        single_read_counts = [10, 20]
        burst_lengths = [[2, 4], [4, 8]]
        stress_count = 25
    elif test_level == 'medium':
        timing_profiles = ['normal', 'fast', 'slow', 'backtoback']
        single_read_counts = [20, 40, 30]
        burst_lengths = [[2, 4, 8], [4, 8, 16], [1, 2, 4, 8]]
        stress_count = 50
    else:  # test_level == 'full'
        timing_profiles = ['normal', 'fast', 'slow', 'backtoback', 'stress']
        single_read_counts = [30, 50, 75]
        burst_lengths = [[1, 2, 4, 8, 16], [2, 4, 8, 16, 32], [1, 3, 7, 15, 31]]
        stress_count = 100

    tb.log.info(f"Testing with timing profiles: {timing_profiles}")

    # Test 1: Basic connectivity test
    tb.log.info("=== Test 1: Basic Connectivity ===")
    tb.set_timing_profile('normal')

    # Single read from known memory location
    success, data, info = await tb.single_read_test(0x1000)
    if not success:
        tb.log.error("Basic connectivity test failed!")
        raise RuntimeError("Basic connectivity failed")

    tb.log.info(f"✓ Basic connectivity test passed: data=0x{data:08X}")

    # Test 2: Single read sequences with different timing profiles
    tb.log.info("=== Test 2: Single Read Sequences ===")

    for i, (profile, count) in enumerate(zip(timing_profiles, single_read_counts)):
        tb.log.info(f"[{i+1}/{len(timing_profiles)}] Single reads with '{profile}' timing ({count} reads)")
        tb.set_timing_profile(profile)

        result = await tb.basic_read_sequence(count)
        if not result:
            tb.log.error(f"Single read sequence failed with '{profile}' timing")
            # Don't fail immediately - continue testing other profiles
        else:
            tb.log.info(f"✓ Single read sequence passed with '{profile}' timing")

    # Test 3: Burst read sequences
    tb.log.info("=== Test 3: Burst Read Sequences ===")

    for i, (profile, lengths) in enumerate(zip(timing_profiles, burst_lengths)):
        tb.log.info(f"[{i+1}/{len(timing_profiles)}] Burst reads with '{profile}' timing: {lengths}")
        tb.set_timing_profile(profile)

        result = await tb.burst_read_sequence(lengths)
        if not result:
            tb.log.error(f"Burst read sequence failed with '{profile}' timing")
        else:
            tb.log.info(f"✓ Burst read sequence passed with '{profile}' timing")

    # Test 4: Mixed read patterns (medium and full levels)
    if test_level in ['medium', 'full']:
        tb.log.info("=== Test 4: Mixed Read Patterns ===")

        # Alternating single and burst reads
        tb.set_timing_profile('normal')
        mixed_success = 0
        mixed_total = 10

        for i in range(mixed_total):
            if i % 2 == 0:
                # Single read
                addr = 0x1000 + (i * 4)
                success, _, _ = await tb.single_read_test(addr)
            else:
                # Short burst read
                addr = 0x2000 + (i * 16)
                success, _, _ = await tb.burst_read_test(addr, 4)

            if success:
                mixed_success += 1

            await tb.wait_clocks('aclk', 3)

        tb.log.info(f"Mixed patterns result: {mixed_success}/{mixed_total} successful")

    # Test 5: Address pattern validation
    tb.log.info("=== Test 5: Address Pattern Validation ===")

    # Test reads from different memory regions
    test_addresses = [
        (0x1000, "Incremental pattern"),
        (0x2000, "Address-based pattern"),
        (0x3000, "Fixed patterns")
    ]

    for addr, description in test_addresses:
        tb.log.info(f"Testing {description} at 0x{addr:08X}")
        success, data, info = await tb.single_read_test(addr)
        if success:
            tb.log.info(f"✓ {description}: data=0x{data:08X}")
        else:
            tb.log.warning(f"⚠ {description} failed")

    # Test 6: Stress testing (medium and full levels)
    if test_level in ['medium', 'full']:
        tb.log.info("=== Test 6: Stress Testing ===")

        result = await tb.stress_read_test(stress_count)
        if result:
            tb.log.info(f"✓ Stress test passed ({stress_count} reads)")
        else:
            tb.log.warning(f"⚠ Stress test had issues ({stress_count} reads)")

    # Test 7: Boundary conditions (full level)
    if test_level == 'full':
        tb.log.info("=== Test 7: Boundary Conditions ===")

        # Test maximum burst length
        if tb.TEST_DATA_WIDTH >= 32:  # Only for reasonable data widths
            max_burst = min(16, 256)  # Reasonable maximum
            success, _, _ = await tb.burst_read_test(0x1000, max_burst)
            if success:
                tb.log.info(f"✓ Maximum burst test passed (length={max_burst})")
            else:
                tb.log.warning(f"⚠ Maximum burst test failed (length={max_burst})")

        # Test edge addresses
        edge_addresses = [0x0000, 0x1000, 0x2000, 0x3000]
        for addr in edge_addresses:
            success, _, _ = await tb.single_read_test(addr)
            if success:
                tb.log.debug(f"✓ Edge address test passed: 0x{addr:08X}")

    # Final statistics and cleanup
    tb.log.info("=== Test Results Summary ===")
    stats = tb.get_test_stats()

    tb.log.info("Test Statistics:")
    tb.log.info(f"  Total reads: {stats['summary']['total_reads']}")
    tb.log.info(f"  Successful reads: {stats['summary']['successful_reads']}")
    tb.log.info(f"  Success rate: {stats['summary']['success_rate']}")
    tb.log.info(f"  Single reads: {stats['details']['single_reads']}")
    tb.log.info(f"  Burst reads: {stats['details']['burst_reads']}")
    tb.log.info(f"  Data mismatches: {stats['details']['data_mismatches']}")
    tb.log.info(f"  Response errors: {stats['details']['response_errors']}")
    tb.log.info(f"  Timeout errors: {stats['details']['timeout_errors']}")

    # Determine overall test result
    success_rate = float(stats['summary']['success_rate'].rstrip('%'))
    if success_rate >= 95.0:
        tb.log.info(f"✓ ALL {test_level.upper()} AXI4 READ MASTER TESTS PASSED!")
    else:
        tb.log.error(f"✗ AXI4 READ MASTER TESTS FAILED (success rate: {success_rate:.1f}%)")
        raise RuntimeError(f"Test failed with {success_rate:.1f}% success rate")


def generate_axi4_params():
    """Generate AXI4 parameter combinations for testing"""

    # Define parameter ranges
    id_widths = [4, 8, 12]
    addr_widths = [32, 64]  # Common AXI4 address widths
    data_widths = [32, 64, 128]  # Common AXI4 data widths
    user_widths = [1, 4]  # Minimal user width options
    ar_depths = [2, 4, 8]  # AR channel buffer depths
    r_depths = [2, 4, 8]   # R channel buffer depths
    test_levels = ['basic', 'medium', 'full']

    # For debugging/quick testing, return a smaller subset
    debug_mode = True
    if debug_mode:
        return [
            (8, 32, 32, 1, 2, 4, 'basic'),
            # (8, 32, 64, 1, 4, 4, 'basic'),
            # (12, 64, 32, 4, 4, 8, 'medium'),
        ]

    # Full parameter sweep for comprehensive testing
    return list(product(id_widths, addr_widths, data_widths, user_widths,
                        ar_depths, r_depths, test_levels))


@pytest.mark.parametrize("id_width, addr_width, data_width, user_width, ar_depth, r_depth, test_level",
                        generate_axi4_params())
def test_axi4_read_master(request, id_width, addr_width, data_width, user_width,
                            ar_depth, r_depth, test_level):
    """Test AXI4 read master with different parameter combinations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi4': 'rtl/amba/axi4/stubs',
        'rtl_gaxi': 'rtl/amba/gaxi',
    })

    # Set up test names and directories
    dut_name = "axi4_master_rd_stub"
    id_str = TBBase.format_dec(id_width, 2)
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 3)
    uw_str = TBBase.format_dec(user_width, 1)
    ard_str = TBBase.format_dec(ar_depth, 1)
    rd_str = TBBase.format_dec(r_depth, 1)

    test_name_plus_params = f"test_axi4_read_master_i{id_str}_a{aw_str}_d{dw_str}_u{uw_str}_ard{ard_str}_rd{rd_str}_{test_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Verilog sources - include dependencies for gaxi_skid_buffer
    verilog_sources = [
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),  # Dependency
        os.path.join(rtl_dict['rtl_axi4'], f"{dut_name}.sv"),       # Main DUT
    ]

    # Check that files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # RTL parameters
    wstrb_width = data_width // 8
    ar_size = id_width + addr_width + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + user_width  # AR packet size
    r_size = id_width + data_width + 2 + 1 + user_width  # R packet size

    rtl_parameters = {
        'SKID_DEPTH_AR': str(ar_depth),
        'SKID_DEPTH_R': str(r_depth),
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': str(user_width),
        'AXI_WSTRB_WIDTH': str(wstrb_width),
        # Calculated parameters
        'AW': str(addr_width),
        'DW': str(data_width),
        'IW': str(id_width),
        'SW': str(wstrb_width),
        'UW': str(user_width),
        'ARSize': str(ar_size),
        'RSize': str(r_size),
    }

    # Calculate timeout based on complexity
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    complexity_factor = (data_width + addr_width + id_width) / 100.0
    timeout_ms = int(5000 * timeout_multipliers.get(test_level, 1) * max(1.0, complexity_factor))

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
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),

        # AXI4 test parameters
        'TEST_ID_WIDTH': str(id_width),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_USER_WIDTH': str(user_width),
        'TEST_CLK_PERIOD': '10',  # 10ns = 100MHz
        'TIMEOUT_CYCLES': '2000',

        # Buffer depth parameters
        'TEST_AR_DEPTH': str(ar_depth),
        'TEST_R_DEPTH': str(r_depth),
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
        "-Wno-PINMISSING",  # Allow unconnected pins for stub testing
    ]
    sim_args = ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
    plusargs = ["+trace"]

    # Create command file for viewing results
    cmd_filename = create_view_cmd(os.path.dirname(log_path), log_path, sim_build,
                                    module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} AXI4 Read Master test: {dut_name}")
    print(f"AXI4 Config: ID={id_width}, ADDR={addr_width}, DATA={data_width}, USER={user_width}")
    print(f"Buffer Depths: AR={ar_depth}, R={r_depth}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
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
        print(f"✓ {test_level.upper()} AXI4 Read Master test PASSED")
    except Exception as e:
        print(f"✗ {test_level.upper()} AXI4 Read Master test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise

