# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_descriptor_engine
# Purpose: Descriptor Engine Test Runner
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Descriptor Engine Test Runner

Test runner for the descriptor_engine.sv module using the CocoTB framework.
Tests both APB programming interface and CDA packet reception paths.

The descriptor engine converts APB requests to AXI reads and passes CDA packets
directly through to descriptor outputs with proper channel filtering.

Based on the AMBA/RAPIDS test runner pattern.
"""

import os
import sys

# Add RAPIDS DV directory to path to import project-area testbench classes
# This makes the import work regardless of whether env_python is sourced
rapids_dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../..'))
if rapids_dv_path not in sys.path:
    sys.path.insert(0, rapids_dv_path)

import random
import shutil
import time
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run

# Import TB class from PROJECT AREA (not framework!)
from tbclasses.descriptor_engine_tb import DescriptorEngineTB, TestClass, DelayProfile
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=600, timeout_unit="sec")
async def descriptor_engine_test(dut):
    """Descriptor engine test using the RAPIDS framework components

    Timeout: 600 seconds (10 minutes) to handle full-level tests:
    - Full level: 20 packets × 10 profiles × 3 test classes = 600 packets
    - Each packet ~500-2000 cycles depending on delay profile
    - Estimated max sim time: ~1.2M cycles @ 10ns = ~12ms sim time
    - Allow 10 minutes for full test execution with ample margin
    """

    # Create testbench instance
    tb = DescriptorEngineTB(dut, clk=dut.clk, rst_n=dut.rst_n)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'Descriptor engine test with seed: {seed}')

    # Get test level from environment (passed from pytest runner)
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    valid_levels = ['basic', 'medium', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid test_level '{test_level}', using 'basic'. Valid: {valid_levels}")
        test_level = 'basic'

    # Complete clock and reset sequence (following AMBA testbench pattern)
    await tb.setup_clocks_and_reset()

    # Initialize test components (AXI slave, GAXI masters, memory model)
    await tb.initialize_test()
    await tb.wait_clocks('clk', 10)

    try:
        overall_success = True

        if test_level == 'basic':
            # Basic level: Quick validation with smaller packet counts
            tb.log.info("=== BASIC LEVEL: Quick validation tests ===")

            # Quick APB validation (10 packets)
            apb_success = await tb.run_apb_basic_test(num_requests=10)
            if not apb_success:
                tb.log.error("Basic APB test failed")
                overall_success = False

            # Quick CDA validation (10 packets)
            cda_success = await tb.run_cda_basic_test(num_packets=10)
            if not cda_success:
                tb.log.error("Basic CDA test failed")
                overall_success = False

            # Quick concurrent test
            concurrent_success = await tb.run_concurrent_test()
            if not concurrent_success:
                tb.log.error("Basic concurrent test failed")
                overall_success = False

        elif test_level == 'medium':
            # Medium level: 10x packet count (30 packets), 7 diverse delay profiles
            tb.log.info("=== MEDIUM LEVEL: Enhanced delay profile coverage with 10x packet count ===")
            tb.log.info("🔍 Running 30 packets per delay profile (10x increase) across 7 diverse profiles")

            # Run APB Only test class with 30 packets per delay profile
            apb_class_success = await tb.run_comprehensive_test_class(TestClass.APB_ONLY, num_packets=30, test_level="medium")
            if not apb_class_success:
                tb.log.error("Medium APB test class failed")
                overall_success = False

        elif test_level == 'full':
            # Full level: 20 packets per profile, ALL delay profiles (10 total)
            # Reduced from 50 to 20 packets for faster execution while maintaining coverage
            tb.log.info("=== FULL LEVEL: Maximum profile coverage with efficient packet count ===")
            tb.log.info("🚀 Running 20 packets per delay profile across ALL 10 delay profiles")
            tb.log.info("🎯 Testing all 3 test classes: APB Only, CDA Only, Mixed")
            tb.log.info("⏱️  Target completion: <5 minutes")

            # Test Class 1: APB Only (20 packets per delay profile, all profiles)
            tb.log.info("\n🎯 === COMPREHENSIVE APB ONLY TEST CLASS (20 packets/profile) ===")
            tb.log.info("🔍 Each delay profile will run 20 packets for good randomization coverage")
            apb_class_success = await tb.run_comprehensive_test_class(TestClass.APB_ONLY, num_packets=20, test_level="full")
            if not apb_class_success:
                tb.log.error("APB Only test class failed")
                overall_success = False

            # Wait between test classes
            await tb.wait_clocks('clk', 100)

            # Test Class 2: CDA Only (20 packets per delay profile, all profiles)
            tb.log.info("\n🎯 === COMPREHENSIVE CDA ONLY TEST CLASS (20 packets/profile) ===")
            tb.log.info("🔍 Each delay profile will run 20 packets for good randomization coverage")
            cda_class_success = await tb.run_comprehensive_test_class(TestClass.CDA_ONLY, num_packets=20, test_level="full")
            if not cda_class_success:
                tb.log.error("CDA Only test class failed")
                overall_success = False

            # Wait between test classes
            await tb.wait_clocks('clk', 100)

            # Test Class 3: Mixed (20 packets per delay profile, all profiles)
            tb.log.info("\n🎯 === COMPREHENSIVE MIXED TEST CLASS (20 packets/profile) ===")
            tb.log.info("🔍 Each delay profile will run 20 packets for good randomization coverage")
            mixed_class_success = await tb.run_comprehensive_test_class(TestClass.MIXED, num_packets=20, test_level="full")
            if not mixed_class_success:
                tb.log.error("Mixed test class failed")
                overall_success = False

        else:
            tb.log.error(f"Unknown test level: {test_level}")
            overall_success = False

        # Wait for final completion
        await tb.wait_clocks('clk', 20)

        # Generate comprehensive final report
        report_success = tb.generate_final_report()

        if not report_success or not overall_success:
            raise AssertionError("Comprehensive descriptor engine test validation failed")

        tb.log.info("=== ALL COMPREHENSIVE DESCRIPTOR ENGINE TESTS PASSED ===")

    except AssertionError as e:
        tb.log.error(f"Descriptor engine test failed: {str(e)}")
        raise

    except Exception as e:
        tb.log.error(f"Descriptor engine test error: {str(e)}")
        raise


@pytest.mark.parametrize("test_level,num_channels,addr_width,data_width,axi_id_width", [
    # All configurations use fixed 512-bit data width due to RTL control bit positions
    # Note: AXI_ID_WIDTH must be >= $clog2(NUM_CHANNELS), using 64-bit addresses

    # Basic test level - quick validation for all configurations
    ("basic", 32, 64, 512, 8),    # Standard configuration (CHAN_WIDTH=5, AXI_ID_WIDTH=8)
    ("basic", 16, 64, 512, 8),    # Fewer channels (CHAN_WIDTH=4, AXI_ID_WIDTH=8)
    ("basic", 8, 64, 512, 8),     # Minimal channels (CHAN_WIDTH=3, AXI_ID_WIDTH=8)
    ("basic", 4, 64, 512, 8),     # Very few channels (CHAN_WIDTH=2, AXI_ID_WIDTH=8)
    ("basic", 64, 64, 512, 8),    # Many channels (CHAN_WIDTH=6, AXI_ID_WIDTH=8)
    ("basic", 32, 64, 512, 6),    # 6-bit ID (CHAN_WIDTH=5, AXI_ID_WIDTH=6) - minimum valid
    ("basic", 32, 64, 512, 12),   # 12-bit ID (CHAN_WIDTH=5, AXI_ID_WIDTH=12)
    ("basic", 16, 64, 512, 4),    # 4-bit ID (CHAN_WIDTH=4, AXI_ID_WIDTH=4) - minimum valid
    ("basic", 8, 64, 512, 3),     # 3-bit ID (CHAN_WIDTH=3, AXI_ID_WIDTH=3) - minimum valid

    # Medium test level - comprehensive testing for key configurations
    ("medium", 32, 64, 512, 8),   # Standard configuration with extended testing
    ("medium", 8, 64, 512, 3),    # Minimal configuration with extended testing
    ("medium", 64, 64, 512, 8),   # High channel count with extended testing

    # Full test level - exhaustive testing for critical configurations
    ("full", 32, 64, 512, 8),     # Standard configuration with full test suite
    ("full", 8, 64, 512, 3),      # Minimal configuration with full test suite
])
def test_descriptor_engine(request, test_level, num_channels, addr_width, data_width, axi_id_width):
    """Run the descriptor engine test with different configurations"""

    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_fub': '../../rtl/rapids_fub',
        'rtl_rapids_includes': '../../rtl/includes',
        'rtl_amba_includes': 'rtl/amba/includes',
        'rtl_amba': 'rtl/amba',
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "descriptor_engine"
    toplevel = dut_name

    # Get Verilog sources and includes from hierarchical file list
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/fub/descriptor_engine.f'
    )

    # Create a human readable test identifier including test level
    nc_str = TBBase.format_dec(num_channels, 2)
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 4)
    iw_str = TBBase.format_dec(axi_id_width, 2)

    test_name_plus_params = f"test_{dut_name}_{test_level}_nc{nc_str}_aw{aw_str}_dw{dw_str}_iw{iw_str}"

    # Add worker ID for pytest-xdist parallel execution to avoid build conflicts
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path - include test level and worker ID for uniqueness
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Clean and create sim_build directory to avoid file locking issues
    if os.path.exists(sim_build):
        try:
            shutil.rmtree(sim_build)
        except (OSError, PermissionError):
            # If cleanup fails, add timestamp for uniqueness
            timestamp = int(time.time() * 1000) % 100000
            sim_build = f"{sim_build}_{timestamp}"

    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters for descriptor engine
    parameters = {
        'CHANNEL_ID': '0',
        'NUM_CHANNELS': num_channels,
        'ADDR_WIDTH': addr_width,
        'DATA_WIDTH': data_width,
        'AXI_ID_WIDTH': axi_id_width,
        'FIFO_DEPTH': '8',
        'TIMEOUT_CYCLES': '1000',
        'MON_AGENT_ID': "8'h10",
        'MON_UNIT_ID': "4'h1",
        'MON_CHANNEL_ID': "6'h0"
    }

    # Environment variables
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_NUM_CHANNELS': str(num_channels),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_AXI_ID_WIDTH': str(axi_id_width),
        'TEST_LEVEL': test_level
    }

    # VCD tracing: Use compile_args to add --trace (VCD), not --trace-fst
    # cocotb-test only adds --trace-fst when waves=True at line 1133
    # We'll use waves=False and manually add VCD tracing
    compile_args = [
        "--trace",              # VCD tracing (not FST!)
        "--trace-depth", "5",   # Reasonable depth for debugging
        "-Wall",
        "-Wno-PINMISSING",
        "-Wno-UNUSED",
        "-Wno-EOFNEWLINE",
        "-Wno-PINCONNECTEMPTY",
        "-Wno-IMPORTSTAR"
    ]

    sim_args = []

    plusargs = []

    # Print test information
    print(f"\n🚀 Comprehensive Descriptor Engine Test")
    print(f"📊 Configuration: {num_channels} channels, {addr_width}-bit addr, {data_width}-bit data, {axi_id_width}-bit ID")
    print(f"📋 Test Level: {test_level}")
    if test_level == 'full':
        print(f"🎯 Test Classes: APB Only, CDA Only, Mixed (20 packets each)")
        print(f"📈 Delay Profiles: ALL {len([p for p in DelayProfile])} profiles per class (maximum coverage)")
        print(f"📦 Total Packets: ~{20 * len([p for p in DelayProfile]) * 3} packets")
        print(f"⏱️  Estimated time: <5 minutes")
    elif test_level == 'medium':
        print(f"🎯 Test Classes: APB Only (30 packets per delay profile - 10x increase)")
        print(f"📈 Delay Profiles: 7 diverse profiles (enhanced coverage)")
        print(f"📦 Total Packets: ~{30 * 7} packets")
        print(f"⏱️  Estimated time: 30-60 seconds")
    else:
        print(f"🎯 Test Classes: Basic validation (10 packets each)")
        print(f"📦 Total Packets: ~30 packets")
        print(f"⏱️  Estimated time: <5 seconds")
    print(f"📝 Logs: {log_path}")
    print(f"📂 Sim build: {sim_build}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=os.path.splitext(os.path.basename(__file__))[0],  # Use this file as module
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # Must be False! We use compile_args for VCD instead
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )

        print(f"\n✅ Comprehensive Descriptor Engine Test COMPLETED!")
        print(f"📋 Results: {results_path}")
        print(f"📝 Logs: {log_path}")
        print(f"📂 Sim build: {sim_build}")
        if test_level == 'full':
            print(f"🎯 Completed: All 3 test classes with ALL {len([p for p in DelayProfile])} delay profiles (20 packets per profile)")
            print(f"📊 Total coverage: ~{20 * len([p for p in DelayProfile]) * 3} packets processed")
        elif test_level == 'medium':
            print(f"🎯 Completed: APB Only test class with 7 diverse delay profiles (30 packets per profile)")
            print(f"📊 Total coverage: ~{30 * 7} packets processed")
        else:
            print(f"🎯 Completed: Basic validation tests (~30 packets)")

    except Exception as e:
        print(f"❌ Comprehensive descriptor engine test failed: {str(e)}")
        print(f"📋 Check logs: {log_path}")
        print(f"📂 Check sim build: {sim_build}")
        raise


if __name__ == "__main__":
    print("Comprehensive Descriptor Engine Test Runner")
    print("Run with: pytest test_descriptor_engine.py -v -s")
    print("")
    print("Test Levels (built into parametrization):")
    print("  basic  - Quick validation (10 packets each, 3 basic tests, ~30 total packets)")
    print("  medium - Enhanced coverage (30 packets × 7 profiles = ~210 packets, APB Only)")
    print("  full   - Maximum coverage (20 packets × 10 profiles × 3 classes = ~600 packets)")
    print("")
    print(f"Available Test Classes: {[tc.value for tc in TestClass]}")
    print(f"Available Delay Profiles ({len([p for p in DelayProfile])} total): {[dp.value for dp in DelayProfile]}")
    print("")
    print("Coverage Summary:")
    print("  basic:  4 profiles × 1 class (quick validation, <5s)")
    print("  medium: 7 profiles × 1 class (10x packet count, ~1min)")
    print("  full:   10 profiles × 3 classes (20 packets/profile, <5min)")
    print("")
    print("Test levels are automatically included in parametrization - no environment variables needed!")
    print("Use 'pytest test_descriptor_engine.py -k basic' to run only basic tests")
    print("Use 'pytest test_descriptor_engine.py -k medium' to run only medium tests")
    print("Use 'pytest test_descriptor_engine.py -k full' to run only full tests")