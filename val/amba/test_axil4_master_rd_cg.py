# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIL4MasterReadCGTB
# Purpose: AXIL4 Master Read Clock Gated Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIL4 Master Read Clock Gated Test Runner

Test runner for the axil4_master_rd_cg module using the CocoTB framework.
Tests clock gating functionality while validating read transactions.

Based on the AXI4 clock gated test runner pattern but simplified for AXIL4 register access.
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from cocotb.triggers import RisingEdge, Timer

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.amba.amba_cg_ctrl import AxiClockGateCtrl

# Import the base testbench (we'll extend it for CG testing)
from CocoTBFramework.tbclasses.axil4.axil4_master_read_tb import AXIL4MasterReadTB


class AXIL4MasterReadCGTB(AXIL4MasterReadTB):
    """
    Clock-gated AXIL4 Master Read testbench.
    Extends the base master read testbench with clock gating capabilities.
    """

    def __init__(self, dut, aclk=None, aresetn=None):
        super().__init__(dut, aclk, aresetn)
        
        # Clock gating specific setup
        self.cg_ctrl = None
        self.setup_clock_gating_controller()
        
        # Clock gating test statistics
        self.cg_stats = {
            'total_cycles_monitored': 0,
            'gated_cycles': 0,
            'power_efficiency_percent': 0.0,
            'gating_transitions': 0
        }

    def setup_clock_gating_controller(self):
        """Setup clock gating controller for monitoring."""
        try:
            self.cg_ctrl = AxiClockGateCtrl(
                dut=self.dut,
                instance_path="i_amba_clock_gate_ctrl",
                clock_signal_name="aclk",
                user_valid_signals=["fub_arvalid", "fub_rready"],
                axi_valid_signals=["m_axil_arvalid", "m_axil_rvalid"],
                gating_signal_name="cg_gating",
                idle_signal_name="cg_idle",
                enable_signal_name="cfg_cg_enable",
                idle_count_signal_name="cfg_cg_idle_count"
            )
            self.log.info("Clock gating controller initialized")
        except Exception as e:
            self.log.warning(f"Could not initialize CG controller: {e}")

    async def configure_clock_gating(self, enable=True, idle_count=8):
        """Configure clock gating parameters."""
        if hasattr(self.dut, 'cfg_cg_enable'):
            self.dut.cfg_cg_enable.value = 1 if enable else 0
        if hasattr(self.dut, 'cfg_cg_idle_count'):
            self.dut.cfg_cg_idle_count.value = idle_count
            
        if self.cg_ctrl:
            self.cg_ctrl.enable_clock_gating(enable)
            self.cg_ctrl.set_idle_count(idle_count)
            
        await self.wait_clocks('aclk', 5)  # Let configuration settle
        self.log.info(f"Clock gating configured: enable={enable}, idle_count={idle_count}")

    async def wait_for_gating_state(self, target_state=True, timeout_cycles=100):
        """Wait for specific gating state."""
        if not hasattr(self.dut, 'cg_gating'):
            return True  # Skip if no gating signal
            
        for _ in range(timeout_cycles):
            current_state = bool(self.dut.cg_gating.value)
            if current_state == target_state:
                state_name = "gated" if target_state else "ungated"
                self.log.info(f"Reached {state_name} state")
                return True
            await RisingEdge(self.aclk)
            
        self.log.warning(f"Timeout waiting for gating state {target_state}")
        return False

    async def measure_power_efficiency(self, test_duration_cycles=1000):
        """Measure power efficiency during a test period."""
        if not hasattr(self.dut, 'cg_gating'):
            return {'error': 'No cg_gating signal available'}
            
        gated_cycles = 0
        transition_count = 0
        prev_gating_state = bool(self.dut.cg_gating.value)
        
        for cycle in range(test_duration_cycles):
            current_gating_state = bool(self.dut.cg_gating.value)
            
            if current_gating_state:
                gated_cycles += 1
                
            if current_gating_state != prev_gating_state:
                transition_count += 1
                prev_gating_state = current_gating_state
                
            await RisingEdge(self.aclk)
            
        efficiency = (gated_cycles / test_duration_cycles) * 100 if test_duration_cycles > 0 else 0
        
        self.cg_stats.update({
            'total_cycles_monitored': test_duration_cycles,
            'gated_cycles': gated_cycles,
            'power_efficiency_percent': efficiency,
            'gating_transitions': transition_count
        })
        
        self.log.info(f"Power efficiency: {efficiency:.1f}% ({gated_cycles}/{test_duration_cycles} cycles gated)")
        return self.cg_stats

    async def validate_ready_signals_during_gating(self):
        """Validate that ready signals are properly controlled during gating."""
        if not hasattr(self.dut, 'cg_gating'):
            return True
            
        gating_active = bool(self.dut.cg_gating.value)
        
        if gating_active:
            # Check that ready signals are forced to 0 during gating
            ready_checks = []
            
            if hasattr(self.dut, 'fub_arready'):
                arready_ok = not bool(self.dut.fub_arready.value)
                ready_checks.append(('fub_arready', arready_ok))
                
            if hasattr(self.dut, 'm_axil_rready'):
                rready_ok = not bool(self.dut.m_axil_rready.value)
                ready_checks.append(('m_axil_rready', rready_ok))
                
            all_ready_ok = all(check[1] for check in ready_checks)
            
            if not all_ready_ok:
                failed_signals = [check[0] for check in ready_checks if not check[1]]
                self.log.error(f"Ready signals not 0 during gating: {failed_signals}")
                
            return all_ready_ok
            
        return True

    async def test_functional_equivalence(self, test_function, *args, **kwargs):
        """Test that CG and non-CG versions produce identical results."""
        self.log.info("=== Testing Functional Equivalence ===")
        
        # Test with clock gating disabled
        await self.configure_clock_gating(enable=False)
        await Timer(100, 'ns')
        
        try:
            result_no_cg = await test_function(*args, **kwargs)
        except Exception as e:
            self.log.error(f"Test failed with CG disabled: {e}")
            return False
            
        # Test with clock gating enabled
        await self.configure_clock_gating(enable=True, idle_count=4)
        await Timer(100, 'ns')
        
        try:
            result_with_cg = await test_function(*args, **kwargs)
        except Exception as e:
            self.log.error(f"Test failed with CG enabled: {e}")
            return False
            
        # Compare results (simple comparison - can be enhanced)
        equivalence = (result_no_cg == result_with_cg)
        
        if equivalence:
            self.log.info("Functional equivalence validated")
        else:
            self.log.error("Functional equivalence validation failed")
            self.log.error(f"No CG result: {result_no_cg}")
            self.log.error(f"With CG result: {result_with_cg}")
            
        return equivalence


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def axil4_master_read_cg_test(dut):
    """AXIL4 master read clock gated test using the enhanced framework"""

    # Create clock-gated testbench instance
    tb = AXIL4MasterReadCGTB(dut, aclk=dut.aclk, aresetn=dut.aresetn)

    # Use seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'AXIL4 master read CG test with seed: {seed}')

    # Get test parameters
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()
    cg_test_mode = os.environ.get('CG_TEST_MODE', 'comprehensive').lower()  # comprehensive, basic, efficiency
    
    valid_levels = ['basic', 'medium', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'basic'")
        test_level = 'basic'

    # Start clock and reset
    await tb.start_clock('aclk', tb.TEST_CLK_PERIOD, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('aclk', 10)
    await tb.deassert_reset()
    await tb.wait_clocks('aclk', 10)

    tb.log.info("=" * 80)
    tb.log.info(f"AXIL4 MASTER READ CLOCK GATED TEST - {test_level.upper()} LEVEL")
    tb.log.info("=" * 80)
    tb.log.info(f"CG Test Mode: {cg_test_mode.upper()}")
    tb.log.info(f"AXIL4 widths: ADDR={tb.TEST_ADDR_WIDTH}, DATA={tb.TEST_DATA_WIDTH}")

    try:
        # Test configurations based on test level
        if test_level == 'basic':
            idle_counts = [4, 8]
            test_transactions = 10
            power_measurement_cycles = 500
        elif test_level == 'medium':
            idle_counts = [2, 4, 8, 16]
            test_transactions = 25
            power_measurement_cycles = 1000
        else:  # full
            idle_counts = [1, 2, 4, 8, 16, 32]
            test_transactions = 50
            power_measurement_cycles = 2000

        total_tests = 0
        passed_tests = 0
        power_efficiency_results = []

        # === COMPREHENSIVE CLOCK GATING TESTS ===
        if cg_test_mode in ['comprehensive', 'basic'] or test_level != 'efficiency':
            
            # Test 1: Functional Equivalence Validation
            tb.log.info("=== Test 1: Functional Equivalence ===")
            
            async def basic_read_test():
                """Basic read test for equivalence comparison."""
                tb.set_timing_profile('normal')
                results = []
                for i in range(5):
                    address = 0x1000 + (i * (tb.TEST_DATA_WIDTH // 8))
                    success, data, info = await tb.register_read_test(address)
                    results.append((success, data))
                return results
                
            equivalence_ok = await tb.test_functional_equivalence(basic_read_test)
            total_tests += 1
            if equivalence_ok:
                passed_tests += 1

            # Test 2: Clock Gating Behavior with Different Idle Counts
            tb.log.info("=== Test 2: Clock Gating Behavior ===")
            
            for idle_count in idle_counts:
                tb.log.info(f"Testing with idle_count = {idle_count}")
                await tb.configure_clock_gating(enable=True, idle_count=idle_count)
                
                # Perform some reads with idle periods
                tb.set_timing_profile('normal')
                read_success = 0
                
                for i in range(5):
                    address = 0x2000 + (i * (tb.TEST_DATA_WIDTH // 8))
                    success, data, info = await tb.register_read_test(address)
                    if success:
                        read_success += 1
                        
                    # Add idle time to trigger gating
                    await tb.wait_clocks('aclk', idle_count + 5)
                    
                # Check ready signals during potential gating
                ready_signals_ok = await tb.validate_ready_signals_during_gating()
                
                total_tests += 1
                if read_success == 5 and ready_signals_ok:
                    passed_tests += 1
                    tb.log.info(f"Idle count {idle_count}: All reads successful, ready signals OK")
                else:
                    tb.log.error(f"Idle count {idle_count}: {read_success}/5 reads successful, ready signals: {ready_signals_ok}")

            # Test 3: Gating Transition Validation
            tb.log.info("=== Test 3: Gating Transitions ===")
            await tb.configure_clock_gating(enable=True, idle_count=2)
            
            # Force idle to trigger gating
            await tb.wait_clocks('aclk', 10)
            gating_achieved = await tb.wait_for_gating_state(target_state=True, timeout_cycles=20)
            
            if gating_achieved:
                # Resume activity and check ungating
                tb.set_timing_profile('fast')
                success, data, info = await tb.register_read_test(0x3000)
                ungating_achieved = await tb.wait_for_gating_state(target_state=False, timeout_cycles=10)
                
                total_tests += 1
                if success and ungating_achieved:
                    passed_tests += 1
                    tb.log.info("Gating transitions working correctly")
                else:
                    tb.log.error(f"Gating transition issues: read_success={success}, ungating={ungating_achieved}")
            else:
                total_tests += 1
                tb.log.warning("Could not achieve gated state for transition testing")

            # Test 4: Power Efficiency Measurement
            tb.log.info("=== Test 4: Power Efficiency Measurement ===")
            
            for idle_count in [4, 8]:
                await tb.configure_clock_gating(enable=True, idle_count=idle_count)
                
                # Start power measurement
                efficiency_task = tb.measure_power_efficiency(power_measurement_cycles)
                
                # Perform reads during measurement with realistic traffic
                read_count = 0
                for cycle in range(0, power_measurement_cycles, 50):  # Read every 50 cycles
                    if cycle + 20 < power_measurement_cycles:  # Ensure we don't exceed measurement period
                        address = 0x4000 + (read_count * (tb.TEST_DATA_WIDTH // 8))
                        success, data, info = await tb.register_read_test(address)
                        read_count += 1
                        
                        # Add some idle time between reads
                        await tb.wait_clocks('aclk', 15)
                        
                # Get efficiency results
                efficiency_stats = await efficiency_task
                power_efficiency_results.append({
                    'idle_count': idle_count,
                    'efficiency_percent': efficiency_stats.get('power_efficiency_percent', 0),
                    'gating_transitions': efficiency_stats.get('gating_transitions', 0)
                })
                
                tb.log.info(f"Idle count {idle_count}: {efficiency_stats.get('power_efficiency_percent', 0):.1f}% power efficiency")

        # === STRESS TESTING ===
        if test_level == 'full':
            tb.log.info("=== Test 5: Stress Testing ===")
            await tb.configure_clock_gating(enable=True, idle_count=1)  # Aggressive gating
            
            # Rapid gating/ungating cycles
            stress_success = 0
            for i in range(20):
                success, data, info = await tb.register_read_test(0x5000 + (i * (tb.TEST_DATA_WIDTH // 8)))
                if success:
                    stress_success += 1
                    
                # Very short idle to cause frequent gating
                await tb.wait_clocks('aclk', 3)
                
            total_tests += 1
            if stress_success >= 18:  # Allow some margin for stress test
                passed_tests += 1
                tb.log.info(f"Stress test: {stress_success}/20 reads successful")
            else:
                tb.log.error(f"Stress test: {stress_success}/20 reads successful")

        # === FINAL RESULTS ===
        tb.log.info("=" * 80)
        tb.log.info("CLOCK GATED AXIL4 MASTER READ TEST SUMMARY")
        tb.log.info("=" * 80)
        
        success_rate = (passed_tests / total_tests * 100) if total_tests > 0 else 0
        tb.log.info(f"Tests passed:           {passed_tests}/{total_tests}")
        tb.log.info(f"Success rate:           {success_rate:.1f}%")
        tb.log.info(f"Test level:             {test_level.upper()}")
        
        if power_efficiency_results:
            tb.log.info("Power Efficiency Results:")
            for result in power_efficiency_results:
                tb.log.info(f"  Idle count {result['idle_count']}: {result['efficiency_percent']:.1f}% efficiency")
                
        if success_rate < 90:
            tb.log.error("AXIL4 MASTER READ CG TEST FAILED")
            raise Exception(f"Clock gated test failed with {success_rate:.1f}% success rate")
            
        tb.log.info("AXIL4 MASTER READ CG TEST PASSED")

    except Exception as e:
        tb.log.error(f"AXIL4 master read CG test FAILED with exception: {str(e)}")
        raise


def generate_axil4_cg_params():
    """Generate test parameters for clock-gated AXIL4 master read testing"""
    
    # Clock gated modules only test with RTL (no stub version)
    addr_widths = [32, 64]
    data_widths = [32, 64]
    ar_depths = [2, 4]
    r_depths = [2, 4]
    test_levels = ['basic', 'medium', 'full']
    cg_test_modes = ['comprehensive', 'efficiency']
    
    # Debug mode for quick testing
    debug_mode = True
    if debug_mode:
        return [
            (32, 32, 2, 4, 'full', 'comprehensive'),
            # (32, 32, 2, 4, 'basic', 'efficiency'),
        ]
    
    return list(product(addr_widths, data_widths, ar_depths, r_depths, test_levels, cg_test_modes))


@pytest.mark.parametrize("addr_width, data_width, ar_depth, r_depth, test_level, cg_test_mode",
                        generate_axil4_cg_params())
def test_axil4_master_read_cg(addr_width, data_width, ar_depth, r_depth, test_level, cg_test_mode):
    """Test AXIL4 master read clock gated with specified parameters"""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_axil4': 'rtl/amba/axil4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_shared': 'rtl/amba/shared',
     'rtl_amba_includes': 'rtl/amba/includes'})

    # Clock gated module details
    dut_name = "axil4_master_rd_cg"
    
    # Create unique test name
    test_name_plus_params = f"test_{worker_id}_{dut_name}_a{addr_width}_d{data_width}_ar{ar_depth}_r{r_depth}_{test_level}_{cg_test_mode}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL files for clock gated master read
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "icg.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "clock_gate_ctrl.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'], "amba_clock_gate_ctrl.sv"),  # Clock gate controller
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axil4'], "axil4_master_rd.sv"),  # Base module
        os.path.join(rtl_dict['rtl_axil4'], f"{dut_name}.sv"),
    ]

    # Check that files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # Parameters for the DUT
    rtl_parameters = {
        'AXIL_ADDR_WIDTH': addr_width,
        'AXIL_DATA_WIDTH': data_width,
        'SKID_DEPTH_AR': ar_depth,
        'SKID_DEPTH_R': r_depth,
        'CG_IDLE_COUNT_WIDTH': 8
    }

    # Calculate timeout based on complexity
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    complexity_factor = (data_width + addr_width) / 100.0
    timeout_ms = int(5000 * timeout_multipliers.get(test_level, 1) * max(1.0, complexity_factor))

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),
        'TEST_ADDR_WIDTH': str(addr_width), 
        'TEST_DATA_WIDTH': str(data_width),
        'SKID_DEPTH_AR': str(ar_depth),
        'SKID_DEPTH_R': str(r_depth),
        'CG_TEST_MODE': cg_test_mode,
        'CG_IDLE_COUNT_WIDTH': '8',  # Default width for idle count
        'AXIL4_COMPLIANCE_CHECK': '1',
    }

    # Simulation settings
    includes = [rtl_dict['rtl_amba_includes']]
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "-Wall", "-Wno-SYNCASYNCNET",
        "-Wno-UNUSED",
        "-Wno-DECLFILENAME",
        "-Wno-PINMISSING",  # Allow unconnected pins
    ]
    sim_args = ["--trace", "--trace-depth", "99"]
    plusargs = ["--trace"]

    # Create command file for viewing results
    cmd_filename = create_view_cmd(os.path.dirname(log_path), log_path, sim_build,
                                    module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} AXIL4 Master Read Clock Gated test: {dut_name}")
    print(f"AXIL4 Config: ADDR={addr_width}, DATA={data_width}")
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
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ {test_level.upper()} AXIL4 Master Read Clock Gated test PASSED")
    except Exception as e:
        print(f"✗ {test_level.upper()} AXIL4 Master Read Clock Gated test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise


if __name__ == "__main__":
    # Can run individual tests or use pytest
    pytest.main([__file__, "-v", "-s"])