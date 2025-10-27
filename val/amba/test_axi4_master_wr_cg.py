# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI4MasterWriteCGTB
# Purpose: AXI4 Master Write Clock Gated Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Master Write Clock Gated Test Runner

Test runner for the axi4_master_wr_cg module using the CocoTB framework.
Tests clock gating functionality while validating write transactions.

Based on the standard AXI4 test runner pattern but enhanced for clock gating validation.
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
from CocoTBFramework.tbclasses.axi4.axi4_master_write_tb import AXI4MasterWriteTB


class AXI4MasterWriteCGTB(AXI4MasterWriteTB):
    """
    Clock-gated AXI4 Master Write testbench.
    Extends the base master write testbench with clock gating capabilities.
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
                user_valid_signals=["fub_axi_awvalid", "fub_axi_wvalid", "fub_axi_bready"],
                axi_valid_signals=["m_axi_awvalid", "m_axi_wvalid", "m_axi_bvalid"],
                gating_signal_name="cg_gating",
                idle_signal_name="cg_idle",
                enable_signal_name="cfg_cg_enable",
                idle_count_signal_name="cfg_cg_idle_count"
            )
            self.log.info("✅ Clock gating controller initialized")
        except Exception as e:
            self.log.warning(f"Could not initialize CG controller: {e}")

    async def configure_clock_gating(self, enable=True, idle_count=8):
        """Configure clock gating parameters."""
        # Set DUT configuration signals directly
        if hasattr(self.dut, 'cfg_cg_enable'):
            self.dut.cfg_cg_enable.value = 1 if enable else 0
        if hasattr(self.dut, 'cfg_cg_idle_count'):
            self.dut.cfg_cg_idle_count.value = idle_count
            
        if self.cg_ctrl:
            self.cg_ctrl.enable_clock_gating(enable)
            self.cg_ctrl.set_idle_count(idle_count)
            
        await self.wait_clocks('aclk', 5)  # Let configuration settle
        self.log.info(f"Clock gating configured: enable={enable}, idle_count={idle_count}")

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

    async def functional_equivalence_test(self, test_iterations=10):
        """Test functional equivalence between gated and non-gated operation."""
        results = {'gated': [], 'non_gated': []}
        
        # Test with clock gating enabled
        await self.configure_clock_gating(enable=True, idle_count=4)
        for i in range(test_iterations):
            addr = 0x1000 + (i * 8)
            data = 0xDEADBEEF + i
            success, response = await self.single_write_test(addr, data)
            results['gated'].append((success, response))

        # Test with clock gating disabled
        await self.configure_clock_gating(enable=False, idle_count=0)
        for i in range(test_iterations):
            addr = 0x1000 + (i * 8)
            data = 0xDEADBEEF + i
            success, response = await self.single_write_test(addr, data)
            results['non_gated'].append((success, response))

        # Compare results
        equivalence = all(g[0] == ng[0] for g, ng in zip(results['gated'], results['non_gated']))
        return equivalence, results


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def axi4_master_write_cg_test(dut):
    """AXI4 master write clock gated test using the enhanced framework"""

    # Create clock-gated testbench instance
    tb = AXI4MasterWriteCGTB(dut, aclk=dut.aclk, aresetn=dut.aresetn)

    # Use seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'AXI4 master write CG test with seed: {seed}')

    # Get test parameters
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()
    cg_test_mode = os.environ.get('CG_TEST_MODE', 'comprehensive').lower()
    
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
    tb.log.info(f"AXI4 MASTER WRITE CLOCK GATED TEST - {test_level.upper()} LEVEL")
    tb.log.info("=" * 80)
    tb.log.info(f"CG Test Mode: {cg_test_mode.upper()}")
    tb.log.info(f"AXI4 widths: ID={tb.TEST_ID_WIDTH}, ADDR={tb.TEST_ADDR_WIDTH}, DATA={tb.TEST_DATA_WIDTH}")

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
        if cg_test_mode in ['comprehensive', 'basic']:
            
            # Test 1: Functional Equivalence Validation
            tb.log.info("=== Test 1: Functional Equivalence ===")
            
            equivalence, results = await tb.functional_equivalence_test(test_iterations=test_transactions)
            total_tests += 1
            if equivalence:
                passed_tests += 1
                tb.log.info("✅ Functional equivalence: PASS")
            else:
                tb.log.error("❌ Functional equivalence: FAIL")

            # Test 2: Clock Gating Efficiency at Different Idle Counts
            tb.log.info("=== Test 2: Power Efficiency Testing ===")
            
            for idle_count in idle_counts:
                tb.log.info(f"Testing idle count: {idle_count}")
                await tb.configure_clock_gating(enable=True, idle_count=idle_count)
                
                # Generate some activity then measure efficiency
                for i in range(5):
                    addr = 0x2000 + (i * 8)
                    data = 0xCAFEBABE + i
                    await tb.single_write_test(addr, data)
                    await tb.wait_clocks('aclk', idle_count * 2)  # Create idle periods

                efficiency_result = await tb.measure_power_efficiency(power_measurement_cycles)
                power_efficiency_results.append({
                    'idle_count': idle_count,
                    'efficiency_percent': efficiency_result['power_efficiency_percent'],
                    'gated_cycles': efficiency_result['gated_cycles']
                })
                
                total_tests += 1
                if efficiency_result['power_efficiency_percent'] > 10.0:  # Reasonable threshold
                    passed_tests += 1
                    tb.log.info(f"✅ Efficiency test (idle={idle_count}): {efficiency_result['power_efficiency_percent']:.1f}%")
                else:
                    tb.log.warning(f"⚠️ Low efficiency (idle={idle_count}): {efficiency_result['power_efficiency_percent']:.1f}%")

            # Test 3: Clock Gating Disable/Enable Transitions
            tb.log.info("=== Test 3: Enable/Disable Transitions ===")
            
            transition_success = 0
            for i in range(5):
                # Test enable transition
                await tb.configure_clock_gating(enable=True, idle_count=8)
                addr = 0x3000 + (i * 8)
                success1, _ = await tb.single_write_test(addr, 0x12345678 + i)
                
                # Test disable transition
                await tb.configure_clock_gating(enable=False, idle_count=0)
                success2, _ = await tb.single_write_test(addr + 4, 0x87654321 + i)
                
                if success1 and success2:
                    transition_success += 1

            total_tests += 1
            if transition_success >= 4:  # Allow one failure
                passed_tests += 1
                tb.log.info(f"✅ Transition test: {transition_success}/5 successful")
            else:
                tb.log.error(f"❌ Transition test: {transition_success}/5 successful")

        # === EFFICIENCY-FOCUSED TESTS ===
        if cg_test_mode in ['efficiency']:
            tb.log.info("=== Efficiency Mode: Extended Power Testing ===")
            
            # Extended efficiency measurement with optimal idle count
            optimal_idle_count = 8
            await tb.configure_clock_gating(enable=True, idle_count=optimal_idle_count)
            
            # Run extended test
            for i in range(test_transactions):
                addr = 0x4000 + (i * 8)
                data = 0xCAFEDADA + i
                await tb.single_write_test(addr, data)
                await tb.wait_clocks('aclk', random.randint(1, optimal_idle_count * 2))

            efficiency_result = await tb.measure_power_efficiency(power_measurement_cycles * 2)
            power_efficiency_results.append({
                'idle_count': optimal_idle_count,
                'efficiency_percent': efficiency_result['power_efficiency_percent'],
                'gated_cycles': efficiency_result['gated_cycles']
            })
            
            total_tests += 1
            if efficiency_result['power_efficiency_percent'] > 15.0:  # Higher threshold for efficiency mode
                passed_tests += 1
                tb.log.info(f"✅ Extended efficiency: {efficiency_result['power_efficiency_percent']:.1f}%")
            else:
                tb.log.warning(f"⚠️ Extended efficiency: {efficiency_result['power_efficiency_percent']:.1f}%")

        # Test 4: Stress Testing (medium and full levels)
        if test_level in ['medium', 'full']:
            tb.log.info("=== Test 4: Clock Gated Stress Testing ===")
            
            await tb.configure_clock_gating(enable=True, idle_count=4)
            stress_success = 0
            for i in range(20):
                addr = 0x5000 + (i * 8)
                data = 0xDADACAFE + i if i < 16 else 0x5000000 + i  # Fix hex literal
                success, _ = await tb.single_write_test(addr, data)
                if success:
                    stress_success += 1
                await tb.wait_clocks('aclk', random.randint(1, 8))

            total_tests += 1
            if stress_success >= 18:  # Allow couple failures in stress test
                passed_tests += 1
                tb.log.info(f"✅ Stress test: {stress_success}/20 successful")
            else:
                tb.log.error(f"❌ Stress test: {stress_success}/20 successful")

        # === FINAL RESULTS ===
        tb.log.info("=" * 80)
        tb.log.info("CLOCK GATED AXI4 MASTER WRITE TEST SUMMARY")
        tb.log.info("=" * 80)
        tb.finalize_test()
        success_rate = (passed_tests / total_tests * 100) if total_tests > 0 else 0
        tb.log.info(f"Tests passed:           {passed_tests}/{total_tests}")
        tb.log.info(f"Success rate:           {success_rate:.1f}%")
        tb.log.info(f"Test level:             {test_level.upper()}")
        
        if power_efficiency_results:
            tb.log.info("Power Efficiency Results:")
            for result in power_efficiency_results:
                tb.log.info(f"  Idle count {result['idle_count']}: {result['efficiency_percent']:.1f}% efficiency")
                
        if success_rate < 90:
            tb.log.error("❌ AXI4 MASTER WRITE CG TEST FAILED")
            raise Exception(f"Clock gated test failed with {success_rate:.1f}% success rate")
            
        tb.log.info("✅ AXI4 MASTER WRITE CG TEST PASSED")

    except Exception as e:
        tb.log.error(f"AXI4 master write CG test FAILED with exception: {str(e)}")
        raise


def generate_axi4_cg_params():
    """Generate test parameters for clock-gated AXI4 master write testing"""
    
    # Clock gated modules only test with RTL (no stub version)
    id_widths = [4, 8]
    addr_widths = [32, 64]
    data_widths = [32, 64]
    user_widths = [1]
    aw_depths = [2, 4]
    w_depths = [2, 4]
    b_depths = [2, 4]
    test_levels = ['basic', 'medium', 'full']
    cg_test_modes = ['comprehensive', 'efficiency']
    
    # Debug mode for quick testing
    debug_mode = True
    if debug_mode:
        return [
            (8, 32, 32, 1, 2, 4, 2, 'full', 'comprehensive'),
            # (8, 32, 32, 1, 2, 4, 2, 'basic', 'efficiency'),
        ]
    
    return list(product(id_widths, addr_widths, data_widths, user_widths,
                        aw_depths, w_depths, b_depths, test_levels, cg_test_modes))


@pytest.mark.parametrize("id_width, addr_width, data_width, user_width, aw_depth, w_depth, b_depth, test_level, cg_test_mode",
                        generate_axi4_cg_params())
def test_axi4_master_write_cg(id_width, addr_width, data_width, user_width, aw_depth, w_depth, b_depth, test_level, cg_test_mode):
    """Test AXI4 master write clock gated with specified parameters"""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':  'rtl/common',
        'rtl_axi4': 'rtl/amba/axi4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_shared':'rtl/amba/shared',
     'rtl_amba_includes': 'rtl/amba/includes'})

    # Clock gated module details
    dut_name = "axi4_master_wr_cg"
    
    # Format parameters with leading zeros for consistent sorting
    id_str = f"id{id_width:03d}_aw{addr_width:03d}_dw{data_width:03d}_uw{user_width:03d}_awd{aw_depth:03d}_wd{w_depth:03d}_bd{b_depth:03d}_{test_level}_{cg_test_mode}"
    # Create unique test name following pattern: test_<module>_<params>
    test_name_plus_params = f"test_{worker_id}_axi4_master_wr_cg_{id_str}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL files for clock gated master write
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "icg.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "clock_gate_ctrl.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'], "amba_clock_gate_ctrl.sv"),  # Clock gate controller
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axi4'], "axi4_master_wr.sv"),  # Base module
        os.path.join(rtl_dict['rtl_axi4'], f"{dut_name}.sv"),
    ]

    # Check that files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # Parameters for the DUT
    rtl_parameters = {
        'AXI_ID_WIDTH': id_width,
        'AXI_ADDR_WIDTH': addr_width,
        'AXI_DATA_WIDTH': data_width,
        'AXI_USER_WIDTH': user_width,
        'SKID_DEPTH_AW': aw_depth,
        'SKID_DEPTH_W': w_depth,
        'SKID_DEPTH_B': b_depth,
        'CG_IDLE_COUNT_WIDTH': 8
    }

    # Calculate timeout based on complexity
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    complexity_factor = (data_width + addr_width + id_width) / 100.0
    timeout_ms = int(5000 * timeout_multipliers.get(test_level, 1) * max(1.0, complexity_factor))

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(4347), # str(random.randint(0, 100000)),

        'TEST_LEVEL': test_level,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),
        'TEST_ID_WIDTH': str(id_width),
        'TEST_ADDR_WIDTH': str(addr_width), 
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_USER_WIDTH': str(user_width),
        'SKID_DEPTH_AW': str(aw_depth),
        'SKID_DEPTH_W': str(w_depth),
        'SKID_DEPTH_B': str(b_depth),
        'TEST_LEVEL': test_level,
        'CG_TEST_MODE': cg_test_mode,
        'CG_IDLE_COUNT_WIDTH': '8',  # Default width for idle count
        'SEED': str(random.randint(1, 1000000)),
        'AXI4_COMPLIANCE_CHECK': '1',
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
        "-Wno-PINMISSING",  # Allow unconnected pins for stub testing
    ]
    sim_args = ["--trace", "--trace-depth", "99"]
    plusargs = ["--trace"]

    # Create command file for viewing results
    cmd_filename = create_view_cmd(os.path.dirname(log_path), log_path, sim_build,
                                    module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} AXI4 Master Write CG test: {dut_name}")
    print(f"AXI4 Config: ID={id_width}, ADDR={addr_width}, DATA={data_width}, USER={user_width}")
    print(f"Buffer Depths: AW={aw_depth}, W={w_depth}, B={b_depth}")
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
        print(f"✓ {test_level.upper()} AXI4 Master Write CG test PASSED")
    except Exception as e:
        print(f"✗ {test_level.upper()} AXI4 Master Write CG test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise


if __name__ == "__main__":
    # Can run individual tests or use pytest
    pytest.main([__file__, "-v", "-s"])
