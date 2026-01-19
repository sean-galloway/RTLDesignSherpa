# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI5MasterWriteCGTB
# Purpose: AXI5 Master Write Clock Gated Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-12-20

"""
AXI5 Master Write Clock Gated Test Runner

Test runner for the axi5_master_wr_cg module using the CocoTB framework.
Tests clock gating functionality while validating write transactions.
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args
from cocotb.triggers import RisingEdge, Timer

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.amba.amba_cg_ctrl import AxiClockGateCtrl
from CocoTBFramework.tbclasses.axi5.axi5_master_write_tb import AXI5MasterWriteTB


class AXI5MasterWriteCGTB(AXI5MasterWriteTB):
    """
    Clock-gated AXI5 Master Write testbench.
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

        await self.wait_clocks('aclk', 5)
        self.log.info(f"Clock gating configured: enable={enable}, idle_count={idle_count}")

    async def wait_for_gating_state(self, target_state=True, timeout_cycles=100):
        """Wait for specific gating state."""
        if not hasattr(self.dut, 'cg_gating'):
            return True

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


@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axi5_master_write_cg_test(dut):
    """AXI5 master write clock gated test"""

    tb = AXI5MasterWriteCGTB(dut, aclk=dut.aclk, aresetn=dut.aresetn)

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'AXI5 master write CG test with seed: {seed}')

    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    await tb.start_clock('aclk', tb.TEST_CLK_PERIOD, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('aclk', 10)
    await tb.deassert_reset()
    await tb.wait_clocks('aclk', 10)

    tb.log.info("=" * 80)
    tb.log.info(f"AXI5 MASTER WRITE CLOCK GATED TEST - {test_level.upper()} LEVEL")
    tb.log.info("=" * 80)

    try:
        if test_level == 'basic':
            idle_counts = [4, 8]
            test_transactions = 10
        elif test_level == 'medium':
            idle_counts = [2, 4, 8, 16]
            test_transactions = 25
        else:
            idle_counts = [1, 2, 4, 8, 16, 32]
            test_transactions = 50

        total_tests = 0
        passed_tests = 0

        # Test with clock gating disabled first
        tb.log.info("=== Test 1: Functional Equivalence ===")
        await tb.configure_clock_gating(enable=False)
        await Timer(100, 'ns')

        tb.set_timing_profile('normal')
        for i in range(5):
            address = 0x1000 + (i * 4)
            data = random.randint(0, tb.MAX_DATA)
            success, info = await tb.single_write_test(address, data)
            if success:
                passed_tests += 1
            total_tests += 1

        # Test with clock gating enabled
        await tb.configure_clock_gating(enable=True, idle_count=4)
        await Timer(100, 'ns')

        for i in range(5):
            address = 0x2000 + (i * 4)
            data = random.randint(0, tb.MAX_DATA)
            success, info = await tb.single_write_test(address, data)
            if success:
                passed_tests += 1
            total_tests += 1

        # Test clock gating behavior with different idle counts
        tb.log.info("=== Test 2: Clock Gating Behavior ===")
        for idle_count in idle_counts:
            tb.log.info(f"Testing with idle_count = {idle_count}")
            await tb.configure_clock_gating(enable=True, idle_count=idle_count)

            for i in range(3):
                address = 0x3000 + (i * 4)
                data = random.randint(0, tb.MAX_DATA)
                success, info = await tb.single_write_test(address, data)
                if success:
                    passed_tests += 1
                total_tests += 1
                await tb.wait_clocks('aclk', idle_count + 5)

        success_rate = (passed_tests / total_tests * 100) if total_tests > 0 else 0

        tb.log.info("=" * 80)
        tb.log.info("AXI5 MASTER WRITE CG TEST SUMMARY")
        tb.log.info("=" * 80)
        tb.log.info(f"Tests passed: {passed_tests}/{total_tests}")
        tb.log.info(f"Success rate: {success_rate:.1f}%")

        if success_rate < 90:
            raise Exception(f"Clock gated test failed with {success_rate:.1f}% success rate")

        tb.log.info("AXI5 MASTER WRITE CG TEST PASSED")

    except Exception as e:
        tb.log.error(f"AXI5 master write CG test FAILED: {str(e)}")
        raise


def generate_axi5_cg_params():
    """Generate AXI5 CG parameter combinations based on REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        params = [(8, 32, 32, 1, 2, 4, 2, 'basic')]
    elif reg_level == 'FUNC':
        params = [
            (8, 32, 32, 1, 2, 4, 2, 'basic'),
            (8, 32, 32, 1, 4, 8, 4, 'medium'),
            (8, 64, 64, 1, 2, 4, 2, 'medium'),
        ]
    else:  # FULL
        test_levels = ['basic', 'medium', 'full']
        configs = [(8, 32, 32, 1, 2, 4, 2), (8, 32, 32, 1, 4, 8, 4), (8, 64, 64, 1, 2, 4, 2)]
        params = [
            (id_w, addr_w, data_w, user_w, aw_d, w_d, b_d, level)
            for (id_w, addr_w, data_w, user_w, aw_d, w_d, b_d) in configs
            for level in test_levels
        ]

    return params


@pytest.mark.parametrize(
    "id_width, addr_width, data_width, user_width, aw_depth, w_depth, b_depth, test_level",
    generate_axi5_cg_params()
)
def test_axi5_master_wr_cg(id_width, addr_width, data_width, user_width, aw_depth, w_depth, b_depth, test_level):
    """Test AXI5 master write clock gated with specified parameters"""

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_axi5': 'rtl/amba/axi5/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_shared': 'rtl/amba/shared',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    dut_name = "axi5_master_wr_cg"
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name = f"test_{worker_id}_{dut_name}_iw{id_width}_aw{addr_width}_dw{data_width}_awd{aw_depth}_wd{w_depth}_bd{b_depth}_{test_level}_{reg_level}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "icg.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "clock_gate_ctrl.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'], "amba_clock_gate_ctrl.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axi5'], "axi5_master_wr.sv"),
        os.path.join(rtl_dict['rtl_axi5'], f"{dut_name}.sv"),
    ]

    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    rtl_parameters = {
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': str(user_width),
        'SKID_DEPTH_AW': str(aw_depth),
        'SKID_DEPTH_W': str(w_depth),
        'SKID_DEPTH_B': str(b_depth),
        'CG_IDLE_COUNT_WIDTH': '8'
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_LEVEL': test_level,
        'TEST_ID_WIDTH': str(id_width),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_USER_WIDTH': str(user_width),
        'TEST_STUB': '0',
        'SEED': str(random.randint(0, 100000)),
        'TEST_CLK_PERIOD': '10',
    }

    compile_args = [
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED", "-Wno-DECLFILENAME", "-Wno-PINMISSING",
        "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC",
        "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE", "-Wno-TIMESCALEMOD",
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    print(f"\n{'='*80}")
    print(f"AXI5 Master Write CG Test")
    print(f"Test Level: {test_level}")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_amba_includes'], rtl_dict['rtl_cmn'], sim_build],
            toplevel=dut_name,
            module="test_axi5_master_wr_cg",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            simulator="verilator",
        )
        print(f"PASSED: {test_name}")
    except Exception as e:
        print(f"FAILED: {test_name}")
        print(f"Error: {str(e)}")
        raise
