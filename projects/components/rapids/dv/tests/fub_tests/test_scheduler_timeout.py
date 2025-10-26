# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: TimeoutTB
# Purpose: RAPIDS Scheduler Timeout Detection Test - Standalone Simple Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Scheduler Timeout Detection Test - Standalone Simple Test

This is a specialized test for timeout detection that does NOT use GAXI infrastructure.
The timeout detection requires sustained backpressure (data_valid=1 && data_ready=0)
which cannot be created with GAXI's automatic ready signal management.

This test uses bare-metal signal control for simplicity and direct RTL interaction.
"""

import os
import sys
import pytest
import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase


# ===========================================================================
# SIMPLE TIMEOUT TESTBENCH - NO GAXI
# ===========================================================================

class TimeoutTB:
    """Minimal testbench for timeout detection - no GAXI infrastructure"""

    def __init__(self, dut):
        self.dut = dut
        self.clk = dut.clk

    async def setup(self):
        """Setup clock and reset"""
        # Start clock
        cocotb.start_soon(Clock(self.clk, 10, units="ns").start())

        # Configure before reset
        self.dut.cfg_initial_credit.value = 4  # 16 credits
        self.dut.cfg_use_credit.value = 1
        self.dut.cfg_idle_mode.value = 0
        self.dut.cfg_channel_wait.value = 0
        self.dut.cfg_channel_enable.value = 1
        self.dut.cfg_channel_reset.value = 0

        # Reset
        self.dut.rst_n.value = 0
        await Timer(100, units="ns")
        self.dut.rst_n.value = 1
        await Timer(50, units="ns")

        # Initialize all inputs to safe defaults
        self.dut.descriptor_valid.value = 0
        self.dut.descriptor_packet.value = 0
        self.dut.descriptor_same.value = 0
        self.dut.descriptor_error.value = 0
        self.dut.descriptor_is_rda.value = 0
        self.dut.descriptor_rda_channel.value = 0
        self.dut.descriptor_eos.value = 0
        self.dut.descriptor_eol.value = 0
        self.dut.descriptor_eod.value = 0
        self.dut.descriptor_type.value = 0

        # Data engine interface - CRITICAL: Start with ready=1
        self.dut.data_ready.value = 1
        self.dut.data_transfer_length.value = 0
        self.dut.data_error.value = 0
        self.dut.data_done_strobe.value = 0

        # Alignment bus
        self.dut.data_alignment_ready.value = 1
        self.dut.data_alignment_next.value = 0

        # Other interfaces
        self.dut.eos_completion_ready.value = 1
        # Standalone scheduler has ctrlwr_* and ctrlrd_* interfaces (not program_*)
        self.dut.ctrlwr_ready.value = 1
        self.dut.ctrlwr_error.value = 0
        self.dut.ctrlrd_ready.value = 1
        self.dut.ctrlrd_error.value = 0
        self.dut.ctrlrd_result.value = 0
        self.dut.rda_complete_ready.value = 1
        self.dut.mon_ready.value = 1
        self.dut.credit_increment.value = 0

        await Timer(50, units="ns")

    async def send_descriptor(self, data_addr, data_length):
        """Send a descriptor to the scheduler"""
        # Create descriptor packet
        descriptor = 0
        descriptor |= (data_addr & 0xFFFFFFFFFFFFFFFF) << 32  # Data address [95:32]
        descriptor |= (data_length & 0xFFFFFFFF)              # Data length [31:0]
        descriptor |= ((data_addr + 0x40) & 0xFFFFFFFFFFFFFFFF) << 96  # Next descriptor [159:96]

        # Wait for ready
        for _ in range(100):
            await RisingEdge(self.clk)
            if int(self.dut.descriptor_ready.value) == 1:
                break

        # Send descriptor
        self.dut.descriptor_valid.value = 1
        self.dut.descriptor_packet.value = descriptor
        self.dut.descriptor_type.value = 1
        await RisingEdge(self.clk)

        # Wait for acceptance
        for _ in range(50):
            await RisingEdge(self.clk)
            if int(self.dut.descriptor_ready.value) == 0:
                break

        # Clear descriptor signals
        self.dut.descriptor_valid.value = 0
        self.dut.descriptor_packet.value = 0
        await RisingEdge(self.clk)

    async def test_timeout(self):
        """Test timeout detection with sustained backpressure"""
        print("\n=== Testing Timeout Detection ===")

        # Send descriptor
        await self.send_descriptor(data_addr=0x9000, data_length=0x100)
        print("  Descriptor sent")

        # Wait for scheduler to assert data_valid
        for cycle in range(50):
            await RisingEdge(self.clk)
            if int(self.dut.data_valid.value) == 1:
                print(f"  data_valid asserted after {cycle} cycles")
                break

        if int(self.dut.data_valid.value) != 1:
            print("  ❌ ERROR: Scheduler never asserted data_valid")
            return False

        # Now create sustained backpressure by forcing data_ready=0
        # This must be done EVERY cycle to override any other drivers
        print("  Creating sustained backpressure (data_ready=0) for 1100 cycles...")

        timeout_counter = 0
        backpressure_warning = 0

        for cycle in range(1100):
            self.dut.data_ready.value = 0  # Force LOW every single cycle
            await RisingEdge(self.clk)

            # Sample periodically to verify condition
            if cycle == 5 or cycle == 100 or cycle == 500 or cycle == 1000:
                data_valid = int(self.dut.data_valid.value)
                data_ready = int(self.dut.data_ready.value)
                timeout_counter = int(self.dut.r_timeout_counter.value)
                backpressure_warning = int(self.dut.backpressure_warning.value)
                fsm_state = int(self.dut.fsm_state.value)
                print(f"    Cycle {cycle}: data_valid={data_valid}, data_ready={data_ready}, "
                      f"timeout_counter={timeout_counter}, backpressure_warning={backpressure_warning}, "
                      f"fsm_state=0x{fsm_state:02x}")

        # Use the last sampled values (from cycle 1000)
        print(f"  Final timeout_counter (at cycle 1000): {timeout_counter}")
        print(f"  Backpressure warning (at cycle 1000): {backpressure_warning}")

        # Check results BEFORE restoring data_ready
        if backpressure_warning == 1 and timeout_counter >= 1000:
            print("  ✅ Timeout/backpressure detected successfully!")
            success = True
        else:
            print(f"  ❌ Timeout not detected (counter={timeout_counter}, warning={backpressure_warning})")
            success = False

        # Now restore data_ready to allow scheduler to complete
        self.dut.data_ready.value = 1

        # Give scheduler time to complete
        for _ in range(100):
            await RisingEdge(self.clk)

        return success


# ===========================================================================
# COCOTB TEST FUNCTION
# ===========================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_timeout_simple(dut):
    """Simple timeout test without GAXI infrastructure"""
    tb = TimeoutTB(dut)
    await tb.setup()
    result = await tb.test_timeout()
    assert result, "Timeout detection test failed"


# ===========================================================================
# PYTEST WRAPPER
# ===========================================================================

@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.timeout
def test_timeout_simple(request):
    """Pytest wrapper for simple timeout test"""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "scheduler"

    verilog_sources = [
        os.path.join(repo_root, 'rtl', 'amba', 'includes', 'monitor_pkg.sv'),
        os.path.join(repo_root, 'projects', 'components', 'rapids', 'rtl', 'includes', 'rapids_pkg.sv'),
        os.path.join(repo_root, 'projects', 'components', 'rapids', 'rtl', 'rapids_fub', f'{dut_name}.sv'),
    ]

    test_name = "test_scheduler_timeout_simple"

    # Handle pytest-xdist
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'CHANNEL_ID': 0,
        'NUM_CHANNELS': 8,
        'CHAN_WIDTH': 3,
        'ADDR_WIDTH': 64,
        'DATA_WIDTH': 512,
        'CREDIT_WIDTH': 8,
        'TIMEOUT_CYCLES': 1000,
        'EARLY_WARNING_THRESHOLD': 4,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'DUT': dut_name,
        'COCOTB_LOG_LEVEL': 'INFO',
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[
                os.path.join(repo_root, 'projects', 'components', 'rapids', 'rtl', 'includes'),
                os.path.join(repo_root, 'rtl', 'amba', 'includes'),
            ],
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_timeout_simple",
            parameters=rtl_parameters,
            simulator="verilator",
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=["-Wno-TIMESCALEMOD"],
        )
        print(f"✓ Test completed! Logs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"  View command: {cmd_filename}")
    except Exception as e:
        print(f"❌ Test failed: {str(e)}")
        print(f"Logs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"View command: {cmd_filename}")
        raise


if __name__ == "__main__":
    # Run when executed directly
    import sys
    print("Running simple timeout detection test...")

    class MockRequest:
        pass

    test_timeout_simple(MockRequest())
