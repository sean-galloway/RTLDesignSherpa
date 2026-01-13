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
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


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

        # Configure before reset (Phase 1 simplified scheduler)
        self.dut.cfg_channel_enable.value = 1
        self.dut.cfg_channel_reset.value = 0
        self.dut.cfg_sched_timeout_cycles.value = 1000  # 1000 cycle timeout
        self.dut.cfg_sched_timeout_enable.value = 1     # Enable timeout detection

        # Reset
        self.dut.rst_n.value = 0
        await Timer(100, units="ns")
        self.dut.rst_n.value = 1
        await Timer(50, units="ns")

        # Initialize descriptor interface
        self.dut.descriptor_valid.value = 0
        self.dut.descriptor_packet.value = 0
        self.dut.descriptor_error.value = 0

        # Initialize completion/error interfaces from engines
        self.dut.sched_rd_done_strobe.value = 0
        self.dut.sched_rd_beats_done.value = 0
        self.dut.sched_wr_done_strobe.value = 0
        self.dut.sched_wr_beats_done.value = 0
        self.dut.sched_rd_error.value = 0
        self.dut.sched_wr_error.value = 0

        # sched_wr_ready indicates write engine is available
        self.dut.sched_wr_ready.value = 1

        # Monitor bus
        self.dut.mon_ready.value = 1

        await Timer(50, units="ns")

    async def send_descriptor(self, src_addr, dst_addr, length_beats):
        """Send a 256-bit RAPIDS descriptor to the scheduler

        RAPIDS Descriptor Format (256-bit):
          [63:0]    - src_addr
          [127:64]  - dst_addr
          [159:128] - length (beats)
          [191:160] - next_descriptor_ptr
          [192]     - valid
          [193]     - gen_irq
          [194]     - last
          [195]     - error
          [199:196] - channel_id
          [207:200] - priority
          [255:208] - reserved
        """
        descriptor = 0
        descriptor |= (src_addr & 0xFFFFFFFFFFFFFFFF)             # [63:0] src_addr
        descriptor |= (dst_addr & 0xFFFFFFFFFFFFFFFF) << 64       # [127:64] dst_addr
        descriptor |= (length_beats & 0xFFFFFFFF) << 128          # [159:128] length
        descriptor |= 0 << 160                                    # [191:160] next_ptr = 0 (last)
        descriptor |= 1 << 192                                    # [192] valid = 1
        descriptor |= 0 << 193                                    # [193] gen_irq = 0
        descriptor |= 1 << 194                                    # [194] last = 1
        descriptor |= 0 << 195                                    # [195] error = 0

        # Wait for ready
        for _ in range(100):
            await RisingEdge(self.clk)
            if int(self.dut.descriptor_ready.value) == 1:
                break

        # Send descriptor
        self.dut.descriptor_valid.value = 1
        self.dut.descriptor_packet.value = descriptor
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
        """Test timeout detection by not sending completion strobes

        Phase 1 scheduler timeout mechanism:
        - Timeout counter increments when in XFER state
        - Counter resets when done_strobe is received
        - sched_error goes high when timeout expires
        """
        print("\n=== Testing Timeout Detection ===")

        # Send descriptor (src=0x1000, dst=0x2000, 16 beats)
        await self.send_descriptor(src_addr=0x1000, dst_addr=0x2000, length_beats=16)
        print("  Descriptor sent")

        # Wait for scheduler to start transfer (sched_rd_valid or sched_wr_valid)
        for cycle in range(50):
            await RisingEdge(self.clk)
            sched_rd = int(self.dut.sched_rd_valid.value)
            sched_wr = int(self.dut.sched_wr_valid.value)
            if sched_rd == 1 or sched_wr == 1:
                print(f"  Transfer started after {cycle} cycles (rd={sched_rd}, wr={sched_wr})")
                break

        if int(self.dut.sched_rd_valid.value) != 1:
            print("  ❌ ERROR: Scheduler never asserted sched_rd_valid")
            return False

        # Create backpressure by setting sched_wr_ready=0
        # Timeout counter increments when sched_wr_valid && !sched_wr_ready
        print("  Creating backpressure (sched_wr_ready=0)...")
        self.dut.sched_wr_ready.value = 0

        timeout_counter = 0
        sched_error = 0

        for cycle in range(1200):
            await RisingEdge(self.clk)

            # Keep write engine not ready (creates backpressure)
            self.dut.sched_wr_ready.value = 0
            self.dut.sched_rd_done_strobe.value = 0
            self.dut.sched_wr_done_strobe.value = 0

            # Sample periodically
            if cycle == 50 or cycle == 500 or cycle == 900 or cycle == 1100:
                try:
                    timeout_counter = int(self.dut.r_timeout_counter.value)
                except AttributeError:
                    timeout_counter = -1  # Signal not visible
                sched_error = int(self.dut.sched_error.value)
                scheduler_state = int(self.dut.scheduler_state.value)
                print(f"    Cycle {cycle}: timeout_counter={timeout_counter}, "
                      f"sched_error={sched_error}, state=0x{scheduler_state:02x}")

            # Early exit if error detected
            if int(self.dut.sched_error.value) == 1:
                print(f"  ✅ sched_error asserted at cycle {cycle}")
                break

        sched_error = int(self.dut.sched_error.value)

        if sched_error == 1:
            print("  ✅ Timeout detected successfully (sched_error=1)!")
            return True
        else:
            print(f"  ❌ Timeout not detected (sched_error={sched_error})")
            return False


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
    # Check if coverage collection is enabled via environment variable
    coverage_enabled = os.environ.get('COVERAGE', '0') == '1'

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "scheduler_beats"

    # Use filelist to get all required sources (including monitor packages)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/fub_beats/scheduler_beats.f'
    )

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
        'ADDR_WIDTH': 64,
        'DATA_WIDTH': 512,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'DUT': dut_name,
        'COCOTB_LOG_LEVEL': 'INFO',
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    # Build compile args - add coverage if enabled
    compile_args = ["-Wno-TIMESCALEMOD", "-Wno-WIDTH", "-Wno-UNOPTFLAT"]
    if coverage_enabled:
        compile_args.extend([
            "--coverage-line",
            "--coverage-toggle",
            "--coverage-underscore",
        ])

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_timeout_simple",
            parameters=rtl_parameters,
            simulator="verilator",
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=compile_args,
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
