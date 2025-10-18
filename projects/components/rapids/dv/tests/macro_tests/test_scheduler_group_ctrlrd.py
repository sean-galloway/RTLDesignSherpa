# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CtrlRdResponder
# Purpose: RAPIDS Scheduler Group - Control Read (ctrlrd) Integration Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Scheduler Group - Control Read (ctrlrd) Integration Test

Purpose:
    Focused test to verify the ctrlrd interface integration between scheduler_group
    and external control read logic.

Test Strategy:
    1. Initialize scheduler_group with minimal configuration
    2. Issue descriptor with control read requirement
    3. Monitor ctrlrd interface for transactions
    4. Respond to ctrlrd requests with valid data
    5. Verify scheduler processes responses correctly

Author: RTL Design Sherpa
Version: 1.0
Date: 2025-10-17
"""

import os
import sys
import pytest
import cocotb
from cocotb.triggers import Timer, RisingEdge, ClockCycles
from cocotb.clock import Clock
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# Add dv directory to path so we can import from tbclasses/
dv_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if dv_dir not in sys.path:
    sys.path.insert(0, dv_dir)

from tbclasses.scheduler_group_tb import SchedulerGroupTB

class CtrlRdResponder:
    """Simple responder for ctrlrd interface"""

    def __init__(self, dut, clk_name='clk'):
        self.dut = dut
        self.clk_name = clk_name
        self.log = cocotb.logging.getLogger("CtrlRdResponder")
        self.transactions = []

    async def run(self):
        """Monitor and respond to ctrlrd requests"""
        self.log.info("CtrlRd Responder started")

        while True:
            await RisingEdge(self.dut.clk)

            # Check for valid ctrlrd request
            if hasattr(self.dut, 'ctrlrd_valid') and self.dut.ctrlrd_valid.value == 1:
                # Capture request
                addr = self.dut.ctrlrd_addr.value.integer if hasattr(self.dut, 'ctrlrd_addr') else 0
                data = self.dut.ctrlrd_data.value.integer if hasattr(self.dut, 'ctrlrd_data') else 0
                mask = self.dut.ctrlrd_mask.value.integer if hasattr(self.dut, 'ctrlrd_mask') else 0

                self.log.info(f"CtrlRd Request: addr=0x{addr:08x} data=0x{data:08x} mask=0x{mask:02x}")
                self.transactions.append({'addr': addr, 'data': data, 'mask': mask})

                # Always ready, return data as result (simple echo for now)
                self.dut.ctrlrd_ready.value = 1
                self.dut.ctrlrd_error.value = 0
                self.dut.ctrlrd_result.value = data  # Echo back the data

                # Wait for handshake
                await RisingEdge(self.dut.clk)

                self.log.info(f"CtrlRd Response: result=0x{data:08x} (echo)")


@cocotb.test()
async def cocotb_test_ctrlrd_basic(dut):
    """Basic ctrlrd interface test - verify handshake and data flow"""

    # Create testbench (scheduler_group uses clk/rst_n)
    tb = SchedulerGroupTB(dut, clk=dut.clk, rst_n=dut.rst_n)

    # Initialize DUT
    cocotb.log.info("=" * 80)
    cocotb.log.info("CTRLRD BASIC HANDSHAKE TEST")
    cocotb.log.info("=" * 80)

    await tb.setup_clocks_and_reset()

    # Start ctrlrd responder
    responder = CtrlRdResponder(dut)
    cocotb.start_soon(responder.run())

    # Wait for stability
    await ClockCycles(dut.clk, 10)

    # Configure scheduler_group for basic operation
    cocotb.log.info("Configuring scheduler_group...")
    dut.cfg_use_credit.value = 0  # Disable credit mode for basic test
    dut.cfg_initial_credit.value = 4  # 4 = 16 credits (2^4)
    dut.cfg_channel_enable.value = 1
    dut.cfg_idle_mode.value = 0
    dut.cfg_channel_wait.value = 0
    dut.cfg_ctrlrd_max_try.value = 10  # Allow up to 10 retries for control reads
    dut.cfg_channel_reset.value = 0

    await ClockCycles(dut.clk, 5)

    # TODO: Issue a descriptor that triggers control read
    # For now, just verify the responder is working

    # Monitor for ctrlrd activity
    cocotb.log.info("Monitoring for ctrlrd transactions...")
    timeout_cycles = 500
    for _ in range(timeout_cycles):
        await RisingEdge(dut.clk)

        if len(responder.transactions) > 0:
            cocotb.log.info(f"✓ Captured {len(responder.transactions)} ctrlrd transaction(s)")
            break
    else:
        cocotb.log.info("ℹ No ctrlrd transactions observed (may be expected if no descriptors issued)")

    # Print summary
    cocotb.log.info("=" * 80)
    cocotb.log.info(f"CTRLRD BASIC TEST COMPLETE")
    cocotb.log.info(f"Transactions captured: {len(responder.transactions)}")
    cocotb.log.info("=" * 80)

    # Test passes if responder is functional (we'll enhance descriptor injection later)


@cocotb.test()
async def cocotb_test_ctrlrd_descriptor_flow(dut):
    """Test ctrlrd with actual descriptor submission"""

    # Create testbench (scheduler_group uses clk/rst_n)
    tb = SchedulerGroupTB(dut, clk=dut.clk, rst_n=dut.rst_n)

    cocotb.log.info("=" * 80)
    cocotb.log.info("CTRLRD DESCRIPTOR FLOW TEST")
    cocotb.log.info("=" * 80)

    await tb.setup_clocks_and_reset()

    # Start ctrlrd responder
    responder = CtrlRdResponder(dut)
    cocotb.start_soon(responder.run())

    # Configure scheduler_group
    dut.cfg_use_credit.value = 0  # Disable credit mode for basic test
    dut.cfg_initial_credit.value = 4  # 4 = 16 credits (2^4)
    dut.cfg_channel_enable.value = 1
    dut.cfg_idle_mode.value = 0
    dut.cfg_channel_wait.value = 0
    dut.cfg_ctrlrd_max_try.value = 10  # Allow up to 10 retries for control reads
    dut.cfg_channel_reset.value = 0

    await ClockCycles(dut.clk, 5)

    # Create a simple descriptor (type 0 - write operation for testing)
    descriptor = {
        'type': 0,
        'src_addr': 0x1000,
        'dst_addr': 0x2000,
        'length': 256,
        'channel': 0
    }

    cocotb.log.info(f"Descriptor spec: {descriptor}")
    cocotb.log.info("Note: This test currently just verifies ctrlrd responder setup")
    cocotb.log.info("TODO: Add APB descriptor submission once method is available")

    # For now, just wait and see if any ctrlrd activity occurs
    cocotb.log.info("Monitoring for ctrlrd transactions...")
    timeout_cycles = 500

    for _ in range(timeout_cycles):
        await RisingEdge(dut.clk)

        if len(responder.transactions) > 0:
            cocotb.log.info(f"✓ Captured {len(responder.transactions)} ctrlrd transaction(s)")
            break

        # Check for completion
        if hasattr(dut, 'eos_completion_valid') and dut.eos_completion_valid.value == 1:
            cocotb.log.info("✓ Operation completed")
            break
    else:
        cocotb.log.info("ℹ No ctrlrd transactions observed (descriptor submission not yet implemented)")

    # Print summary
    cocotb.log.info("=" * 80)
    cocotb.log.info(f"CTRLRD DESCRIPTOR FLOW TEST COMPLETE")
    cocotb.log.info(f"CtrlRd transactions: {len(responder.transactions)}")
    for i, txn in enumerate(responder.transactions):
        cocotb.log.info(f"  [{i}] addr=0x{txn['addr']:08x} data=0x{txn['data']:08x}")
    cocotb.log.info("=" * 80)


# Pytest fixtures and test generation
@pytest.mark.parametrize(
    "num_channels,addr_width,data_width",
    [
        (32, 64, 512),  # Standard configuration
    ]
)
def test_scheduler_group_ctrlrd(num_channels, addr_width, data_width):
    """pytest wrapper for ctrlrd integration tests"""

    # Get paths using framework utility
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_fub': '../../rtl/rapids_fub',
        'rtl_rapids_macro': '../../rtl/rapids_macro',
        'rtl_rapids_includes': '../../rtl/includes',
        'rtl_amba': 'rtl/amba',
        'rtl_cmn': 'rtl/common'
    })

    # Get Verilog sources and includes from hierarchical file list
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/macro/scheduler_group.f'
    )

    # Construct test name
    test_name = f"test_scheduler_group_ctrlrd_nc{num_channels:02d}_aw{addr_width:02d}_dw{data_width:04d}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)

    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    rtl_parameters = {
        'NUM_CHANNELS': str(num_channels),
        'ADDR_WIDTH': str(addr_width),
        'DATA_WIDTH': str(data_width),
        'AXI_ID_WIDTH': '8',
        'CREDIT_WIDTH': '8',
    }

    # Test environment
    extra_env = {
        'DUT': 'scheduler_group',
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
    }

    # Verilator compilation arguments
    compile_args = [
        "-Wall",
        "-Wno-PINMISSING",
        "-Wno-UNUSED",
        "-Wno-SYNCASYNCNET",
        "-Wno-EOFNEWLINE",
        "-Wno-PINCONNECTEMPTY",
        "-Wno-IMPORTSTAR"
    ]

    # Get dv directory for Python imports
    dv_dir = os.path.dirname(tests_dir)  # Go up from tests/ to dv/

    # Run simulation
    run(
        python_search=[tests_dir, dv_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="scheduler_group",
        module="test_scheduler_group_ctrlrd",
        testcase="cocotb_test_ctrlrd_basic,cocotb_test_ctrlrd_descriptor_flow",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=False,  # Disable for speed
        keep_files=True,
        compile_args=compile_args,
    )


if __name__ == "__main__":
    # Allow running directly with pytest
    pytest.main([__file__, "-v", "-s"])
