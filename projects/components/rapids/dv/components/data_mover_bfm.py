# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: DataMoverBFM
# Purpose: RAPIDS Data Mover BFM - Reusable Data Engine Model
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Data Mover BFM - Reusable Data Engine Model

This BFM simulates a data mover/engine that responds to scheduler data transfer requests.
It's designed to be reused across different test scenarios:
- Scheduler-only unit tests
- Scheduler + descriptor engine integration tests
- Full RAPIDS integration tests

Key Features:
- Simple request/response model for data transfers
- Handles address alignment (ALIGN, STREAM, FINAL phases)
- Configurable delays for backpressure simulation
- Enable/disable control for manual testing scenarios
- Transaction tracking and statistics

Usage:
    data_bfm = DataMoverBFM(
        dut=dut,
        clk=clk,
        log=logger
    )

    # Start background processing
    cocotb.start_soon(data_bfm.run())

    # Enable/disable as needed
    data_bfm.enable = False  # For manual control in specific tests
"""

import cocotb
from cocotb.triggers import RisingEdge
import random


class DataMoverBFM:
    """Data Engine BFM for RAPIDS Scheduler Testing

    This BFM simulates a data mover/DMA engine that:
    1. Waits for data_valid from scheduler (data transfer request)
    2. Calculates how much data to consume based on address alignment
    3. Waits a configurable delay (simulating data transfer time)
    4. Pulses data_done_strobe to acknowledge completion

    The data_ready signal should be controlled separately by a GAXI slave
    component for proper protocol handling. This BFM focuses on the
    request/acknowledge behavior.
    """

    def __init__(self, dut, clk, log, enable=True):
        """Initialize the Data Mover BFM

        Args:
            dut: Device under test (scheduler module)
            clk: Clock signal
            log: Logger instance
            enable: Initial enable state (default: True)
        """
        self.dut = dut
        self.clk = clk
        self.log = log
        self.enable = enable

        # Configuration
        self.base_delay = 2      # Minimum cycles for data transfer
        self.max_delay = 5       # Maximum cycles for data transfer
        self.backpressure = False  # Enable longer delays for backpressure testing

        # Statistics
        self.transfers_completed = 0
        self.descriptors_completed = 0
        self.align_phase_count = 0
        self.stream_phase_count = 0
        self.final_phase_count = 0

    def set_timing(self, base_delay, max_delay):
        """Configure transfer timing delays

        Args:
            base_delay: Minimum delay in clock cycles
            max_delay: Maximum delay in clock cycles
        """
        self.base_delay = base_delay
        self.max_delay = max_delay
        self.log.info(f"Data BFM timing set to: base={base_delay}, max={max_delay} cycles")

    def enable_backpressure(self, enabled=True):
        """Enable/disable backpressure mode (longer delays)

        Args:
            enabled: True to enable extended delays, False for normal timing
        """
        self.backpressure = enabled
        if enabled:
            self.base_delay = 5
            self.max_delay = 15
        else:
            self.base_delay = 2
            self.max_delay = 5
        self.log.info(f"Data BFM backpressure mode: {'enabled' if enabled else 'disabled'}")

    async def run(self):
        """Main BFM loop - processes data transfer requests

        This coroutine should be started with cocotb.start_soon() and runs
        continuously in the background, responding to scheduler data requests.
        """
        # Track current transfer state per descriptor
        current_addr = 0
        current_remaining = 0
        in_transfer = False

        while True:
            await RisingEdge(self.clk)

            # Check if BFM is enabled - skip processing if disabled
            if not self.enable:
                continue

            # Check if scheduler is requesting a data transfer
            data_valid = int(self.dut.data_valid.value)
            data_ready = int(self.dut.data_ready.value)

            if data_valid == 1 and data_ready == 1:
                # Starting new descriptor? Capture initial parameters
                if not in_transfer:
                    current_addr = int(self.dut.data_address.value)
                    current_remaining = int(self.dut.data_length.value)
                    in_transfer = True
                    self.log.debug(f"Data BFM: New descriptor addr=0x{current_addr:x} len={current_remaining}B")

                # Calculate how much data to consume this transfer
                addr_offset = current_addr & 0x3F  # addr[5:0] - offset within 64B boundary

                if addr_offset != 0:
                    # ALIGNMENT phase: consume up to next 64B boundary
                    bytes_to_boundary = 64 - addr_offset
                    transfer_length = min(bytes_to_boundary, current_remaining)
                    phase_name = "ALIGN"
                    self.align_phase_count += 1
                elif current_remaining > 64:
                    # STREAMING phase: consume full 64B
                    transfer_length = 64
                    phase_name = "STREAM"
                    self.stream_phase_count += 1
                else:
                    # FINAL phase: consume remaining data
                    transfer_length = current_remaining
                    phase_name = "FINAL"
                    self.final_phase_count += 1

                self.log.debug(f"Data BFM: {phase_name} transfer len={transfer_length}B "
                              f"(offset={addr_offset}, remaining={current_remaining})")

                # Simulate data transfer processing time
                delay = random.randint(self.base_delay, self.max_delay)
                for _ in range(delay):
                    await RisingEdge(self.clk)

                # Update state for next transfer
                current_addr += transfer_length
                current_remaining -= transfer_length

                # Report completion to scheduler with done strobe
                self.dut.data_transfer_length.value = transfer_length
                self.dut.data_done_strobe.value = 1
                self.log.debug(f"Data BFM: Done {phase_name} len={transfer_length}B, remaining={current_remaining}B")

                await RisingEdge(self.clk)
                self.dut.data_done_strobe.value = 0

                self.transfers_completed += 1

                # Descriptor complete?
                if current_remaining == 0:
                    in_transfer = False
                    self.descriptors_completed += 1
                    self.log.debug(f"Data BFM: Descriptor complete (total: {self.descriptors_completed})")

                # Give scheduler time to process completion
                await RisingEdge(self.clk)

    def get_statistics(self):
        """Get BFM statistics

        Returns:
            dict: Statistics dictionary with transfer counts
        """
        return {
            'transfers_completed': self.transfers_completed,
            'descriptors_completed': self.descriptors_completed,
            'align_phase_count': self.align_phase_count,
            'stream_phase_count': self.stream_phase_count,
            'final_phase_count': self.final_phase_count
        }

    def reset_statistics(self):
        """Reset all statistics counters"""
        self.transfers_completed = 0
        self.descriptors_completed = 0
        self.align_phase_count = 0
        self.stream_phase_count = 0
        self.final_phase_count = 0
        self.log.info("Data BFM statistics reset")

    def print_statistics(self):
        """Print statistics summary"""
        self.log.info("=== Data Mover BFM Statistics ===")
        self.log.info(f"  Descriptors completed: {self.descriptors_completed}")
        self.log.info(f"  Total transfers: {self.transfers_completed}")
        self.log.info(f"    - ALIGN phase: {self.align_phase_count}")
        self.log.info(f"    - STREAM phase: {self.stream_phase_count}")
        self.log.info(f"    - FINAL phase: {self.final_phase_count}")
