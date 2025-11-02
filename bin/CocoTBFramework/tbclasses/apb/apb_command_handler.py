# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBCommandHandler
# Purpose: APB Command Handler for APB slave command/response interface
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
APB Command Handler for APB slave command/response interface
"""
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer


class APBCommandHandler:
    """
    Command Handler for APB slave command/response interface.

    This class:
    1. Monitors the command interface of an APB slave
    2. Processes commands by reading/writing to a memory model
    3. Drives the response interface with results

    The handler acts as the "processor" behind the APB slave's command/response
    interface, allowing it to operate independently of the APB bus.
    """

    def __init__(self, dut, memory_model, log=None):
        """
        Initialize the command handler.

        Args:
            dut: Device under test (for accessing command/response signals)
            memory_model: MemoryModel instance for data storage/retrieval
            log: Logger instance
        """
        self.dut = dut
        self.memory_model = memory_model
        self.log = log or getattr(dut, '_log', None)

        # Command/response tasks
        self.cmd_task = None
        self.running = False

    async def start(self):
        """Start the command handler task."""
        if not self.running:
            self.running = True
            self.cmd_task = cocotb.start_soon(self._process_commands())
            self.log.info("APB Command Handler started")

    async def stop(self):
        """Stop the command handler task."""
        self.running = False
        await Timer(10, units='ns')  # Allow task to complete
        self.cmd_task = None
        self.log.info("APB Command Handler stopped")

    async def _process_commands(self):  # sourcery skip: move-assign
        """
        Process commands from the APB slave command interface.

        This method:
        1. Monitors the command interface for valid commands
        2. Processes commands using the memory model
        3. Drives the response interface with results
        """
        while self.running:
            # Wait for command valid signal
            while not self.dut.o_cmd_valid.value and self.running:
                await RisingEdge(self.dut.pclk)

            if not self.running:
                break

            # Capture command details
            pwrite = int(self.dut.o_cmd_pwrite.value)
            paddr = int(self.dut.o_cmd_paddr.value)
            pwdata = int(self.dut.o_cmd_pwdata.value)
            pstrb = int(self.dut.o_cmd_pstrb.value) if hasattr(self.dut, 'o_cmd_pstrb') else 0xFF

            # Process command
            if pwrite:  # Write command
                self.log.info(f"Command: WRITE addr=0x{paddr:08X}, data=0x{pwdata:08X}")

                # Convert data to bytearray
                pwdata_bytes = self.memory_model.integer_to_bytearray(pwdata, self.memory_model.bytes_per_line)

                # Write to memory model
                self.memory_model.write(paddr, pwdata_bytes, pstrb)

                # Create response (no data for writes)
                prdata = 0
            else:  # Read command
                self.log.info(f"Command: READ addr=0x{paddr:08X}")

                # Read from memory model
                prdata_bytes = self.memory_model.read(paddr, self.memory_model.bytes_per_line)
                prdata = self.memory_model.bytearray_to_integer(prdata_bytes)

                self.log.info(f"Read data: 0x{prdata:08X}")

            # Acknowledge command
            self.dut.i_cmd_ready.value = 1
            await RisingEdge(self.dut.pclk)
            self.dut.i_cmd_ready.value = 0

            # Add short delay for processing
            delay_cycles = 2  # Adjustable delay
            for _ in range(delay_cycles):
                await RisingEdge(self.dut.pclk)

            # Send response
            self.dut.i_rsp_valid.value = 1
            self.dut.i_rsp_prdata.value = prdata
            self.dut.i_rsp_pslverr.value = 0  # No error by default

            # Wait for ready acknowledgement
            while not self.dut.o_rsp_ready.value and self.running:
                await RisingEdge(self.dut.pclk)

            if not self.running:
                break

            # Deassert valid on next clock
            await RisingEdge(self.dut.pclk)
            self.dut.i_rsp_valid.value = 0

    async def reset(self):
        """Reset the command handler state."""
        # De-assert all outputs
        self.dut.i_cmd_ready.value = 0
        self.dut.i_rsp_valid.value = 0
        self.dut.i_rsp_prdata.value = 0
        self.dut.i_rsp_pslverr.value = 0

        # Reset the memory model if needed
        # self.memory_model.reset()

        # Wait a couple of clock cycles
        for _ in range(2):
            await RisingEdge(self.dut.pclk)
