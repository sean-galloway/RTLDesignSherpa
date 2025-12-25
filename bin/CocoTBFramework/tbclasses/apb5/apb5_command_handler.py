# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APB5CommandHandler
# Purpose: APB5 Command Handler for APB5 slave command/response interface
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""
APB5 Command Handler for APB5 slave command/response interface

Extended from APB command handler to support APB5 features:
- User signals (PAUSER, PWUSER, PRUSER, PBUSER)
- Wake-up signaling (PWAKEUP)
- Parity support (optional)
"""
import cocotb
from cocotb.triggers import RisingEdge, Timer


class APB5CommandHandler:
    """
    Command Handler for APB5 slave command/response interface.

    This class:
    1. Monitors the command interface of an APB5 slave
    2. Processes commands by reading/writing to a memory model
    3. Drives the response interface with results
    4. Handles APB5-specific signals (user signals, wakeup)

    The handler acts as the "processor" behind the APB5 slave's command/response
    interface, allowing it to operate independently of the APB bus.
    """

    def __init__(self, dut, memory_model, log=None,
                 ruser_width=4, buser_width=4,
                 support_wakeup=True, support_parity=False):
        """
        Initialize the APB5 command handler.

        Args:
            dut: Device under test (for accessing command/response signals)
            memory_model: MemoryModel instance for data storage/retrieval
            log: Logger instance
            ruser_width: Width of PRUSER signal
            buser_width: Width of PBUSER signal
            support_wakeup: Whether to support PWAKEUP signaling
            support_parity: Whether to support parity signals
        """
        self.dut = dut
        self.memory_model = memory_model
        self.log = log or getattr(dut, '_log', None)

        # APB5-specific configuration
        self.ruser_width = ruser_width
        self.buser_width = buser_width
        self.support_wakeup = support_wakeup
        self.support_parity = support_parity

        # User signal maximums
        self.max_ruser = (1 << ruser_width) - 1
        self.max_buser = (1 << buser_width) - 1

        # Command/response tasks
        self.cmd_task = None
        self.wakeup_task = None
        self.running = False

        # Wakeup state
        self.wakeup_pending = False
        self.wakeup_reason = 0

        # Statistics
        self.stats = {
            'commands_processed': 0,
            'writes': 0,
            'reads': 0,
            'errors': 0,
            'wakeups': 0
        }

    async def start(self):
        """Start the command handler task."""
        if not self.running:
            self.running = True
            self.cmd_task = cocotb.start_soon(self._process_commands())
            if self.support_wakeup:
                self.wakeup_task = cocotb.start_soon(self._handle_wakeup())
            self.log.info("APB5 Command Handler started")

    async def stop(self):
        """Stop the command handler task."""
        self.running = False
        await Timer(10, units='ns')  # Allow task to complete
        self.cmd_task = None
        self.wakeup_task = None
        self.log.info("APB5 Command Handler stopped")

    async def _process_commands(self):
        """
        Process commands from the APB5 slave command interface.

        This method:
        1. Monitors the command interface for valid commands
        2. Captures APB5 user signals (PAUSER, PWUSER)
        3. Processes commands using the memory model
        4. Drives the response interface with results and user signals
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

            # Capture APB5-specific signals if available
            pauser = 0
            pwuser = 0
            if hasattr(self.dut, 'o_cmd_pauser'):
                pauser = int(self.dut.o_cmd_pauser.value)
            if hasattr(self.dut, 'o_cmd_pwuser'):
                pwuser = int(self.dut.o_cmd_pwuser.value)

            # Process command
            error = 0
            if pwrite:  # Write command
                self.log.info(f"APB5 Command: WRITE addr=0x{paddr:08X}, data=0x{pwdata:08X}, "
                             f"pauser=0x{pauser:X}, pwuser=0x{pwuser:X}")

                # Convert data to bytearray
                pwdata_bytes = self.memory_model.integer_to_bytearray(
                    pwdata, self.memory_model.bytes_per_line
                )

                # Write to memory model
                try:
                    self.memory_model.write(paddr, pwdata_bytes, pstrb)
                    self.stats['writes'] += 1
                except Exception as e:
                    self.log.warning(f"Write error: {e}")
                    error = 1
                    self.stats['errors'] += 1

                # Create response (no data for writes)
                prdata = 0
            else:  # Read command
                self.log.info(f"APB5 Command: READ addr=0x{paddr:08X}, pauser=0x{pauser:X}")

                # Read from memory model
                try:
                    prdata_bytes = self.memory_model.read(paddr, self.memory_model.bytes_per_line)
                    prdata = self.memory_model.bytearray_to_integer(prdata_bytes)
                    self.stats['reads'] += 1
                except Exception as e:
                    self.log.warning(f"Read error: {e}")
                    prdata = 0xDEADBEEF  # Error pattern
                    error = 1
                    self.stats['errors'] += 1

                self.log.info(f"Read data: 0x{prdata:08X}")

            # Acknowledge command
            self.dut.i_cmd_ready.value = 1
            await RisingEdge(self.dut.pclk)
            self.dut.i_cmd_ready.value = 0

            # Add short delay for processing
            delay_cycles = 2  # Adjustable delay
            for _ in range(delay_cycles):
                await RisingEdge(self.dut.pclk)

            # Generate APB5 user response signals
            pruser = self._generate_pruser(paddr, pwrite)
            pbuser = self._generate_pbuser(paddr, pwrite, error)

            # Send response
            self.dut.i_rsp_valid.value = 1
            self.dut.i_rsp_prdata.value = prdata
            self.dut.i_rsp_pslverr.value = error

            # Set APB5 user response signals if available
            if hasattr(self.dut, 'i_rsp_pruser'):
                self.dut.i_rsp_pruser.value = pruser
            if hasattr(self.dut, 'i_rsp_pbuser'):
                self.dut.i_rsp_pbuser.value = pbuser

            # Wait for ready acknowledgement
            while not self.dut.o_rsp_ready.value and self.running:
                await RisingEdge(self.dut.pclk)

            if not self.running:
                break

            # Deassert valid on next clock
            await RisingEdge(self.dut.pclk)
            self.dut.i_rsp_valid.value = 0

            self.stats['commands_processed'] += 1

    async def _handle_wakeup(self):
        """
        Handle APB5 PWAKEUP signaling.

        This method monitors for conditions that should trigger wakeup
        and drives the PWAKEUP signal accordingly.
        """
        while self.running:
            # Wait for wakeup condition
            while not self.wakeup_pending and self.running:
                await RisingEdge(self.dut.pclk)

            if not self.running:
                break

            # Assert PWAKEUP
            if hasattr(self.dut, 'o_pwakeup'):
                self.dut.o_pwakeup.value = 1
                self.log.info(f"APB5 PWAKEUP asserted, reason={self.wakeup_reason}")
                self.stats['wakeups'] += 1

                # Hold for a few cycles
                for _ in range(3):
                    await RisingEdge(self.dut.pclk)

                # Deassert PWAKEUP
                self.dut.o_pwakeup.value = 0
                self.log.info("APB5 PWAKEUP deasserted")

            self.wakeup_pending = False
            self.wakeup_reason = 0

    def _generate_pruser(self, addr, pwrite):
        """
        Generate PRUSER value based on transaction.

        Can be overridden in subclasses for custom behavior.
        """
        # Simple implementation: lower bits of address
        return addr & self.max_ruser

    def _generate_pbuser(self, addr, pwrite, error):
        """
        Generate PBUSER value based on transaction.

        Can be overridden in subclasses for custom behavior.
        """
        # Simple implementation: error in bit 0, write in bit 1
        return (error & 1) | ((pwrite & 1) << 1)

    def trigger_wakeup(self, reason=1):
        """
        Trigger a PWAKEUP event.

        Args:
            reason: Reason code for the wakeup
        """
        if self.support_wakeup:
            self.wakeup_pending = True
            self.wakeup_reason = reason

    async def reset(self):
        """Reset the command handler state."""
        # De-assert all outputs
        self.dut.i_cmd_ready.value = 0
        self.dut.i_rsp_valid.value = 0
        self.dut.i_rsp_prdata.value = 0
        self.dut.i_rsp_pslverr.value = 0

        # De-assert APB5 outputs if available
        if hasattr(self.dut, 'i_rsp_pruser'):
            self.dut.i_rsp_pruser.value = 0
        if hasattr(self.dut, 'i_rsp_pbuser'):
            self.dut.i_rsp_pbuser.value = 0
        if hasattr(self.dut, 'o_pwakeup'):
            self.dut.o_pwakeup.value = 0

        # Reset wakeup state
        self.wakeup_pending = False
        self.wakeup_reason = 0

        # Reset statistics
        for key in self.stats:
            self.stats[key] = 0

        # Wait a couple of clock cycles
        for _ in range(2):
            await RisingEdge(self.dut.pclk)

    def get_stats(self):
        """Get command handler statistics."""
        return self.stats.copy()
