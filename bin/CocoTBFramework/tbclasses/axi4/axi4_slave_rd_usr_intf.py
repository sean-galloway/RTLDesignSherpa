"""
AXI4 Slave Read User Interface

This module provides a testbench interface for the user-facing interfaces
of the AXI4 Slave Read module, specifically focusing on the error interface.
"""

import cocotb
from cocotb.triggers import Timer
from collections import deque

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_slave
from CocoTBFramework.components.flex_randomizer import FlexRandomizer

# Import definitions from include file
from .axi4_slave_rd_usr_intf_incl import (
    ErrorInfo, ErrorType, create_error_randomizers,
    get_error_fifo_field_config,
    FIFO_READY_CONSTRAINTS_FIXED,
    FIFO_READY_CONSTRAINTS_ALWAYS, FIFO_READY_CONSTRAINTS_FAST,
    FIFO_READY_CONSTRAINTS_SLOW, FIFO_READY_CONSTRAINTS_VERY_SLOW
)


class Axi4SlaveRdUserIntf(TBBase):
    """
    Interface for the user-facing components of the AXI4 Slave Read module.
    This class handles the error interface which provides additional
    functionality beyond the standard AXI4 interfaces.
    """

    def __init__(self, dut):
        """
        Initialize the AXI4 Slave Read User Interface.

        Args:
            dut: Device under test
        """
        super().__init__(dut)

        # Extract parameters from the DUT or use defaults
        self.id_width = int(getattr(dut, 'AXI_ID_WIDTH', 8))
        self.addr_width = int(getattr(dut, 'AXI_ADDR_WIDTH', 32))
        self.data_width = int(getattr(dut, 'AXI_DATA_WIDTH', 32))
        self.user_width = int(getattr(dut, 'AXI_USER_WIDTH', 1))
        self.timeout_ar = int(getattr(dut, 'TIMEOUT_AR', 1000))
        self.timeout_r = int(getattr(dut, 'TIMEOUT_R', 1000))

        # Create field configurations for the user interfaces
        self.error_field_config = get_error_fifo_field_config(self.addr_width, self.id_width)

        # Create randomizers for different test scenarios
        self.error_randomizers = create_error_randomizers()

        # Create GAXI slave component for the error FIFO
        self.error_slave = create_gaxi_slave(
            dut, "ErrorSlave", "", dut.aclk,
            field_config=self.error_field_config,
            randomizer=self.error_randomizers['fast_ready'],
            log=self.log,
            multi_sig=True,
            signal_map={
                'm2s_valid': 'm_error_valid',
                's2m_ready': 'm_error_ready'
            },
            optional_signal_map={
                'm2s_pkt_type': 'm_error_type',
                'm2s_pkt_addr': 'm_error_addr',
                'm2s_pkt_id': 'm_error_id'
            }
        )

        # Queue for tracking received information
        self.error_queue = deque()

        # Add callback to process received packets
        self.error_slave.add_callback(self._handle_error_info)

        # For test verification
        self.expected_errors = {}  # Dict mapping ID to expected errors
        self.total_errors = 0

    def _handle_error_info(self, packet):
        """
        Process error information received from the DUT.

        Args:
            packet: GAXIPacket containing error information
        """
        if hasattr(packet, 'type') and hasattr(packet, 'addr') and hasattr(packet, 'id'):
            error_info = ErrorInfo(
                type=packet.type,
                addr=packet.addr,
                id=packet.id
            )

            self.error_queue.append(error_info)
            self.log.info(f"Received error info: type={error_info.error_type_str}, addr=0x{error_info.addr:08X}, id=0x{error_info.id:X}")

            # Error types are verified in the test cases, not automatically here

    async def reset_interfaces(self):
        """Reset the error interface."""
        await self.error_slave.reset_bus()

        # Clear queue
        self.error_queue.clear()

        # Reset verification state
        self.expected_errors.clear()
        self.total_errors = 0

        self.log.info("User interface reset")

    def set_error_readiness(self, mode):
        """
        Set the readiness mode for the error interface.

        Args:
            mode: One of 'fixed', 'always_ready', 'fast_ready', 'slow_ready', 'very_slow_ready'
        """
        if mode in self.error_randomizers:
            self.error_slave.set_randomizer(self.error_randomizers[mode])
            self.log.info(f"Error interface readiness set to {mode}")
        else:
            self.log.error(f"Unknown error readiness mode: {mode}")

    def expect_error(self, id_value, error_type):
        """
        Register an expected error for a specific ID.

        Args:
            id_value: Transaction ID
            error_type: Expected error type (from ErrorType enum)
        """
        self.expected_errors[id_value] = error_type
        self.log.info(f"Expecting error type {ErrorType(error_type).name} for ID=0x{id_value:X}")

    def get_error_count(self, error_type=None):
        """
        Get the count of errors of a specific type.

        Args:
            error_type: Error type to count (None for all errors)

        Returns:
            Number of errors of the specified type
        """
        if error_type is None:
            return len(self.error_queue)

        return sum(error.type == error_type for error in self.error_queue)

    async def wait_for_errors(self, count, timeout_ns=None):
        """
        Wait for a specific number of error notifications.

        Args:
            count: Number of errors to wait for
            timeout_ns: Timeout in nanoseconds (None for no timeout)

        Returns:
            True if the specified number of errors were received, False otherwise
        """
        start_time = cocotb.utils.get_sim_time('ns')
        current_count = len(self.error_queue)

        while current_count < count:
            # Check timeout
            if timeout_ns is not None:
                current_time = cocotb.utils.get_sim_time('ns')
                if current_time - start_time > timeout_ns:
                    self.log.warning(f"Timeout waiting for errors: received {current_count}/{count}")
                    return False

            # Wait for more errors
            await Timer(100, units='ns')
            current_count = len(self.error_queue)

        return True

    async def verify_collision_behavior(self, error_types_to_trigger, timeout_clks=1000):
        """
        Verify behavior when multiple error types occur simultaneously.

        Args:
            error_types_to_trigger: List of error types to trigger simultaneously
            timeout_clks: Timeout in clock cycles

        Returns:
            True if all expected errors were detected, False otherwise
        """
        # Count current errors
        initial_error_count = len(self.error_queue)

        # Set interface to fast response mode
        self.set_error_readiness('fast_ready')

        # Wait for errors to be reported (timeout based)
        start_time = cocotb.utils.get_sim_time('ns')
        timeout_ns = timeout_clks * 10  # Assuming 10ns clock period

        # Expected number of errors
        expected_error_count = initial_error_count + len(error_types_to_trigger)

        # Wait for errors to be reported
        success = await self.wait_for_errors(expected_error_count, timeout_ns)

        if not success:
            self.log.error(f"Not all expected collision errors were detected: {error_types_to_trigger}")
            self.total_errors += 1
            return False

        # Verify that all expected error types were detected
        new_errors = list(self.error_queue)[initial_error_count:]
        detected_types = [error.type for error in new_errors]

        all_detected = True
        for error_type in error_types_to_trigger:
            if error_type not in detected_types:
                self.log.error(f"Error type {ErrorType(error_type).name} not detected in collision test")
                self.total_errors += 1
                all_detected = False

        return all_detected
