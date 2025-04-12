"""
AXI4 Master Write Fub Interface

This module provides a testbench interface for the fub-facing interfaces
of the AXI4 Master Write module, specifically focusing on the split and error interfaces.
"""

import cocotb
from cocotb.triggers import Timer
from collections import deque

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_slave
from CocoTBFramework.components.flex_randomizer import FlexRandomizer

# Import definitions from include file
from .axi4_master_wr_fub_intf_incl import (
    SplitInfo, ErrorInfo, ErrorType, create_error_randomizers,
    get_split_fifo_field_config, get_error_fifo_field_config,
    FIFO_READY_CONSTRAINTS_FIXED,
    FIFO_READY_CONSTRAINTS_ALWAYS, FIFO_READY_CONSTRAINTS_FAST,
    FIFO_READY_CONSTRAINTS_SLOW, FIFO_READY_CONSTRAINTS_VERY_SLOW
)


class Axi4MasterWrFubIntf(TBBase):
    """
    Interface for the fub-facing components of the AXI4 Master Write module.
    This class handles the split and error interfaces which provide additional
    functionality beyond the standard AXI4 interfaces.
    """

    def __init__(self, dut):
        """
        Initialize the AXI4 Master Write Fub Interface.

        Args:
            dut: Device under test
        """
        super().__init__(dut)

        # Extract parameters from the DUT or use defaults
        self.id_width = int(getattr(dut, 'AXI_ID_WIDTH', 8))
        self.addr_width = int(getattr(dut, 'AXI_ADDR_WIDTH', 32))
        self.data_width = int(getattr(dut, 'AXI_DATA_WIDTH', 32))
        self.fub_width = int(getattr(dut, 'AXI_FUB_WIDTH', 1))
        self.timeout_aw = int(getattr(dut, 'TIMEOUT_AW', 1000))
        self.timeout_w = int(getattr(dut, 'TIMEOUT_W', 1000))
        self.timeout_b = int(getattr(dut, 'TIMEOUT_B', 1000))

        # Create field configurations for the fub interfaces
        self.split_field_config = get_split_fifo_field_config(self.addr_width, self.id_width)
        self.error_field_config = get_error_fifo_field_config(self.addr_width, self.id_width)

        # Create randomizers for different test scenarios
        self.split_randomizers = {
            'fixed': FlexRandomizer(FIFO_READY_CONSTRAINTS_FIXED),
            'always_ready': FlexRandomizer(FIFO_READY_CONSTRAINTS_ALWAYS),
            'fast_ready': FlexRandomizer(FIFO_READY_CONSTRAINTS_FAST),
            'slow_ready': FlexRandomizer(FIFO_READY_CONSTRAINTS_SLOW),
            'very_slow_ready': FlexRandomizer(FIFO_READY_CONSTRAINTS_VERY_SLOW)
        }

        self.error_randomizers = create_error_randomizers()

        # Create GAXI slave components for the split and error FIFOs
        self.split_slave = create_gaxi_slave(
            dut, "SplitSlave", "", dut.aclk,
            field_config=self.split_field_config,
            randomizer=self.split_randomizers['fast_ready'],
            log=self.log,
            multi_sig=True,
            signal_map={
                'm2s_valid': 'fub_split_valid',
                's2m_ready': 'fub_split_ready'
            },
            optional_signal_map={
                'm2s_pkt_addr': 'fub_split_addr',
                'm2s_pkt_id': 'fub_split_id',
                'm2s_pkt_cnt': 'fub_split_cnt'
            }
        )

        self.error_slave = create_gaxi_slave(
            dut, "ErrorSlave", "", dut.aclk,
            field_config=self.error_field_config,
            randomizer=self.error_randomizers['fast_ready'],
            log=self.log,
            multi_sig=True,
            signal_map={
                'm2s_valid': 'fub_error_valid',
                's2m_ready': 'fub_error_ready'
            },
            optional_signal_map={
                'm2s_pkt_type': 'fub_error_type',
                'm2s_pkt_addr': 'fub_error_addr',
                'm2s_pkt_id': 'fub_error_id'
            }
        )

        # Queues for tracking received information
        self.split_queue = deque()
        self.error_queue = deque()

        # Add callbacks to process received packets
        self.split_slave.add_callback(self._handle_split_info)
        self.error_slave.add_callback(self._handle_error_info)

        # For test verification
        self.expected_splits = {}  # Dict mapping ID to expected splits
        self.expected_errors = {}  # Dict mapping ID to expected errors
        self.total_errors = 0

        # Flag to control whether to check split info automatically
        self.check_splits_automatically = True

        # Performance metrics tracking
        self.initial_transaction_count = 0
        self.initial_byte_count = 0
        self.initial_latency_sum = 0

    def _handle_split_info(self, packet):
        """
        Process split information received from the DUT.

        Args:
            packet: GAXIPacket containing split information
        """
        if hasattr(packet, 'addr') and hasattr(packet, 'id') and hasattr(packet, 'cnt'):
            split_info = SplitInfo(
                addr=packet.addr,
                id=packet.id,
                cnt=packet.cnt
            )

            self.split_queue.append(split_info)
            self.log.info(f"Received split info @ {packet.start_time}ns: addr=0x{split_info.addr:08X}, id=0x{split_info.id:X}, cnt={split_info.cnt}")

            # Verify against expected splits if automatic checking is enabled
            if self.check_splits_automatically and split_info.id in self.expected_splits:
                expected = self.expected_splits[split_info.id]
                if expected != split_info.cnt:
                    self.log.error(f"Split mismatch for ID=0x{split_info.id:X}: expected={expected}, actual={split_info.cnt}")
                    self.total_errors += 1
                else:
                    self.log.debug(f"Split verification passed for ID=0x{split_info.id:X}: cnt={split_info.cnt}")

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
        """Reset the split and error interfaces."""
        await self.split_slave.reset_bus()
        await self.error_slave.reset_bus()

        # Clear queues
        self.split_queue.clear()
        self.error_queue.clear()

        # Reset verification state
        self.expected_splits.clear()
        self.expected_errors.clear()
        self.total_errors = 0

        self.log.info("Fub interfaces reset")

    def set_split_readiness(self, mode):
        """
        Set the readiness mode for the split interface.

        Args:
            mode: One of 'fixed', 'always_ready', 'fast_ready', 'slow_ready', 'very_slow_ready'
        """
        if mode in self.split_randomizers:
            self.split_slave.set_randomizer(self.split_randomizers[mode])
            self.log.info(f"Split interface readiness set to {mode}")
        else:
            self.log.error(f"Unknown split readiness mode: {mode}")

    def set_error_readiness(self, mode):
        """
        Set the readiness mode for the error interface.

        Args:
            mode: One of 'always_ready', 'fast_ready', 'slow_ready', 'very_slow_ready'
        """
        if mode in self.error_randomizers:
            self.error_slave.set_randomizer(self.error_randomizers[mode])
            self.log.info(f"Error interface readiness set to {mode}")
        else:
            self.log.error(f"Unknown error readiness mode: {mode}")

    def expect_split(self, id_value, cnt):
        """
        Register an expected split for a specific ID.

        Args:
            id_value: Transaction ID
            cnt: Expected number of splits
        """
        self.expected_splits[id_value] = cnt
        self.log.info(f"Expecting {cnt} splits for ID=0x{id_value:X}")

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

    async def wait_for_splits(self, count, timeout_ns=None):
        """
        Wait for a specific number of split notifications.

        Args:
            count: Number of splits to wait for
            timeout_ns: Timeout in nanoseconds (None for no timeout)

        Returns:
            True if the specified number of splits were received, False otherwise
        """
        start_time = cocotb.utils.get_sim_time('ns')
        current_count = len(self.split_queue)

        while current_count < count:
            # Check timeout
            if timeout_ns is not None:
                current_time = cocotb.utils.get_sim_time('ns')
                if current_time - start_time > timeout_ns:
                    self.log.warning(f"Timeout waiting for splits: received {current_count}/{count}")
                    return False

            # Wait for more splits
            await Timer(100, units='ns')
            current_count = len(self.split_queue)

        return True

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

        # Set both interfaces to fast response mode
        self.set_split_readiness('fast_ready')
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

    def verify_split_count(self, id_value, expected_count):
        """
        Verify that a transaction with the given ID was split the expected number of times.

        Args:
            id_value: Transaction ID
            expected_count: Expected number of splits

        Returns:
            True if the split count matches, False otherwise
        """
        # Find all split notifications for this ID
        splits_for_id = [s for s in self.split_queue if s.id == id_value]

        if not splits_for_id:
            self.log.error(f"No split notification found for ID=0x{id_value:X}")
            return False

        # Use the most recent split notification
        most_recent = splits_for_id[-1]
        actual_count = most_recent.cnt

        if actual_count != expected_count:
            self.log.error(f"Split count mismatch for ID=0x{id_value:X}: expected={expected_count}, actual={actual_count}")
            return False

        return True
