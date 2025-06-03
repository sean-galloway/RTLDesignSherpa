"""
AXI4 Transaction Sequence

This module provides a coordinator for complete AXI4 transactions, combining
address and data sequences for writes and reads, and managing transaction IDs
and dependencies.
"""

import random
import itertools
from typing import List, Dict, Any, Optional, Tuple, Union, Set
from collections import deque, defaultdict

from ..field_config import FieldConfig
from ..flex_randomizer import FlexRandomizer
from .axi4_packet import AXI4Packet
from .axi4_seq_address import AXI4AddressSequence
from .axi4_seq_data import AXI4DataSequence
from .axi4_seq_base import AXI4BaseSequence
from ..randomization_config import RandomizationConfig, RandomizationMode


class AXI4TransactionSequence(AXI4BaseSequence):
    """
    Coordinator for AXI4 transaction sequences combining address and data operations.

    This class manages complete AXI4 transactions by coordinating address and data
    sequences for both read and write operations, with ID management and dependency
    tracking.
    """

    def __init__(self, name: str = "axi4_transaction",
                    id_width: int = 8,
                    addr_width: int = 32,
                    data_width: int = 32,
                    user_width: int = 1,
                    randomization_config: Optional[RandomizationConfig] = None):
        """
        Initialize the AXI4 Transaction Sequence.

        Args:
            name: Sequence name
            id_width: Width of ID field in bits
            addr_width: Width of address field in bits
            data_width: Width of data field in bits
            user_width: Width of user field in bits
            randomization_config: Optional randomization configuration
        """
        super().__init__(name=name, randomization_config=randomization_config)

        self.id_width = id_width
        self.addr_width = addr_width
        self.data_width = data_width
        self.user_width = user_width

        # Create address sequences for write and read
        self.write_addr_sequence = AXI4AddressSequence(
            name=f"{name}_aw",
            channel="AW",
            id_width=id_width,
            addr_width=addr_width,
            user_width=user_width,
            randomization_config=randomization_config
        )

        self.read_addr_sequence = AXI4AddressSequence(
            name=f"{name}_ar",
            channel="AR",
            id_width=id_width,
            addr_width=addr_width,
            user_width=user_width,
            randomization_config=randomization_config
        )

        # Create data sequences for write and read
        self.write_data_sequence = AXI4DataSequence(
            name=f"{name}_w",
            channel="W",
            data_width=data_width,
            user_width=user_width,
            randomization_config=randomization_config
        )

        self.read_data_sequence = AXI4DataSequence(
            name=f"{name}_r",
            channel="R",
            data_width=data_width,
            user_width=user_width,
            randomization_config=randomization_config
        )

        # Transaction ID tracking
        self.write_id_counter = 0
        self.read_id_counter = 0
        self.used_write_ids = set()
        self.used_read_ids = set()

        # Transaction dependency tracking
        self.write_dependencies = {}  # id -> set of dependent IDs
        self.read_dependencies = {}   # id -> set of dependent IDs

        # Response tracking
        self.write_responses = {}  # id -> response packet
        self.read_responses = defaultdict(list)  # id -> list of response packets

        # Packet storage
        self.write_addr_packets = {}  # id -> packet
        self.write_data_packets = defaultdict(list)  # id -> list of packets
        self.read_addr_packets = {}  # id -> packet

        # Statistics
        self.stats.update({
            'write_transactions': 0,
            'read_transactions': 0,
            'dependencies': 0,
            'in_progress': 0,
            'completed': 0
        })

    def get_next_write_id(self) -> int:
        """
        Get the next available write transaction ID.

        Returns:
            Available transaction ID
        """
        # If all IDs are used, wrap around
        if len(self.used_write_ids) >= (1 << self.id_width):
            self.used_write_ids.clear()
            self.write_id_counter = 0

        # Find the next available ID
        while self.write_id_counter in self.used_write_ids:
            self.write_id_counter = (self.write_id_counter + 1) % (1 << self.id_width)

        # Mark this ID as used
        self.used_write_ids.add(self.write_id_counter)

        return self.write_id_counter

    def get_next_read_id(self) -> int:
        """
        Get the next available read transaction ID.

        Returns:
            Available transaction ID
        """
        # If all IDs are used, wrap around
        if len(self.used_read_ids) >= (1 << self.id_width):
            self.used_read_ids.clear()
            self.read_id_counter = 0

        # Find the next available ID
        while self.read_id_counter in self.used_read_ids:
            self.read_id_counter = (self.read_id_counter + 1) % (1 << self.id_width)

        # Mark this ID as used
        self.used_read_ids.add(self.read_id_counter)

        return self.read_id_counter

    def add_write_transaction(self,
                            addr: int,
                            data_values: List[int],
                            id_value: Optional[int] = None,
                            burst_size: int = 2,
                            burst_type: int = 1,
                            strb_values: Optional[List[int]] = None,
                            lock: int = 0,
                            cache: int = 0,
                            prot: int = 0,
                            qos: int = 0,
                            region: int = 0,
                            user: int = 0,
                            dependencies: Optional[List[int]] = None) -> int:
        """
        Add a write transaction with address and data.

        Args:
            addr: Target address
            data_values: List of data values for the burst
            id_value: Transaction ID (auto-generated if None)
            burst_size: Burst size (log2 of number of bytes)
            burst_type: Burst type (0=FIXED, 1=INCR, 2=WRAP)
            strb_values: List of strobe values
            lock: Lock type (0=Normal, 1=Exclusive)
            cache: Cache type
            prot: Protection type
            qos: Quality of Service
            region: Region identifier
            user: User signal
            dependencies: List of transaction IDs that must complete before this one

        Returns:
            Transaction ID
        """
        # Auto-generate ID if not provided
        if id_value is None:
            id_value = self.get_next_write_id()
        else:
            # Register externally provided ID
            self.used_write_ids.add(id_value)

        # Calculate burst length based on data values
        burst_len = len(data_values) - 1
        burst_len = max(burst_len, 0)
        # Calculate proper alignment for address
        alignment = 1 << burst_size
        aligned_addr = (addr // alignment) * alignment

        # Check if address needed alignment
        if aligned_addr != addr:
            self.log_warning(f"Address 0x{addr:X} not aligned for size {burst_size}, using 0x{aligned_addr:X}")

        # Validate burst parameters
        valid, msg = self.validate_burst_parameters(aligned_addr, burst_len, burst_size, burst_type)
        if not valid:
            self.log_warning(f"Burst parameter validation failed: {msg}")
            # Try to correct WRAP burst lengths
            if burst_type == self.BURST_WRAP and not self.is_power_of_two(burst_len + 1):
                burst_len = self.next_power_of_two(burst_len + 1) - 1
                self.log_info(f"Adjusted burst length to {burst_len} for WRAP burst")

        # Add address transaction
        self.write_addr_sequence.add_transaction(
            addr=aligned_addr,
            id_value=id_value,
            burst_len=burst_len,
            burst_size=burst_size,
            burst_type=burst_type,
            lock=lock,
            cache=cache,
            prot=prot,
            qos=qos,
            region=region,
            user=user
        )

        # Add data transactions
        if strb_values is None:
            # Default to all bytes enabled
            strb_mask = (1 << (self.data_width // 8)) - 1
            strb_values = [strb_mask] * len(data_values)

        # Ensure strb_values has the same length as data_values
        if len(strb_values) < len(data_values):
            # Pad with full strobes if list is too short
            strb_values = strb_values + [(1 << (self.data_width // 8)) - 1] * (len(data_values) - len(strb_values))

        # Add data burst
        self.write_data_sequence.add_burst(
            data_values=data_values,
            strb_values=strb_values,
            user_values=[user] * len(data_values)
        )

        # Register dependencies
        if dependencies:
            if id_value not in self.write_dependencies:
                self.write_dependencies[id_value] = set()
            self.write_dependencies[id_value].update(dependencies)
            self.stats['dependencies'] += len(dependencies)

        # Store transaction ID
        self.write_addr_packets[id_value] = self.write_addr_sequence.generate_packet()

        # Generate and store data packets
        data_packets = self.write_data_sequence.generate_packets(len(data_values))
        self.write_data_packets[id_value] = data_packets

        # Update statistics
        self.stats['write_transactions'] += 1
        self.stats['in_progress'] += 1

        return id_value

    def add_read_transaction(self,
                            addr: int,
                            burst_len: int = 0,
                            id_value: Optional[int] = None,
                            burst_size: int = 2,
                            burst_type: int = 1,
                            lock: int = 0,
                            cache: int = 0,
                            prot: int = 0,
                            qos: int = 0,
                            region: int = 0,
                            user: int = 0,
                            dependencies: Optional[List[int]] = None) -> int:
        """
        Add a read transaction with address and expected burst length.

        Args:
            addr: Target address
            burst_len: Burst length (0 = 1 beat, 255 = 256 beats)
            id_value: Transaction ID (auto-generated if None)
            burst_size: Burst size (log2 of number of bytes)
            burst_type: Burst type (0=FIXED, 1=INCR, 2=WRAP)
            lock: Lock type (0=Normal, 1=Exclusive)
            cache: Cache type
            prot: Protection type
            qos: Quality of Service
            region: Region identifier
            user: User signal
            dependencies: List of transaction IDs that must complete before this one

        Returns:
            Transaction ID
        """
        # Auto-generate ID if not provided
        if id_value is None:
            id_value = self.get_next_read_id()
        else:
            # Register externally provided ID
            self.used_read_ids.add(id_value)

        # Calculate proper alignment for address
        alignment = 1 << burst_size
        aligned_addr = (addr // alignment) * alignment

        # Check if address needed alignment
        if aligned_addr != addr:
            self.log_warning(f"Address 0x{addr:X} not aligned for size {burst_size}, using 0x{aligned_addr:X}")

        # Validate burst parameters
        valid, msg = self.validate_burst_parameters(aligned_addr, burst_len, burst_size, burst_type)
        if not valid:
            self.log_warning(f"Burst parameter validation failed: {msg}")
            # Try to correct WRAP burst lengths
            if burst_type == self.BURST_WRAP and not self.is_power_of_two(burst_len + 1):
                burst_len = self.next_power_of_two(burst_len + 1) - 1
                self.log_info(f"Adjusted burst length to {burst_len} for WRAP burst")

        # Add address transaction
        self.read_addr_sequence.add_transaction(
            addr=aligned_addr,
            id_value=id_value,
            burst_len=burst_len,
            burst_size=burst_size,
            burst_type=burst_type,
            lock=lock,
            cache=cache,
            prot=prot,
            qos=qos,
            region=region,
            user=user
        )

        # Register dependencies
        if dependencies:
            if id_value not in self.read_dependencies:
                self.read_dependencies[id_value] = set()
            self.read_dependencies[id_value].update(dependencies)
            self.stats['dependencies'] += len(dependencies)

        # Store transaction ID and packet
        self.read_addr_packets[id_value] = self.read_addr_sequence.generate_packet()

        # Update statistics
        self.stats['read_transactions'] += 1
        self.stats['in_progress'] += 1

        return id_value

    def add_read_response_data(self,
                                id_value: int,
                                data_values: List[int],
                                resp_values: Optional[List[int]] = None,
                                user: int = 0) -> 'AXI4TransactionSequence':
        """
        Add expected read response data for a specific transaction ID.
        Typically used when simulating expected responses.

        Args:
            id_value: Transaction ID
            data_values: List of data values expected in response
            resp_values: List of response codes (0=OKAY, etc.)
            user: User signal

        Returns:
            Self for method chaining
        """
        # Default resp values if not provided
        if resp_values is None:
            resp_values = [0] * len(data_values)  # All OKAY

        # Ensure resp_values has the same length as data_values
        if len(resp_values) < len(data_values):
            # Pad with OKAY responses if list is too short
            resp_values = resp_values + [0] * (len(data_values) - len(resp_values))

        # Add expected response data to read data sequence
        for i, data in enumerate(data_values):
            is_last = (i == len(data_values) - 1)

            self.read_data_sequence.add_transaction(
                data=data,
                last=is_last,
                user=user,
                id_value=id_value,
                resp=resp_values[i]
            )

        # Generate and store response packets
        response_packets = self.read_data_sequence.generate_packets(len(data_values))
        self.read_responses[id_value] = response_packets

        return self

    def add_write_response(self,
                            id_value: int,
                            resp: int = 0,
                            user: int = 0) -> 'AXI4TransactionSequence':
        """
        Add a write response for a specific transaction ID.
        Typically used when simulating expected responses.

        Args:
            id_value: Transaction ID
            resp: Response code (0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)
            user: User signal

        Returns:
            Self for method chaining
        """
        # Create B packet with given response
        b_packet = AXI4Packet.create_b_packet(
            bid=id_value,
            bresp=resp,
            buser=user
        )

        # Store response
        self.write_responses[id_value] = b_packet

        return self

    def complete_transaction(self, id_value: int, is_read: bool = False) -> bool:
        """
        Mark a transaction as complete.

        Args:
            id_value: Transaction ID to complete
            is_read: True if this is a read transaction, False for write

        Returns:
            True if transaction was completed, False if not found or already complete
        """
        if is_read:
            if id_value in self.read_addr_packets:
                # Mark as complete
                if id_value in self.read_dependencies:
                    del self.read_dependencies[id_value]
                self.stats['completed'] += 1
                self.stats['in_progress'] -= 1
                return True
        elif id_value in self.write_addr_packets:
            # Mark as complete
            if id_value in self.write_dependencies:
                del self.write_dependencies[id_value]
            self.stats['completed'] += 1
            self.stats['in_progress'] -= 1
            return True

        return False

    def get_dependencies(self, id_value: int, is_read: bool = False) -> Set[int]:
        """
        Get the set of transaction IDs that a specific transaction depends on.

        Args:
            id_value: Transaction ID to check
            is_read: True if this is a read transaction, False for write

        Returns:
            Set of transaction IDs that must complete before this one
        """
        dependencies = set()

        if is_read:
            if id_value in self.read_dependencies:
                dependencies.update(self.read_dependencies[id_value])
        elif id_value in self.write_dependencies:
            dependencies.update(self.write_dependencies[id_value])

        return dependencies

    def has_dependency(self, id_value: int, dependency_id: int, is_read: bool = False) -> bool:
        """
        Check if a transaction has a specific dependency.

        Args:
            id_value: Transaction ID to check
            dependency_id: Dependency ID to look for
            is_read: True if this is a read transaction, False for write

        Returns:
            True if dependency_id is in the dependencies for id_value
        """
        dependencies = self.get_dependencies(id_value, is_read)
        return dependency_id in dependencies

    def get_write_ids(self) -> List[int]:
        """
        Get all write transaction IDs.

        Returns:
            List of all write transaction IDs
        """
        return list(self.write_addr_packets.keys())

    def get_read_ids(self) -> List[int]:
        """
        Get all read transaction IDs.

        Returns:
            List of all read transaction IDs
        """
        return list(self.read_addr_packets.keys())

    def get_write_addr_packet(self, id_value: int) -> Optional[AXI4Packet]:
        """
        Get the write address packet for a specific transaction ID.

        Args:
            id_value: Transaction ID

        Returns:
            Write address packet or None if not found
        """
        return self.write_addr_packets.get(id_value)

    def get_write_data_packets(self, id_value: int) -> List[AXI4Packet]:
        """
        Get write data packets for a specific transaction ID.

        Args:
            id_value: Transaction ID

        Returns:
            List of write data packets or empty list if not found
        """
        return self.write_data_packets.get(id_value, [])

    def get_read_addr_packet(self, id_value: int) -> Optional[AXI4Packet]:
        """
        Get the read address packet for a specific transaction ID.

        Args:
            id_value: Transaction ID

        Returns:
            Read address packet or None if not found
        """
        return self.read_addr_packets.get(id_value)

    def get_read_response_packets(self, id_value: int) -> List[AXI4Packet]:
        """
        Get read response packets for a specific transaction ID.

        Args:
            id_value: Transaction ID

        Returns:
            List of read response packets or empty list if not found
        """
        return self.read_responses.get(id_value, [])

    def get_write_response_packet(self, id_value: int) -> Optional[AXI4Packet]:
        """
        Get the write response packet for a specific transaction ID.

        Args:
            id_value: Transaction ID

        Returns:
            Write response packet or None if not found
        """
        return self.write_responses.get(id_value)

    def get_ready_transactions(self, is_read: bool = False) -> List[int]:
        """
        Get list of transaction IDs that are ready to execute (no pending dependencies).

        Args:
            is_read: True for read transactions, False for write

        Returns:
            List of transaction IDs ready to execute
        """
        ready_ids = []

        if is_read:
            ready_ids.extend(
                id_value
                for id_value in self.read_addr_packets.keys()
                if id_value not in self.read_dependencies
                or not self.read_dependencies[id_value]
            )
        else:
            ready_ids.extend(
                id_value
                for id_value in self.write_addr_packets.keys()
                if id_value not in self.write_dependencies
                or not self.write_dependencies[id_value]
            )
        return ready_ids

    def get_pending_transactions(self, is_read: bool = False) -> List[int]:
        """
        Get list of transaction IDs that are pending (have dependencies).

        Args:
            is_read: True for read transactions, False for write

        Returns:
            List of transaction IDs that are pending
        """
        pending_ids = []

        if is_read:
            pending_ids.extend(
                id_value
                for id_value in self.read_addr_packets.keys()
                if id_value in self.read_dependencies
                and self.read_dependencies[id_value]
            )
        else:
            pending_ids.extend(
                id_value
                for id_value in self.write_addr_packets.keys()
                if id_value in self.write_dependencies
                and self.write_dependencies[id_value]
            )
        return pending_ids

    def set_random_selection(self, enable: bool = True) -> 'AXI4TransactionSequence':
        """
        Enable/disable random selection from sequences.

        Args:
            enable: True to enable random selection, False to use sequential

        Returns:
            Self for method chaining
        """
        self.use_random_selection = enable

        # Propagate to component sequences
        self.write_addr_sequence.set_random_selection(enable)
        self.write_data_sequence.set_random_selection(enable)
        self.read_addr_sequence.set_random_selection(enable)
        self.read_data_sequence.set_random_selection(enable)

        return self

    def cleanup(self) -> None:
        """
        Release resources to prevent memory leaks.
        """
        # Clean up component sequences
        self.write_addr_sequence.cleanup()
        self.write_data_sequence.cleanup()
        self.read_addr_sequence.cleanup()
        self.read_data_sequence.cleanup()

        # Clear tracking structures
        self.used_write_ids.clear()
        self.used_read_ids.clear()
        self.write_dependencies.clear()
        self.read_dependencies.clear()
        self.write_responses.clear()
        self.read_responses.clear()
        self.write_addr_packets.clear()
        self.write_data_packets.clear()
        self.read_addr_packets.clear()

        # Call base class cleanup
        super().cleanup()

    def get_stats(self) -> Dict[str, Any]:
        """
        Get statistics about the transaction sequence.

        Returns:
            Dictionary with statistics
        """
        # Combine stats from all sequences
        combined_stats = self.stats.copy()
        combined_stats['write_addr'] = self.write_addr_sequence.get_stats()
        combined_stats['write_data'] = self.write_data_sequence.get_stats()
        combined_stats['read_addr'] = self.read_addr_sequence.get_stats()
        combined_stats['read_data'] = self.read_data_sequence.get_stats()

        # Add pending counts
        combined_stats['pending_writes'] = len(self.get_pending_transactions(False))
        combined_stats['pending_reads'] = len(self.get_pending_transactions(True))
        combined_stats['ready_writes'] = len(self.get_ready_transactions(False))
        combined_stats['ready_reads'] = len(self.get_ready_transactions(True))

        return combined_stats

    # ========================================================================
    # Utility Methods
    # ========================================================================

    def get_burst_addresses(self, id_value: int, is_read: bool = False) -> List[int]:
        """
        Get all addresses in a burst for a specific transaction.

        Args:
            id_value: Transaction ID
            is_read: True if this is a read transaction, False for write

        Returns:
            List of addresses in the burst, or empty list if transaction not found
        """
        # Get the packet for this transaction
        packet = None
        if is_read:
            packet = self.read_addr_packets.get(id_value)
        else:
            packet = self.write_addr_packets.get(id_value)

        if not packet:
            return []

        # Get burst parameters from packet
        if is_read:
            addr = packet.araddr
            burst_len = packet.arlen
            burst_size = packet.arsize
            burst_type = packet.arburst
        else:
            addr = packet.awaddr
            burst_len = packet.awlen
            burst_size = packet.awsize
            burst_type = packet.awburst

        # Calculate addresses
        return self.calculate_burst_addresses(addr, burst_len, burst_size, burst_type)

    def get_transaction_data(self, id_value: int, is_read: bool = False) -> List[int]:
        """
        Get data values for a specific transaction.

        Args:
            id_value: Transaction ID
            is_read: True if this is a read response, False for write data

        Returns:
            List of data values, or empty list if transaction not found
        """
        data_values = []

        if is_read:
            # Get read response packets
            packets = self.get_read_response_packets(id_value)
            data_values.extend(packet.rdata for packet in packets)
        else:
            # Get write data packets
            packets = self.get_write_data_packets(id_value)
            data_values.extend(packet.wdata for packet in packets)
        return data_values

    # ========================================================================
    # Factory Methods
    # ========================================================================

    @classmethod
    def create_x_boundary_test(cls, alignment_mask=0xFFF, channel="AR",
                            base_addr=0,  # Add base_addr parameter
                            data_width=32, id_width=8, addr_width=32,
                            user_width=1, randomization_config=None):
        """
        Create a transaction sequence that tests boundary conditions with configurable boundary size.

        Args:
            alignment_mask: Alignment mask that defines the boundary (e.g., 0xFFF for 4KB boundary)
            channel: Target channel, "AR" for reads or "AW" for writes (or "BOTH" for both)
            base_addr: Base address for the test (can be used to test different pages)
            data_width: Width of data in bits
            id_width: Width of ID field in bits
            addr_width: Width of address field in bits
            user_width: Width of user field in bits
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4TransactionSequence
        """
        # Calculate the boundary size for the name
        boundary_size = alignment_mask + 1

        # Create a transaction sequence
        sequence = cls(
            name=f"{boundary_size}b_boundary_test",
            id_width=id_width,
            addr_width=addr_width,
            data_width=data_width,
            user_width=user_width,
            randomization_config=randomization_config
        )

        # Determine which channels to create tests for
        channels = []
        if channel.upper() == "BOTH":
            channels = ["AR", "AW"]
        else:
            channels = [channel.upper()]

        # Process each requested channel
        id_offset = 0
        for ch in channels:
            # Create address sequence for boundary testing
            # Pass through the base_addr parameter
            addr_sequence = AXI4AddressSequence.create_x_boundary_test(
                alignment_mask=alignment_mask,
                channel=ch,
                base_addr=base_addr,
                id_value=id_offset,
                data_width=data_width
            )

            # Generate packets from the address sequence
            addr_packets = addr_sequence.generate_packets()

            # Convert address sequence transactions to transaction sequence
            for packet in addr_packets:
                if ch == "AR":
                    # Add read transaction from address packet
                    sequence.add_read_transaction(
                        addr=packet.araddr,
                        id_value=packet.arid,
                        burst_len=packet.arlen,
                        burst_size=packet.arsize,
                        burst_type=packet.arburst
                    )
                else:  # AW
                    # For write transactions, we need data values
                    # Calculate number of data transfers needed
                    burst_len = packet.awlen
                    data_count = burst_len + 1

                    # Create data values (using a pattern based on ID and address)
                    data_values = [(0xA0000000 + packet.awid*0x100 + j) for j in range(data_count)]

                    # Add write transaction with data
                    sequence.add_write_transaction(
                        addr=packet.awaddr,
                        id_value=packet.awid,
                        data_values=data_values,
                        # burst_len=packet.awlen,
                        burst_size=packet.awsize,
                        burst_type=packet.awburst
                    )

            # Update ID offset for next channel
            id_offset += len(addr_packets)

        return sequence

    @classmethod
    def create_simple_writes(cls,
                            addrs: List[int],
                            data_values: List[List[int]],
                            id_values: Optional[List[int]] = None,
                            data_width: int = 32,
                            randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4TransactionSequence':
        """
        Create a sequence of simple write transactions.

        Args:
            addrs: List of addresses
            data_values: List of data bursts (each item is a list of values for one burst)
            id_values: List of transaction IDs to use (auto-generated if None)
            data_width: Width of data in bits
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4TransactionSequence
        """
        sequence = cls(name="simple_writes", data_width=data_width,
                        randomization_config=randomization_config)

        # Create transactions
        for i, addr in enumerate(addrs):
            # Get data for this transaction
            if i < len(data_values):
                data = data_values[i]
            else:
                data = [0]  # Default if not enough data provided

            # Get ID for this transaction
            id_value = None
            if id_values and i < len(id_values):
                id_value = id_values[i]

            # Add transaction
            sequence.add_write_transaction(addr, data, id_value)

        return sequence

    @classmethod
    def create_simple_reads(cls,
                            addrs: List[int],
                            burst_lens: List[int],
                            id_values: Optional[List[int]] = None,
                            data_width: int = 32,
                            randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4TransactionSequence':
        """
        Create a sequence of simple read transactions.

        Args:
            addrs: List of addresses
            burst_lens: List of burst lengths
            id_values: List of transaction IDs to use (auto-generated if None)
            data_width: Width of data in bits
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4TransactionSequence
        """
        sequence = cls(name="simple_reads", data_width=data_width,
                        randomization_config=randomization_config)

        # Create transactions
        for i, addr in enumerate(addrs):
            # Get burst length for this transaction
            if i < len(burst_lens):
                burst_len = burst_lens[i]
            else:
                burst_len = 0  # Default if not enough burst lengths provided

            # Get ID for this transaction
            id_value = None
            if id_values and i < len(id_values):
                id_value = id_values[i]

            # Add transaction
            sequence.add_read_transaction(addr, burst_len, id_value)

        return sequence

    @classmethod
    def create_incrementing_writes(cls,
                                    start_addr: int = 0,
                                    count: int = 10,
                                    data_width: int = 32,
                                    randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4TransactionSequence':
        """
        Create a sequence of write transactions with incrementing addresses and data.

        Args:
            start_addr: Starting address
            count: Number of transactions
            data_width: Width of data in bits
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4TransactionSequence
        """
        sequence = cls(name="incrementing_writes", data_width=data_width,
                        randomization_config=randomization_config)

        # Byte increment based on data width
        addr_increment = data_width // 8

        # Create transactions
        for i in range(count):
            addr = start_addr + (i * addr_increment)
            data = [i]  # Single beat with incrementing value

            # Add transaction
            sequence.add_write_transaction(addr, data)

        return sequence

    @classmethod
    def create_read_after_write(cls,
                                addrs: List[int],
                                data_values: List[List[int]],
                                data_width: int = 32,
                                randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4TransactionSequence':
        """
        Create a sequence where each address is first written, then read.

        Args:
            addrs: List of addresses
            data_values: List of data bursts for writes
            data_width: Width of data in bits
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4TransactionSequence with read-after-write dependencies
        """
        sequence = cls(name="read_after_write", data_width=data_width,
                        randomization_config=randomization_config)

        # Create write transactions and corresponding reads
        for i, addr in enumerate(addrs):
            # Get data for this transaction
            if i < len(data_values):
                data = data_values[i]
            else:
                data = [0]  # Default if not enough data provided

            # Add write transaction
            write_id = sequence.add_write_transaction(addr, data)

            # Add corresponding read transaction dependent on the write
            burst_len = len(data) - 1
            read_id = sequence.add_read_transaction(
                addr=addr,
                burst_len=burst_len,
                dependencies=[write_id]  # Make read depend on write
            )

            # Add expected response data
            sequence.add_read_response_data(read_id, data)

        return sequence

    @classmethod
    def create_burst_variations(cls,
                                start_addr: int = 0,
                                data_width: int = 32,
                                randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4TransactionSequence':
        """
        Create a sequence with various burst types and lengths.

        Args:
            start_addr: Starting address
            data_width: Width of data in bits
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4TransactionSequence
        """
        sequence = cls(name="burst_variations", data_width=data_width,
                        randomization_config=randomization_config)

        # Test parameters
        burst_types = [1, 2, 0]  # INCR, WRAP, FIXED
        burst_lengths = [0, 1, 3, 7, 15]  # 1, 2, 4, 8, 16 transfers
        burst_sizes = [2, 3]  # 4, 8 bytes

        # Byte increment for address spacing
        addr_increment = 64

        # Create transactions
        addr = start_addr
        for burst_type, burst_size, burst_len in itertools.product(burst_types, burst_sizes, burst_lengths):
            # Skip invalid combinations (WRAP bursts with lengths not 2^n)
            if burst_type == sequence.BURST_WRAP and not sequence.is_power_of_two(burst_len + 1):
                continue

            # Create data values for the burst
            data_values = [0xA0000000 + i for i in range(burst_len + 1)]

            # Add write transaction
            write_id = sequence.add_write_transaction(
                addr=addr,
                data_values=data_values,
                burst_size=burst_size,
                burst_type=burst_type
            )

            # Add read transaction for the same burst
            read_id = sequence.add_read_transaction(
                addr=addr,
                burst_len=burst_len,
                burst_size=burst_size,
                burst_type=burst_type,
                dependencies=[write_id]
            )

            # Add expected response data
            sequence.add_read_response_data(read_id, data_values)

            # Increment address
            addr += addr_increment

        return sequence

    @classmethod
    def create_exclusive_access_test(cls,
                                    addrs: List[int],
                                    data_values: List[int],
                                    data_width: int = 32,
                                    randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4TransactionSequence':
        """
        Create a sequence testing exclusive access.

        Args:
            addrs: List of addresses to test
            data_values: Data values to write
            data_width: Width of data in bits
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4TransactionSequence with exclusive access patterns
        """
        sequence = cls(name="exclusive_access", data_width=data_width,
                        randomization_config=randomization_config)

        # For each address, perform exclusive read followed by exclusive write
        for i, addr in enumerate(addrs):
            # Get data for this transaction
            data = data_values[i % len(data_values)]

            # First, do a regular write to initialize
            init_write_id = sequence.add_write_transaction(
                addr=addr,
                data_values=[data]
            )

            # Add exclusive read
            read_id = sequence.add_read_transaction(
                addr=addr,
                burst_len=0,  # Single transfer
                lock=1,  # Exclusive access
                dependencies=[init_write_id]
            )

            # Add expected response for read
            sequence.add_read_response_data(read_id, [data])

            # Add exclusive write dependent on the read
            write_id = sequence.add_write_transaction(
                addr=addr,
                data_values=[data + 1],  # Increment the data
                lock=1,  # Exclusive access
                dependencies=[read_id]  # Write depends on read
            )

            # Add write response with EXOKAY
            sequence.add_write_response(write_id, cls.RESP_EXOKAY)

        return sequence

    @classmethod
    def create_protocol_stress_test(cls,
                                    data_width: int = 32,
                                    randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4TransactionSequence':
        """
        Create a comprehensive test of AXI4 protocol features.

        Args:
            data_width: Width of data in bits
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4TransactionSequence with protocol stress patterns
        """
        sequence = cls(name="protocol_stress", data_width=data_width,
                        randomization_config=randomization_config)

        # Base address for different test sections
        addr = 0x10000000

        # 1. Basic single beat transactions
        for i in range(5):
            # Write
            write_id = sequence.add_write_transaction(
                addr=addr + (i*4),
                data_values=[i]
            )

            # Read with dependency
            read_id = sequence.add_read_transaction(
                addr=addr + (i*4),
                burst_len=0,
                dependencies=[write_id]
            )

            # Add expected response
            sequence.add_read_response_data(read_id, [i])

        addr += 0x1000

        # 2. INCR burst transactions
        for length in [1, 3, 7, 15]:
            data_values = [0xA0000000 + i for i in range(length + 1)]

            # Write
            write_id = sequence.add_write_transaction(
                addr=addr,
                data_values=data_values,
                burst_type=cls.BURST_INCR
            )

            # Read with dependency
            read_id = sequence.add_read_transaction(
                addr=addr,
                burst_len=length,
                burst_type=cls.BURST_INCR,
                dependencies=[write_id]
            )

            # Add expected response
            sequence.add_read_response_data(read_id, data_values)

            addr += 0x100

        # 3. WRAP burst transactions
        for length in [1, 3, 7, 15]:
            data_values = [0xB0000000 + i for i in range(length + 1)]

            # Write
            write_id = sequence.add_write_transaction(
                addr=addr,
                data_values=data_values,
                burst_type=cls.BURST_WRAP
            )

            # Read with dependency
            read_id = sequence.add_read_transaction(
                addr=addr,
                burst_len=length,
                burst_type=cls.BURST_WRAP,
                dependencies=[write_id]
            )

            # Add expected response
            sequence.add_read_response_data(read_id, data_values)

            addr += 0x100

        # 4. FIXED burst transactions (limited to shorter bursts)
        for length in [1, 3]:
            data_values = [0xC0000000 + i for i in range(length + 1)]

            # Write
            write_id = sequence.add_write_transaction(
                addr=addr,
                data_values=data_values,
                burst_type=cls.BURST_FIXED
            )

            # Read with dependency
            read_id = sequence.add_read_transaction(
                addr=addr,
                burst_len=length,
                burst_type=cls.BURST_FIXED,
                dependencies=[write_id]
            )

            # Add expected response
            sequence.add_read_response_data(read_id, data_values)

            addr += 0x100

        # 5. Exclusive access pattern
        # First, normal write to initialize memory
        write_id = sequence.add_write_transaction(
            addr=addr,
            data_values=[0xD0000000]
        )

        # Exclusive read
        read_id = sequence.add_read_transaction(
            addr=addr,
            burst_len=0,  # Single beat
            lock=1,  # Exclusive
            dependencies=[write_id]
        )

        # Add expected read response
        sequence.add_read_response_data(read_id, [0xD0000000])

        # Exclusive write
        excl_write_id = sequence.add_write_transaction(
            addr=addr,
            data_values=[0xD0000001],  # Modify the value
            lock=1,  # Exclusive
            dependencies=[read_id]
        )

        # Add EXOKAY response for exclusive write
        sequence.add_write_response(excl_write_id, cls.RESP_EXOKAY)

        # Regular read to verify exclusive write
        final_read_id = sequence.add_read_transaction(
            addr=addr,
            dependencies=[excl_write_id]
        )

        # Add expected response showing updated value
        sequence.add_read_response_data(final_read_id, [0xD0000001])

        addr += 0x100

        # 6. Different burst sizes
        for size in [0, 1, 2, 3]:  # 1, 2, 4, 8 bytes
            # Align address to burst size
            byte_count = 1 << size
            aligned_addr = (addr // byte_count) * byte_count

            # Create data
            data_values = [0xE0000000 + i for i in range(4)]

            # Write
            write_id = sequence.add_write_transaction(
                addr=aligned_addr,
                data_values=data_values,
                burst_size=size,
                burst_type=cls.BURST_INCR
            )

            # Read with dependency
            read_id = sequence.add_read_transaction(
                addr=aligned_addr,
                burst_len=3,  # 4 beats
                burst_size=size,
                burst_type=cls.BURST_INCR,
                dependencies=[write_id]
            )

            # Add expected response
            sequence.add_read_response_data(read_id, data_values)

            addr += 0x100

        # 7. Different protection attributes
        for prot in range(8):
            # Write
            write_id = sequence.add_write_transaction(
                addr=addr + (prot * 4),
                data_values=[0xF0000000 + prot],
                prot=prot
            )

            # Read with dependency and same protection
            read_id = sequence.add_read_transaction(
                addr=addr + (prot * 4),
                burst_len=0,  # Single beat
                prot=prot,
                dependencies=[write_id]
            )

            # Add expected response
            sequence.add_read_response_data(read_id, [0xF0000000 + prot])

        # 8. Byte strobes (partial writes)
        addr += 0x100
        strobe_patterns = [0x1, 0x3, 0x7, 0xF, 0x5, 0xA]

        for i, strb in enumerate(strobe_patterns):
            # Partial write with specific strobe
            write_id = sequence.add_write_transaction(
                addr=addr + (i * 4),
                data_values=[0xFFFFFFFF],  # All ones
                strb_values=[strb]  # Partial strobe
            )

            # Read to verify partial write
            read_id = sequence.add_read_transaction(
                addr=addr + (i * 4),
                dependencies=[write_id]
            )

            # The expected result depends on strobe pattern:
            # Only bytes with active strobe bits should be written
            expected = 0
            for bit in range(4):  # Assuming 4 bytes (32-bit data)
                if strb & (1 << bit):
                    # This byte was written with 0xFF
                    expected |= 0xFF << (bit * 8)

            # Add expected response
            sequence.add_read_response_data(read_id, [expected])

        # 9. Error responses
        addr += 0x100

        # Add a read to an unmapped address expecting DECERR
        unmapped_read_id = sequence.add_read_transaction(
            addr=0xF0000000  # Assumed to be unmapped
        )

        # Add expected error response
        sequence.add_read_response_data(
            unmapped_read_id,
            [0],  # Data (likely don't care)
            [cls.RESP_DECERR]  # DECERR response
        )

        # Add a write to an unmapped address
        unmapped_write_id = sequence.add_write_transaction(
            addr=0xF0000000,  # Assumed to be unmapped
            data_values=[0xDEADBEEF]
        )

        # Add expected error response
        sequence.add_write_response(
            unmapped_write_id,
            cls.RESP_DECERR  # DECERR response
        )

        return sequence

    @classmethod
    def create_random_transactions(cls,
                                count: int = 10,
                                addr_range: Tuple[int, int] = (0, 0xFFFF),
                                id_range: Tuple[int, int] = (0, 15),
                                data_width: int = 32,
                                min_size: int = 0,  # Add min_size parameter with default 0
                                randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4TransactionSequence':
        """
        Create a sequence of random but legal AXI4 transactions.

        Args:
            count: Number of transactions to generate
            addr_range: (min, max) address range
            id_range: (min, max) ID range
            data_width: Width of data in bits
            min_size: Minimum size parameter (log2 of bytes per transfer)
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4TransactionSequence
        """
        sequence = cls(name="random_transactions",
                    data_width=data_width,
                    randomization_config=randomization_config)

        # Create address sequence for random address generation
        addr_sequence = AXI4AddressSequence.create_random_transactions(
            count=count,
            addr_range=addr_range,
            id_range=id_range,
            channel="AR",  # Use read channel for addresses
            randomization_config=randomization_config
        )

        # Generate the address packets
        addr_packets = addr_sequence.generate_packets(count)

        # Create both read and write transactions with the random addresses
        for i, packet in enumerate(addr_packets):
            # Extract address parameters
            addr = packet.araddr if hasattr(packet, 'araddr') else 0
            id_value = packet.arid if hasattr(packet, 'arid') else 0
            burst_len = packet.arlen if hasattr(packet, 'arlen') else 0

            # Apply min_size constraint to ensure size is at least the minimum supported
            if hasattr(packet, 'arsize'):
                burst_size = max(packet.arsize, min_size)
            else:
                burst_size = max(2, min_size)  # Default to word size if not specified

            burst_type = packet.arburst if hasattr(packet, 'arburst') else 1

            if i % 2 == 0:  # Even indices: create write transactions
                # Generate random data for write
                data_values = []
                for _ in range(burst_len + 1):
                    # Random data value in the range that fits data_width
                    data_value = random.randint(0, (1 << data_width) - 1)
                    data_values.append(data_value)

                # Add write transaction
                sequence.add_write_transaction(
                    addr=addr,
                    data_values=data_values,
                    id_value=id_value,
                    burst_size=burst_size,
                    burst_type=burst_type
                )
            else:  # Odd indices: create read transactions
                # Add read transaction
                sequence.add_read_transaction(
                    addr=addr,
                    burst_len=burst_len,
                    id_value=id_value,
                    burst_size=burst_size,
                    burst_type=burst_type
                )

        return sequence