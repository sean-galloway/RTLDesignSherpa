"""
AXI4 Transaction Sequence

This module provides a coordinator for complete AXI4 transactions, combining
address and data sequences for writes and reads, and managing transaction IDs
and dependencies.
"""

import random
from typing import List, Dict, Any, Optional, Tuple, Union, Set
from collections import deque

from CocoTBFramework.components.field_config import FieldConfig
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.axi4.axi4_packet import AXI4Packet
from CocoTBFramework.components.axi4.axi4_address_sequence import AXI4AddressSequence
from CocoTBFramework.components.axi4.axi4_data_sequence import AXI4DataSequence


class AXI4TransactionSequence:
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
                 user_width: int = 1):
        """
        Initialize the AXI4 Transaction Sequence.

        Args:
            name: Sequence name
            id_width: Width of ID field in bits
            addr_width: Width of address field in bits
            data_width: Width of data field in bits
            user_width: Width of user field in bits
        """
        self.name = name
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
            user_width=user_width
        )
        
        self.read_addr_sequence = AXI4AddressSequence(
            name=f"{name}_ar", 
            channel="AR",
            id_width=id_width,
            addr_width=addr_width,
            user_width=user_width
        )
        
        # Create data sequences for write and read
        self.write_data_sequence = AXI4DataSequence(
            name=f"{name}_w",
            channel="W",
            data_width=data_width,
            user_width=user_width
        )
        
        self.read_data_sequence = AXI4DataSequence(
            name=f"{name}_r",
            channel="R",
            data_width=data_width,
            user_width=user_width
        )
        
        # Create Write Response (B) sequence
        self.write_resp_sequence = []
        
        # Transaction ID tracking
        self.write_id_counter = 0
        self.read_id_counter = 0
        self.used_write_ids = set()
        self.used_read_ids = set()
        
        # Transaction dependency tracking
        self.write_dependencies = {}  # id -> set of dependent IDs
        self.read_dependencies = {}   # id -> set of dependent IDs
        
        # Randomization options
        self.randomizer = None
        self.use_random_selection = False
        
        # Statistics
        self.stats = {
            'write_transactions': 0,
            'read_transactions': 0,
            'dependencies': 0
        }

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
        if burst_len < 0:
            burst_len = 0
        
        # Calculate proper alignment for address
        alignment = 1 << burst_size
        aligned_addr = (addr // alignment) * alignment
        
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
        
        # Update statistics
        self.stats['write_transactions'] += 1
        
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
        
        # Update statistics
        self.stats['read_transactions'] += 1
        
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
        
        # Add data for each beat
        for i, data in enumerate(data_values):
            is_last = (i == len(data_values) - 1)
            
            self.read_data_sequence.add_transaction(
                data=data,
                last=is_last,
                user=user,
                id_value=id_value,
                resp=resp_values[i]
            )
        
        return self

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
        else:
            if id_value in self.write_dependencies:
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
        # Extract IDs from the address sequence
        ids = []
        for i in range(len(self.write_addr_sequence.id_sequence)):
            id_value = self.write_addr_sequence.id_sequence[i]
            if id_value not in ids:
                ids.append(id_value)
        
        return ids

    def get_read_ids(self) -> List[int]:
        """
        Get all read transaction IDs.
        
        Returns:
            List of all read transaction IDs
        """
        # Extract IDs from the address sequence
        ids = []
        for i in range(len(self.read_addr_sequence.id_sequence)):
            id_value = self.read_addr_sequence.id_sequence[i]
            if id_value not in ids:
                ids.append(id_value)
        
        return ids

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

    def set_randomizer(self, randomizer: FlexRandomizer) -> 'AXI4TransactionSequence':
        """
        Set the randomizer for timing constraints.

        Args:
            randomizer: FlexRandomizer instance
            
        Returns:
            Self for method chaining
        """
        self.randomizer = randomizer
        
        # Propagate to component sequences
        self.write_addr_sequence.set_randomizer(randomizer)
        self.write_data_sequence.set_randomizer(randomizer)
        self.read_addr_sequence.set_randomizer(randomizer)
        self.read_data_sequence.set_randomizer(randomizer)
        
        return self

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
        # Find the transaction by ID
        if is_read:
            addr_sequence = self.read_addr_sequence
        else:
            addr_sequence = self.write_addr_sequence
        
        # Look up transaction
        for i, tx_id in enumerate(addr_sequence.id_sequence):
            if tx_id == id_value:
                # Found it, calculate burst addresses
                addr = addr_sequence.addr_sequence[i]
                burst_len = addr_sequence.len_sequence[i]
                burst_size = addr_sequence.size_sequence[i]
                burst_type = addr_sequence.burst_sequence[i]
                
                return addr_sequence.calculate_burst_addresses(
                    addr, burst_len, burst_size, burst_type
                )
                
        # Transaction not found
        return []

    def get_transaction_data(self, id_value: int, is_read: bool = False) -> List[int]:
        """
        Get data values for a specific transaction.
        
        Args:
            id_value: Transaction ID
            is_read: True if this is a read transaction, False for write/read response
            
        Returns:
            List of data values, or empty list if transaction not found
        """
        if is_read:
            # For read transactions, look in the read response data
            data_sequence = self.read_data_sequence
            id_sequence = data_sequence.id_sequence
        else:
            # For write transactions, just return the data
            # We don't have easy mapping to transaction IDs,
            # so we'll return all data for now
            return self.write_data_sequence.data_sequence
        
        # For read responses, find by ID
        data_values = []
        for i, tx_id in enumerate(id_sequence):
            if tx_id == id_value:
                data_values.append(data_sequence.data_sequence[i])
                
        return data_values

    # ========================================================================
    # Factory Methods
    # ========================================================================
    
    @classmethod
    def create_simple_writes(cls, 
                           addrs: List[int], 
                           data_values: List[List[int]],
                           id_values: Optional[List[int]] = None,
                           data_width: int = 32) -> 'AXI4TransactionSequence':
        """
        Create a sequence of simple write transactions.
        
        Args:
            addrs: List of addresses
            data_values: List of data bursts (each item is a list of values for one burst)
            id_values: List of transaction IDs to use (auto-generated if None)
            data_width: Width of data in bits
            
        Returns:
            Configured AXI4TransactionSequence
        """
        sequence = cls(name="simple_writes", data_width=data_width)
        
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
                          data_width: int = 32) -> 'AXI4TransactionSequence':
        """
        Create a sequence of simple read transactions.
        
        Args:
            addrs: List of addresses
            burst_lens: List of burst lengths
            id_values: List of transaction IDs to use (auto-generated if None)
            data_width: Width of data in bits
            
        Returns:
            Configured AXI4TransactionSequence
        """
        sequence = cls(name="simple_reads", data_width=data_width)
        
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
                                 data_width: int = 32) -> 'AXI4TransactionSequence':
        """
        Create a sequence of write transactions with incrementing addresses and data.
        
        Args:
            start_addr: Starting address
            count: Number of transactions
            data_width: Width of data in bits
            
        Returns:
            Configured AXI4TransactionSequence
        """
        sequence = cls(name="incrementing_writes", data_width=data_width)
        
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
                              data_width: int = 32) -> 'AXI4TransactionSequence':
        """
        Create a sequence where each address is first written, then read.
        
        Args:
            addrs: List of addresses
            data_values: List of data bursts for writes
            data_width: Width of data in bits
            
        Returns:
            Configured AXI4TransactionSequence with read-after-write dependencies
        """
        sequence = cls(name="read_after_write", data_width=data_width)
        
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
            sequence.add_read_transaction(
                addr=addr,
                burst_len=burst_len,
                dependencies=[write_id]  # Make read depend on write
            )
            
        return sequence

    @classmethod
    def create_burst_variations(cls, 
                              start_addr: int = 0, 
                              data_width: int = 32) -> 'AXI4TransactionSequence':
        """
        Create a sequence with various burst types and lengths.
        
        Args:
            start_addr: Starting address
            data_width: Width of data in bits
            
        Returns:
            Configured AXI4TransactionSequence
        """
        sequence = cls(name="burst_variations", data_width=data_width)
        
        # Test parameters
        burst_types = [1, 2, 0]  # INCR, WRAP, FIXED
        burst_lengths = [0, 1, 3, 7, 15]  # 1, 2, 4, 8, 16 transfers
        burst_sizes = [2, 3]  # 4, 8 bytes
        
        # Byte increment for address spacing
        addr_increment = 64
        
        # Create transactions
        addr = start_addr
        for burst_type in burst_types:
            for burst_size in burst_sizes:
                for burst_len in burst_lengths:
                    # Skip invalid combinations (WRAP bursts with lengths not 2^n)
                    if burst_type == 2 and (burst_len + 1) & (burst_len) != 0:
                        continue
                    
                    # Create data values for the burst
                    data_values = [0xA0000000 + i for i in range(burst_len + 1)]
                    
                    # Add write transaction
                    sequence.add_write_transaction(
                        addr=addr,
                        data_values=data_values,
                        burst_size=burst_size,
                        burst_type=burst_type
                    )
                    
                    # Add read transaction for the same burst
                    sequence.add_read_transaction(
                        addr=addr,
                        burst_len=burst_len,
                        burst_size=burst_size,
                        burst_type=burst_type
                    )
                    
                    # Increment address
                    addr += addr_increment
            
        return sequence

    @classmethod
    def create_exclusive_access_test(cls, 
                                   addrs: List[int], 
                                   data_values: List[int],
                                   data_width: int = 32) -> 'AXI4TransactionSequence':
        """
        Create a sequence testing exclusive access.
        
        Args:
            addrs: List of addresses to test
            data_values: Data values to write
            data_width: Width of data in bits
            
        Returns:
            Configured AXI4TransactionSequence with exclusive access patterns
        """
        sequence = cls(name="exclusive_access", data_width=data_width)
        
        # For each address, perform exclusive read followed by exclusive write
        for i, addr in enumerate(addrs):
            # Get data for this transaction
            data = data_values[i % len(data_values)]
            
            # Add exclusive read
            read_id = sequence.add_read_transaction(
                addr=addr,
                burst_len=0,  # Single transfer
                lock=1  # Exclusive access
            )
            
            # Add exclusive write dependent on the read
            sequence.add_write_transaction(
                addr=addr,
                data_values=[data],
                lock=1,  # Exclusive access
                dependencies=[read_id]  # Write depends on read
            )
            
        return sequence

    @classmethod
    def create_protocol_stress_test(cls, data_width: int = 32) -> 'AXI4TransactionSequence':
        """
        Create a comprehensive test of AXI4 protocol features.
        
        Args:
            data_width: Width of data in bits
            
        Returns:
            Configured AXI4TransactionSequence with protocol stress patterns
        """
        sequence = cls(name="protocol_stress", data_width=data_width)
        
        # Base address for different test sections
        addr = 0x10000000
        
        # 1. Basic single beat transactions
        for i in range(5):
            # Write
            sequence.add_write_transaction(
                addr=addr + (i*4),
                data_values=[i]
            )
            
            # Read
            sequence.add_read_transaction(
                addr=addr + (i*4),
                burst_len=0
            )
        
        addr += 0x1000
        
        # 2. INCR burst transactions
        for length in [1, 3, 7, 15]:
            data_values = [0xA0000000 + i for i in range(length + 1)]
            
            # Write
            write_id = sequence.add_write_transaction(
                addr=addr,
                data_values=data_values,
                burst_type=1  # INCR
            )
            
            # Read with dependency
            sequence.add_read_transaction(
                addr=addr,
                burst_len=length,
                burst_type=1,  # INCR
                dependencies=[write_id]
            )
            
            addr += 0x100
        
        # 3. WRAP burst transactions
        for length in [1, 3, 7, 15]:
            data_values = [0xB0000000 + i for i in range(length + 1)]
            
            # Write
            write_id = sequence.add_write_transaction(
                addr=addr,
                data_values=data_values,
                burst_type=2  # WRAP
            )
            
            # Read with dependency
            sequence.add_read_transaction(
                addr=addr,
                burst_len=length,
                burst_type=2,  # WRAP
                dependencies=[write_id]
            )
            
            addr += 0x100
        
        # 4. FIXED burst transactions
        for length in [1, 3]:
            data_values = [0xC0000000 + i for i in range(length + 1)]
            
            # Write
            write_id = sequence.add_write_transaction(
                addr=addr,
                data_values=data_values,
                burst_type=0  # FIXED
            )
            
            # Read with dependency
            sequence.add_read_transaction(
                addr=addr,
                burst_len=length,
                burst_type=0,  # FIXED
                dependencies=[write_id]
            )
            
            addr += 0x100
        
        # 5. Exclusive access
        write_id = sequence.add_write_transaction(
            addr=addr,
            data_values=[0xD0000000],
            burst_type=1  # INCR
        )
        
        # Exclusive read after write
        read_id = sequence.add_read_transaction(
            addr=addr,
            burst_len=0,
            lock=1,  # Exclusive
            dependencies=[write_id]
        )
        
        # Exclusive write after exclusive read
        sequence.add_write_transaction(
            addr=addr,
            data_values=[0xD0000001],
            lock=1,  # Exclusive
            dependencies=[read_id]
        )
        
        addr += 0x100
        
        # 6. Different burst sizes
        for size in [0, 1, 2, 3]:  # 1, 2, 4, 8 bytes
            byte_count = 1 << size
            aligned_addr = (addr // byte_count) * byte_count
            
            # Create data
            data_values = [0xE0000000 + i for i in range(4)]
            
            # Write
            write_id = sequence.add_write_transaction(
                addr=aligned_addr,
                data_values=data_values,
                burst_size=size,
                burst_type=1  # INCR
            )
            
            # Read with dependency
            sequence.add_read_transaction(
                addr=aligned_addr,
                burst_len=3,
                burst_size=size,
                burst_type=1,  # INCR
                dependencies=[write_id]
            )
            
            addr += 0x100
        
        # 7. Different protection attributes
        for prot in range(8):
            # Write
            write_id = sequence.add_write_transaction(
                addr=addr + (prot * 4),
                data_values=[0xF0000000 + prot],
                prot=prot
            )
            
            # Read with dependency
            sequence.add_read_transaction(
                addr=addr + (prot * 4),
                burst_len=0,
                prot=prot,
                dependencies=[write_id]
            )
        
        # 8. Byte strobes (partial writes)
        addr += 0x100
        strobe_patterns = [0x1, 0x3, 0x7, 0xF, 0x5, 0xA]
        
        for i, strb in enumerate(strobe_patterns):
            # Partial write with specific strobe
            sequence.add_write_transaction(
                addr=addr + (i * 4),
                data_values=[0xF1000000 + i],
                strb_values=[strb]
            )
        
        return sequence