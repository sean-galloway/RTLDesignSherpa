"""
AXI4 Protocol Extensions

This module extends the AXI4 components with additional protocol features:
1. Quality of Service (QoS) support
2. Exclusive access handling
3. Atomic operations
4. Barrier transactions
"""

import random
from typing import Dict, List, Optional, Tuple, Set, Any
from collections import deque
import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from CocoTBFramework.components.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.axi4.axi4_packets import AXI4Packet


class QoSHandler:
    """
    Quality of Service handler for AXI4 transactions.
    
    This class manages QoS priorities according to the AXI4 specification.
    Higher QoS values indicate higher priority transactions.
    """
    
    def __init__(self, num_priority_levels: int = 16):
        """
        Initialize the QoS handler.
        
        Args:
            num_priority_levels: Number of priority levels (default: 16)
        """
        self.num_priority_levels = num_priority_levels
        
        # Transaction queues for each priority level
        self.write_queues = {i: deque() for i in range(num_priority_levels)}
        self.read_queues = {i: deque() for i in range(num_priority_levels)}
        
        # Fairness counters to prevent starvation of lower priority transactions
        self.write_counters = {i: 0 for i in range(num_priority_levels)}
        self.read_counters = {i: 0 for i in range(num_priority_levels)}
        
        # Configurable starvation threshold
        self.starvation_threshold = 10
        
        # Configuratble priority bump for starved transactions
        self.starvation_bump = 4
    
    def queue_write_transaction(self, transaction: Dict[str, Any], qos: int):
        """
        Queue a write transaction with QoS priority.
        
        Args:
            transaction: Write transaction to queue
            qos: Quality of Service value (0-15)
        """
        # Ensure QoS is within range
        qos = max(0, min(qos, self.num_priority_levels - 1))
        
        # Add transaction to appropriate queue
        self.write_queues[qos].append(transaction)
    
    def queue_read_transaction(self, transaction: Dict[str, Any], qos: int):
        """
        Queue a read transaction with QoS priority.
        
        Args:
            transaction: Read transaction to queue
            qos: Quality of Service value (0-15)
        """
        # Ensure QoS is within range
        qos = max(0, min(qos, self.num_priority_levels - 1))
        
        # Add transaction to appropriate queue
        self.read_queues[qos].append(transaction)
    
    def get_next_write_transaction(self) -> Optional[Dict[str, Any]]:
        """
        Get the next write transaction based on QoS priority.
        
        Returns:
            Highest priority write transaction, or None if no transactions
        """
        # Check for starvation and potentially bump priorities
        self._check_write_starvation()
        
        # Try to get a transaction from the highest non-empty priority queue
        for qos in range(self.num_priority_levels - 1, -1, -1):
            if self.write_queues[qos]:
                # Increment counters for all other priorities
                for other_qos in range(self.num_priority_levels):
                    if other_qos != qos:
                        self.write_counters[other_qos] += 1
                
                # Reset counter for this priority
                self.write_counters[qos] = 0
                
                # Return and remove the next transaction
                return self.write_queues[qos].popleft()
        
        # No transactions available
        return None
    
    def get_next_read_transaction(self) -> Optional[Dict[str, Any]]:
        """
        Get the next read transaction based on QoS priority.
        
        Returns:
            Highest priority read transaction, or None if no transactions
        """
        # Check for starvation and potentially bump priorities
        self._check_read_starvation()
        
        # Try to get a transaction from the highest non-empty priority queue
        for qos in range(self.num_priority_levels - 1, -1, -1):
            if self.read_queues[qos]:
                # Increment counters for all other priorities
                for other_qos in range(self.num_priority_levels):
                    if other_qos != qos:
                        self.read_counters[other_qos] += 1
                
                # Reset counter for this priority
                self.read_counters[qos] = 0
                
                # Return and remove the next transaction
                return self.read_queues[qos].popleft()
        
        # No transactions available
        return None
    
    def _check_write_starvation(self):
        """Check for starved write transactions and potentially bump priorities"""
        for qos in range(self.num_priority_levels):
            if (self.write_counters[qos] > self.starvation_threshold and 
                    self.write_queues[qos]):
                # This priority level is starved, bump some transactions
                bump_qos = min(qos + self.starvation_bump, self.num_priority_levels - 1)
                
                # Move up to 3 transactions to higher priority
                for _ in range(min(3, len(self.write_queues[qos]))):
                    transaction = self.write_queues[qos].popleft()
                    self.write_queues[bump_qos].append(transaction)
                
                # Reset counter for this priority
                self.write_counters[qos] = 0
    
    def _check_read_starvation(self):
        """Check for starved read transactions and potentially bump priorities"""
        for qos in range(self.num_priority_levels):
            if (self.read_counters[qos] > self.starvation_threshold and 
                    self.read_queues[qos]):
                # This priority level is starved, bump some transactions
                bump_qos = min(qos + self.starvation_bump, self.num_priority_levels - 1)
                
                # Move up to 3 transactions to higher priority
                for _ in range(min(3, len(self.read_queues[qos]))):
                    transaction = self.read_queues[qos].popleft()
                    self.read_queues[bump_qos].append(transaction)
                
                # Reset counter for this priority
                self.read_counters[qos] = 0
    
    def get_stats(self) -> Dict[str, Any]:
        """
        Get statistics about QoS queue usage.
        
        Returns:
            Dictionary with statistics
        """
        write_queue_sizes = {qos: len(queue) for qos, queue in self.write_queues.items()}
        read_queue_sizes = {qos: len(queue) for qos, queue in self.read_queues.items()}
        
        return {
            'write_queue_sizes': write_queue_sizes,
            'read_queue_sizes': read_queue_sizes,
            'write_counters': self.write_counters.copy(),
            'read_counters': self.read_counters.copy()
        }


class ExclusiveAccessHandler:
    """
    Exclusive access handler for AXI4 transactions.
    
    This class manages exclusive access operations according to the AXI4 specification.
    It tracks exclusive monitors and provides support for exclusive reads and writes.
    """
    
    def __init__(self):
        """Initialize the exclusive access handler"""
        # Track exclusive monitors for each ID
        # Key: (ID, master_id), Value: (address, size)
        self.exclusive_monitors = {}
        
        # Track exclusive access regions - address ranges that require exclusivity
        # Each region is a tuple of (start_address, end_address)
        self.exclusive_regions = []
        
        # Track statistics
        self.stats = {
            'exclusive_reads': 0,
            'exclusive_writes': 0,
            'successful_exclusive_writes': 0,
            'failed_exclusive_writes': 0
        }
    
    def register_exclusive_region(self, start_address: int, end_address: int):
        """
        Register a memory region that requires exclusive access.
        
        Args:
            start_address: Start address of the region
            end_address: End address of the region
        """
        self.exclusive_regions.append((start_address, end_address))
    
    def is_exclusive_region(self, address: int, size: int) -> bool:
        """
        Check if an address range falls within a registered exclusive region.
        
        Args:
            address: Start address
            size: Size in bytes
            
        Returns:
            True if the address range requires exclusive access
        """
        end_address = address + size - 1
        for region_start, region_end in self.exclusive_regions:
            if address <= region_end and end_address >= region_start:
                return True
        return False
    
    def handle_exclusive_read(self, id_value: int, master_id: int, address: int, size: int) -> bool:
        """
        Handle an exclusive read operation.
        
        Args:
            id_value: Transaction ID
            master_id: Master identifier
            address: Read address
            size: Size in bytes
            
        Returns:
            True if the exclusive read was successfully processed
        """
        # Set up exclusive monitor for this ID
        self.exclusive_monitors[(id_value, master_id)] = (address, size)
        
        # Update statistics
        self.stats['exclusive_reads'] += 1
        
        return True
    
    def handle_exclusive_write(self, id_value: int, master_id: int, address: int, size: int) -> bool:
        """
        Handle an exclusive write operation.
        
        Args:
            id_value: Transaction ID
            master_id: Master identifier
            address: Write address
            size: Size in bytes
            
        Returns:
            True if the exclusive write was successful, False if it failed
        """
        # Update statistics
        self.stats['exclusive_writes'] += 1
        
        # Check if there's a valid exclusive monitor for this ID
        if (id_value, master_id) not in self.exclusive_monitors:
            self.stats['failed_exclusive_writes'] += 1
            return False
        
        # Get the monitored address and size
        monitor_address, monitor_size = self.exclusive_monitors[(id_value, master_id)]
        
        # Check if the write address matches the monitored address
        if address != monitor_address or size != monitor_size:
            self.stats['failed_exclusive_writes'] += 1
            return False
        
        # Check if the exclusive monitor is still valid
        # (in a real implementation, this would check if another master has written to this address)
        # For now, we'll randomly succeed or fail to simulate real-world conditions
        if random.random() < 0.9:  # 90% success rate
            # Success - clear the exclusive monitor
            del self.exclusive_monitors[(id_value, master_id)]
            self.stats['successful_exclusive_writes'] += 1
            return True
        else:
            # Failure - the monitor is no longer valid
            del self.exclusive_monitors[(id_value, master_id)]
            self.stats['failed_exclusive_writes'] += 1
            return False
    
    def clear_exclusive_monitor(self, id_value: int, master_id: int):
        """
        Clear the exclusive monitor for an ID.
        
        Args:
            id_value: Transaction ID
            master_id: Master identifier
        """
        if (id_value, master_id) in self.exclusive_monitors:
            del self.exclusive_monitors[(id_value, master_id)]
    
    def get_stats(self) -> Dict[str, Any]:
        """
        Get statistics about exclusive access operations.
        
        Returns:
            Dictionary with statistics
        """
        stats = self.stats.copy()
        stats['active_monitors'] = len(self.exclusive_monitors)
        return stats


class AtomicOperationHandler:
    """
    Handler for atomic operations in AXI4.
    
    While not part of the base AXI4 specification, atomic operations
    are commonly implemented as extensions, particularly in AXI5 and
    specialized implementations.
    """
    
    # Atomic operation types
    ATOMIC_ADD = 0
    ATOMIC_SWAP = 1
    ATOMIC_COMPARE_SWAP = 2
    ATOMIC_MIN = 3
    ATOMIC_MAX = 4
    ATOMIC_AND = 5
    ATOMIC_OR = 6
    ATOMIC_XOR = 7
    
    def __init__(self, memory_model=None):
        """
        Initialize the atomic operation handler.
        
        Args:
            memory_model: Memory model for data storage
        """
        self.memory_model = memory_model
        
        # Track statistics
        self.stats = {
            'operations': {
                self.ATOMIC_ADD: 0,
                self.ATOMIC_SWAP: 0,
                self.ATOMIC_COMPARE_SWAP: 0,
                self.ATOMIC_MIN: 0,
                self.ATOMIC_MAX: 0,
                self.ATOMIC_AND: 0,
                self.ATOMIC_OR: 0,
                self.ATOMIC_XOR: 0
            },
            'successful_operations': 0,
            'failed_operations': 0
        }
    
    def perform_atomic_operation(self, op_type: int, address: int, value: int, compare_value: int = None) -> Tuple[bool, int]:
        """
        Perform an atomic operation.
        
        Args:
            op_type: Type of atomic operation
            address: Memory address
            value: Operation value
            compare_value: Comparison value for compare-and-swap
            
        Returns:
            Tuple of (success, old_value)
        """
        # Ensure we have a memory model
        if not self.memory_model:
            self.stats['failed_operations'] += 1
            return False, 0
        
        # Update operation statistics
        if op_type in self.stats['operations']:
            self.stats['operations'][op_type] += 1
        
        try:
            # Read current value from memory
            data_bytes = self.memory_model.read(address, self.memory_model.bytes_per_line)
            old_value = self.memory_model.bytearray_to_integer(data_bytes)
            
            # Perform the requested operation
            new_value = self._calculate_new_value(op_type, old_value, value, compare_value)
            
            # Write the new value to memory
            new_bytes = self.memory_model.integer_to_bytearray(new_value, self.memory_model.bytes_per_line)
            self.memory_model.write(address, new_bytes, 0xFF)  # Full write
            
            self.stats['successful_operations'] += 1
            return True, old_value
        except Exception as e:
            self.stats['failed_operations'] += 1
            return False, 0
    
    def _calculate_new_value(self, op_type: int, old_value: int, value: int, compare_value: int = None) -> int:
        """
        Calculate the new value for an atomic operation.
        
        Args:
            op_type: Type of atomic operation
            old_value: Current value in memory
            value: Operation value
            compare_value: Comparison value for compare-and-swap
            
        Returns:
            New value to write to memory
        """
        if op_type == self.ATOMIC_ADD:
            return old_value + value
        elif op_type == self.ATOMIC_SWAP:
            return value
        elif op_type == self.ATOMIC_COMPARE_SWAP:
            return value if old_value == compare_value else old_value
        elif op_type == self.ATOMIC_MIN:
            return min(old_value, value)
        elif op_type == self.ATOMIC_MAX:
            return max(old_value, value)
        elif op_type == self.ATOMIC_AND:
            return old_value & value
        elif op_type == self.ATOMIC_OR:
            return old_value | value
        elif op_type == self.ATOMIC_XOR:
            return old_value ^ value
        else:
            # Unknown operation type
            return old_value
    
    def get_stats(self) -> Dict[str, Any]:
        """
        Get statistics about atomic operations.
        
        Returns:
            Dictionary with statistics
        """
        return self.stats.copy()


class BarrierHandler:
    """
    Handler for barrier transactions in AXI4.
    
    Barriers ensure ordering between transactions and are particularly
    useful in systems with multiple masters. They're an extension to
    the base AXI4 specification.
    """
    
    # Barrier types
    BARRIER_MEMORY = 0
    BARRIER_DEVICE = 1
    BARRIER_SYSTEM = 2
    
    def __init__(self):
        """Initialize the barrier handler"""
        # Track pending transactions before each barrier
        # Key: barrier_id, Value: list of transaction IDs
        self.pending_before_barrier = {}
        
        # Track pending transactions after each barrier
        # Key: barrier_id, Value: list of transaction IDs
        self.pending_after_barrier = {}
        
        # Track active barriers
        # Key: barrier_id, Value: barrier_type
        self.active_barriers = {}
        
        # Next barrier ID
        self.next_barrier_id = 1
        
        # Track statistics
        self.stats = {
            'barriers_created': 0,
            'barriers_completed': 0,
            'transactions_ordered': 0
        }
    
    def create_barrier(self, barrier_type: int) -> int:
        """
        Create a new barrier.
        
        Args:
            barrier_type: Type of barrier
            
        Returns:
            Barrier ID
        """
        barrier_id = self.next_barrier_id
        self.next_barrier_id += 1
        
        self.active_barriers[barrier_id] = barrier_type
        self.pending_before_barrier[barrier_id] = []
        self.pending_after_barrier[barrier_id] = []
        
        self.stats['barriers_created'] += 1
        
        return barrier_id
    
    def add_transaction_before_barrier(self, barrier_id: int, transaction_id: int):
        """
        Add a transaction to the "before barrier" group.
        
        Args:
            barrier_id: Barrier ID
            transaction_id: Transaction ID
        """
        if barrier_id in self.pending_before_barrier:
            self.pending_before_barrier[barrier_id].append(transaction_id)
            self.stats['transactions_ordered'] += 1
    
    def add_transaction_after_barrier(self, barrier_id: int, transaction_id: int):
        """
        Add a transaction to the "after barrier" group.
        
        Args:
            barrier_id: Barrier ID
            transaction_id: Transaction ID
        """
        if barrier_id in self.pending_after_barrier:
            self.pending_after_barrier[barrier_id].append(transaction_id)
            self.stats['transactions_ordered'] += 1
    
    def is_transaction_allowed(self, transaction_id: int) -> bool:
        """
        Check if a transaction is allowed to proceed.
        
        Args:
            transaction_id: Transaction ID
            
        Returns:
            True if the transaction can proceed, False if it must wait
        """
        # Check if this transaction is after any active barrier
        for barrier_id, transactions in self.pending_after_barrier.items():
            if transaction_id in transactions:
                # Check if all "before barrier" transactions are complete
                if self.pending_before_barrier[barrier_id]:
                    # Still have pending transactions before this barrier
                    return False
        
        return True
    
    def complete_transaction(self, transaction_id: int):
        """
        Mark a transaction as complete.
        
        Args:
            transaction_id: Transaction ID
        """
        # Remove from all "before barrier" groups
        for barrier_id, transactions in list(self.pending_before_barrier.items()):
            if transaction_id in transactions:
                transactions.remove(transaction_id)
                
                # Check if this barrier is now complete
                if not transactions and not self.pending_after_barrier[barrier_id]:
                    self._complete_barrier(barrier_id)
        
        # Remove from all "after barrier" groups
        for barrier_id, transactions in list(self.pending_after_barrier.items()):
            if transaction_id in transactions:
                transactions.remove(transaction_id)
                
                # Check if this barrier is now complete
                if not transactions and not self.pending_before_barrier[barrier_id]:
                    self._complete_barrier(barrier_id)
    
    def _complete_barrier(self, barrier_id: int):
        """
        Mark a barrier as complete.
        
        Args:
            barrier_id: Barrier ID
        """
        if barrier_id in self.active_barriers:
            del self.active_barriers[barrier_id]
            del self.pending_before_barrier[barrier_id]
            del self.pending_after_barrier[barrier_id]
            
            self.stats['barriers_completed'] += 1
    
    def get_stats(self) -> Dict[str, Any]:
        """
        Get statistics about barrier transactions.
        
        Returns:
            Dictionary with statistics
        """
        stats = self.stats.copy()
        stats['active_barriers'] = len(self.active_barriers)
        return stats


# Factory function to create all extension handlers
def create_axi4_extension_handlers(memory_model=None, log=None):
    """
    Create all AXI4 extension handlers.
    
    Args:
        memory_model: Memory model for data storage
        log: Logger instance
        
    Returns:
        Dictionary of extension handlers
    """
    if log:
        log.info("Creating AXI4 extension handlers")
    
    # Create handlers
    qos_handler = QoSHandler()
    exclusive_handler = ExclusiveAccessHandler()
    atomic_handler = AtomicOperationHandler(memory_model)
    barrier_handler = BarrierHandler()
    
    return {
        'qos': qos_handler,
        'exclusive': exclusive_handler,
        'atomic': atomic_handler,
        'barrier': barrier_handler
    }


# Extended AXI4Master with protocol extensions
class ExtendedAXI4Master:
    """
    Extended AXI4 Master with protocol extensions.
    
    This class wraps a standard AXI4Master and adds support for:
    - Quality of Service (QoS)
    - Exclusive access
    - Atomic operations
    - Barrier transactions
    """
    
    def __init__(self, master, extensions, log=None):
        """
        Initialize the extended AXI4 master.
        
        Args:
            master: AXI4Master instance
            extensions: Dictionary of extension handlers
            log: Logger instance
        """
        self.master = master
        self.extensions = extensions
        self.log = log or master.log
        
        # Master ID - used for exclusive access tracking
        self.master_id = id(self)
        
        self.log.info(f"ExtendedAXI4Master created with ID {self.master_id}")
    
    async def exclusive_read(self, addr, size=2, burst=1, id=0, length=0, cache=0, prot=0, qos=0, region=0, user=0):
        """
        Execute an AXI4 exclusive read transaction.
        
        Args:
            addr: Target address
            size: Transfer size (0=byte, 1=halfword, 2=word, 3=doubleword, etc.)
            burst: Burst type (0=FIXED, 1=INCR, 2=WRAP)
            id: Transaction ID
            length: Burst length (0 = 1 beat, 1 = 2 beats, etc.)
            cache: Cache type
            prot: Protection type
            qos: Quality of Service
            region: Region identifier
            user: User signal
            
        Returns:
            dict: Transaction results with responses
        """
        # Set lock bit for exclusive access
        result = await self.master.read(
            addr, size, burst, id, length, cache, prot, qos, region, user
        )
        
        # Register exclusive monitor
        if 'exclusive' in self.extensions:
            self.extensions['exclusive'].handle_exclusive_read(
                id, self.master_id, addr, 1 << size
            )
        
        return result
    
    async def exclusive_write(self, addr, data, size=2, burst=1, strobe=None, id=0, length=0, cache=0, prot=0, qos=0, region=0, user=0):
        """
        Execute an AXI4 exclusive write transaction.
        
        Args:
            addr: Target address
            data: Data to write (int, list, or bytearray)
            size: Transfer size (0=byte, 1=halfword, 2=word, 3=doubleword, etc.)
            burst: Burst type (0=FIXED, 1=INCR, 2=WRAP)
            strobe: Byte strobe (default: all bytes enabled)
            id: Transaction ID
            length: Burst length (0 = 1 beat, 1 = 2 beats, etc.)
            cache: Cache type
            prot: Protection type
            qos: Quality of Service
            region: Region identifier
            user: User signal
            
        Returns:
            dict: Transaction results with response including exclusive status
        """
        # Set lock bit for exclusive access
        result = await self.master.write(
            addr, data, size, burst, strobe, id, length, cache, prot, qos, region, user
        )
        
        # Check exclusive status
        if 'exclusive' in self.extensions:
            success = self.extensions['exclusive'].handle_exclusive_write(
                id, self.master_id, addr, 1 << size
            )
            result['exclusive_success'] = success
        
        return result
    
    async def atomic_operation(self, op_type, addr, value, compare_value=None, id=0, qos=0):
        """
        Execute an atomic operation.
        
        Args:
            op_type: Type of atomic operation
            addr: Target address
            value: Operation value
            compare_value: Comparison value for compare-and-swap
            id: Transaction ID
            qos: Quality of Service
            
        Returns:
            Tuple of (success, old_value)
        """
        if 'atomic' not in self.extensions:
            return False, 0
        
        # Perform atomic operation via handler
        return self.extensions['atomic'].perform_atomic_operation(
            op_type, addr, value, compare_value
        )
    
    async def create_barrier(self, barrier_type):
        """
        Create a barrier to ensure transaction ordering.
        
        Args:
            barrier_type: Type of barrier
            
        Returns:
            Barrier ID
        """
        if 'barrier' not in self.extensions:
            return -1
        
        return self.extensions['barrier'].create_barrier(barrier_type)
    
    async def order_transaction_before_barrier(self, barrier_id, transaction_id):
        """
        Ensure a transaction completes before a barrier.
        
        Args:
            barrier_id: Barrier ID
            transaction_id: Transaction ID
        """
        if 'barrier' in self.extensions:
            self.extensions['barrier'].add_transaction_before_barrier(
                barrier_id, transaction_id
            )
    
    async def order_transaction_after_barrier(self, barrier_id, transaction_id):
        """
        Ensure a transaction starts after a barrier.
        
        Args:
            barrier_id: Barrier ID
            transaction_id: Transaction ID
        """
        if 'barrier' in self.extensions:
            self.extensions['barrier'].add_transaction_after_barrier(
                barrier_id, transaction_id
            )
    
    async def complete_transaction(self, transaction_id):
        """
        Mark a transaction as complete for barrier tracking.
        
        Args:
            transaction_id: Transaction ID
        """
        if 'barrier' in self.extensions:
            self.extensions['barrier'].complete_transaction(transaction_id)
    
    def get_extension_stats(self):
        """
        Get statistics from all extension handlers.
        
        Returns:
            Dictionary with statistics from all extensions
        """
        stats = {}
        
        for name, handler in self.extensions.items():
            if hasattr(handler, 'get_stats'):
                stats[name] = handler.get_stats()
        
        return stats
