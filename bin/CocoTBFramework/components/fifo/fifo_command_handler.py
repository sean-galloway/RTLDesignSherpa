"""
FIFO Command Handler for Transaction Dependency Management

This module provides dependency orchestration between FIFO Master and Slave components,
focusing on transaction dependencies and sequence processing while leveraging
existing component statistics and infrastructure.
"""

import cocotb
from collections import deque
from cocotb.triggers import RisingEdge
from cocotb.utils import get_sim_time


class FIFOCommandHandler:
    """
    Command handler for orchestrating FIFO transaction dependencies.

    This class focuses on dependency resolution and sequence processing,
    allowing transactions to depend on completion of previous transactions.
    Statistics and state management are handled by the master/slave components.
    """

    def __init__(self, master, slave, log=None):
        """
        Initialize the FIFO command handler.

        Args:
            master: FIFOMaster instance
            slave: FIFOSlave instance
            log: Logger instance
        """
        self.master = master
        self.slave = slave
        self.log = log or getattr(master, 'log', None)

        # Transaction dependency tracking
        self.pending_dependencies = {}  # txn_id -> dependency_info
        self.completed_transactions = set()  # Set of completed transaction IDs
        self.transaction_ordering = []  # List of transaction IDs in order

        # Callback management
        self.callbacks = []

        # Processing task
        self.processor_task = None
        self.running = False

    async def start(self):
        """
        Start the command handler processing task.

        Returns:
            Self for method chaining
        """
        if not self.running:
            self.running = True
            # Set up callback for slave responses
            self.slave.add_callback(self._handle_slave_response)
            self.processor_task = cocotb.start_soon(self._process_dependencies())
            self.log.info("FIFO command handler started")
        return self

    async def stop(self):
        """
        Stop the command handler processing task.

        Returns:
            Self for method chaining
        """
        self.running = False
        if self.processor_task:
            self.processor_task.cancel()
            self.processor_task = None
        # Remove our callback from slave
        if self._handle_slave_response in self.slave.callbacks:
            self.slave.callbacks.remove(self._handle_slave_response)
        self.log.info("FIFO command handler stopped")
        return self

    def add_callback(self, callback):
        """
        Add a callback function to be called when transactions complete.

        Args:
            callback: Function to call with completed transaction

        Returns:
            Self for method chaining
        """
        if callback not in self.callbacks:
            self.callbacks.append(callback)
        return self

    def remove_callback(self, callback):
        """
        Remove a previously added callback function.

        Args:
            callback: Function to remove

        Returns:
            Self for method chaining
        """
        if callback in self.callbacks:
            self.callbacks.remove(callback)
        return self

    async def send_with_dependency(self, packet, depends_on_id=None, dependency_type="after"):
        """
        Send a packet with dependency tracking.

        Args:
            packet: Packet to send
            depends_on_id: Transaction ID this depends on (None for no dependency)
            dependency_type: Type of dependency ("after", "immediate", "conditional")

        Returns:
            Transaction ID for this packet
        """
        # Generate unique transaction ID
        txn_id = id(packet)
        packet.transaction_id = txn_id

        # Store dependency information
        if depends_on_id is not None:
            self.pending_dependencies[txn_id] = {
                'depends_on': depends_on_id,
                'dependency_type': dependency_type,
                'packet': packet,
                'ready': False
            }
        else:
            # No dependency, can send immediately
            await self.master.send(packet)

        # Track ordering
        self.transaction_ordering.append(txn_id)
        return txn_id

    async def _process_dependencies(self):
        """
        Main processing loop for handling transaction dependencies.
        """
        while self.running:
            # Check for dependencies that are now ready
            ready_transactions = []
            for txn_id, dep_info in self.pending_dependencies.items():
                if not dep_info['ready'] and self._is_dependency_satisfied(dep_info):
                    dep_info['ready'] = True
                    ready_transactions.append(txn_id)

            # Send ready transactions
            for txn_id in ready_transactions:
                dep_info = self.pending_dependencies[txn_id]
                packet = dep_info['packet']
                await self.master.send(packet)
                # Keep in pending_dependencies until response received
                self.log.debug(f"Sent transaction {txn_id} after dependency satisfied")

            # Wait for next cycle
            await RisingEdge(self.master.clock)

    def _is_dependency_satisfied(self, dep_info):
        """
        Check if a transaction's dependencies are satisfied.

        Args:
            dep_info: Dependency information dictionary

        Returns:
            True if dependencies are satisfied, False otherwise
        """
        depends_on = dep_info['depends_on']
        dependency_type = dep_info['dependency_type']

        if dependency_type == "after":
            # Wait for dependent transaction to complete
            return depends_on in self.completed_transactions
        elif dependency_type == "immediate":
            # Send immediately after dependent transaction is sent (not completed)
            return True  # For now, treat as immediate
        elif dependency_type == "conditional":
            # Custom logic could be added here
            return depends_on in self.completed_transactions
        else:
            return True

    def _handle_slave_response(self, response):
        """
        Handle a response from the slave to track completion.

        Args:
            response: Response packet from slave
        """
        # Try to get transaction ID from response
        txn_id = getattr(response, 'transaction_id', None)
        
        if txn_id:
            # Mark as completed
            self.completed_transactions.add(txn_id)
            
            # Remove from pending dependencies if present
            if txn_id in self.pending_dependencies:
                del self.pending_dependencies[txn_id]
            
            self.log.debug(f"Transaction {txn_id} completed")
            
            # Trigger callbacks
            for callback in self.callbacks:
                try:
                    callback(response)
                except Exception as e:
                    self.log.error(f"Error in callback: {e}")

    async def process_sequence(self, sequence):
        """
        Process a FIFO sequence with dependency handling.

        Args:
            sequence: FIFOSequence to process

        Returns:
            Dictionary of responses by transaction index
        """
        # Generate packets from sequence
        packets = sequence.generate_packets()
        
        # Track sequence index to transaction ID mapping
        sequence_to_txn_id = {}
        response_map = {}

        # Process each packet with dependency awareness
        for sequence_index, packet in enumerate(packets):
            # Check for dependencies
            depends_on_index = getattr(packet, 'depends_on_index', None)
            dependency_type = getattr(packet, 'dependency_type', 'after')
            
            # Convert sequence index to transaction ID
            depends_on_id = None
            if depends_on_index is not None and depends_on_index in sequence_to_txn_id:
                depends_on_id = sequence_to_txn_id[depends_on_index]

            # Send with dependency
            txn_id = await self.send_with_dependency(packet, depends_on_id, dependency_type)
            sequence_to_txn_id[sequence_index] = txn_id

        # Wait for all transactions to complete
        expected_completions = set(sequence_to_txn_id.values())
        while not expected_completions.issubset(self.completed_transactions) and self.running:
            await RisingEdge(self.master.clock)

        # Collect responses (would need to be implemented based on actual response tracking)
        # This is a simplified version - real implementation would track responses properly
        for seq_idx, txn_id in sequence_to_txn_id.items():
            if txn_id in self.completed_transactions:
                response_map[seq_idx] = f"Completed transaction {txn_id}"

        return response_map

    def get_dependency_status(self):
        """
        Get current status of dependencies.

        Returns:
            Dictionary with dependency information
        """
        return {
            'pending_dependencies': len(self.pending_dependencies),
            'completed_transactions': len(self.completed_transactions),
            'total_transactions': len(self.transaction_ordering),
            'dependency_details': {
                txn_id: {
                    'depends_on': info['depends_on'],
                    'dependency_type': info['dependency_type'],
                    'ready': info['ready']
                }
                for txn_id, info in self.pending_dependencies.items()
            }
        }

    def clear_completed(self):
        """
        Clear completed transaction tracking to free memory.

        Returns:
            Self for method chaining
        """
        self.completed_transactions.clear()
        self.transaction_ordering.clear()
        return self

    def get_stats(self):
        """
        Get handler statistics by combining master and slave stats.

        Returns:
            Dictionary with comprehensive statistics
        """
        return {
            'dependency_status': self.get_dependency_status(),
            'master_stats': self.master.get_stats() if hasattr(self.master, 'get_stats') else {},
            'slave_stats': self.slave.get_stats() if hasattr(self.slave, 'get_stats') else {},
        }
