"""
GAXI Command Handler for Master-Slave Communication

This module provides a command handler to coordinate transactions between
GAXI Master and Slave components, handling packet routing, timing,
and response matching.
"""

import cocotb
from collections import deque
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time


class GAXICommandHandler:
    """
    Command handler for GAXI transactions between master and slave components.
    
    This class coordinates communication between GAXIMaster and GAXISlave
    components, handling packet routing, timing, and response matching.
    It supports transaction dependencies and provides monitoring
    capabilities for transaction flow.
    """
    
    def __init__(self, master, slave, memory_model=None, log=None):
        """
        Initialize the GAXI command handler.
        
        Args:
            master: GAXIMaster instance
            slave: GAXISlave instance
            memory_model: Optional memory model (if None, uses master's memory model)
            log: Logger instance
        """
        self.master = master
        self.slave = slave
        self.memory_model = memory_model or getattr(master, 'memory_model', None)
        self.log = log or getattr(master, 'log', None)
        
        # Transaction tracking
        self.pending_transactions = {}  # txn_id -> transaction info
        self.completed_transactions = {}  # txn_id -> transaction info
        self.transaction_ordering = []  # List of transaction IDs in order of receipt
        
        # Response tracking
        self.responses = {}  # txn_id -> response info
        
        # Statistics
        self.stats = {
            'total_transactions': 0,
            'completed_transactions': 0,
            'pending_transactions': 0,
            'avg_latency': 0,
            'min_latency': float('inf'),
            'max_latency': 0
        }
        
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
            self.processor_task = cocotb.start_soon(self._process_transactions())
            self.log.info("GAXI command handler started")
        return self
    
    async def stop(self):
        """
        Stop the command handler processing task.
        
        Returns:
            Self for method chaining
        """
        self.running = False
        if self.processor_task:
            await Timer(10, units='ns')
            self.processor_task = None
            self.log.info("GAXI command handler stopped")
        return self
    
    async def _process_transactions(self):
        """
        Main processing loop for transactions from master to slave.
        
        This monitors the master's sent queue and forwards transactions to the slave,
        then tracks responses through callbacks.
        """
        # Set up callbacks for slave responses
        self.slave.add_callback(self._handle_slave_response)
        
        # Main processing loop
        while self.running:
            # Check for new transactions from master to forward to slave
            await self._forward_transactions()
            
            # Update statistics
            self._update_statistics()
            
            # Wait for next cycle
            await RisingEdge(self.master.clock)
    
    async def _forward_transactions(self):
        """Forward transactions from master to slave."""
        # Check if master has sent transactions to forward
        if hasattr(self.master, 'sent_queue') and self.master.sent_queue:
            # Take the next transaction from the master's queue
            transaction = self.master.sent_queue.popleft()
            
            # Generate a unique ID for tracking this transaction
            txn_id = id(transaction)
            
            # Store in pending transactions
            self.pending_transactions[txn_id] = {
                'transaction': transaction,
                'start_time': get_sim_time('ns'),
                'completed': False,
                'depends_on': getattr(transaction, 'depends_on_index', None),
                'dependency_type': getattr(transaction, 'dependency_type', None)
            }
            
            # Add to ordering list
            self.transaction_ordering.append(txn_id)
            
            # Update statistics
            self.stats['total_transactions'] += 1
            self.stats['pending_transactions'] += 1
            
            # Forward to slave if dependency is satisfied or no dependency
            if self._is_dependency_satisfied(txn_id):
                await self._send_to_slave(txn_id)
            else:
                self.log.debug(f"Transaction {txn_id} waiting for dependency to complete")
    
    def _is_dependency_satisfied(self, txn_id):
        """
        Check if a transaction's dependencies are satisfied.
        
        Args:
            txn_id: Transaction ID to check
            
        Returns:
            True if dependencies are satisfied (or no dependencies), False otherwise
        """
        transaction_info = self.pending_transactions.get(txn_id)
        if not transaction_info:
            return False
            
        depends_on = transaction_info.get('depends_on')
        if depends_on is None:
            return True  # No dependency
            
        # Find the dependent transaction in our tracking
        dependent_txn_id = None
        for i, tx_id in enumerate(self.transaction_ordering):
            if i == depends_on:
                dependent_txn_id = tx_id
                break
                
        if dependent_txn_id is None:
            self.log.warning(f"Transaction {txn_id} depends on index {depends_on} which doesn't exist")
            return True  # Can't find dependency, proceed anyway
            
        # Check if the dependent transaction is completed
        return dependent_txn_id in self.completed_transactions
    
    async def _send_to_slave(self, txn_id):
        """
        Send a transaction to the slave.
        
        Args:
            txn_id: Transaction ID to send
        """
        transaction_info = self.pending_transactions.get(txn_id)
        if not transaction_info:
            return
            
        transaction = transaction_info['transaction']
        
        # Log the forwarding
        self.log.debug(f"Forwarding transaction {txn_id} to slave")
        
        # Send to slave
        if hasattr(self.slave, 'process_request'):
            await self.slave.process_request(transaction)
        else:
            # Fallback if slave doesn't have a process_request method
            await self.slave.send(transaction)
    
    def _handle_slave_response(self, response):
        """
        Handle a response from the slave.
        
        Args:
            response: Response packet from slave
        """
        # Match response to a pending transaction
        matched_txn_id = None
        
        # Try to match by going through pending transactions in order
        for txn_id in self.transaction_ordering:
            if txn_id in self.pending_transactions and not self.pending_transactions[txn_id]['completed']:
                # This is a simple matching strategy - in a real implementation, matching would
                # be based on protocol-specific identifiers
                matched_txn_id = txn_id
                break
        
        if matched_txn_id:
            transaction_info = self.pending_transactions[matched_txn_id]
            
            # Mark as completed
            transaction_info['completed'] = True
            transaction_info['end_time'] = get_sim_time('ns')
            transaction_info['latency'] = transaction_info['end_time'] - transaction_info['start_time']
            
            # Store response
            self.responses[matched_txn_id] = response
            
            # Move from pending to completed
            self.completed_transactions[matched_txn_id] = transaction_info
            
            # Update statistics
            self.stats['pending_transactions'] -= 1
            self.stats['completed_transactions'] += 1
            
            # Log completion
            self.log.debug(
                f"Transaction {matched_txn_id} completed, latency: "
                f"{transaction_info['latency']} ns"
            )
            
            # Check if any waiting transactions now have satisfied dependencies
            self._check_waiting_transactions()
    
    def _check_waiting_transactions(self):
        """Check if any waiting transactions now have satisfied dependencies."""
        for txn_id in self.transaction_ordering:
            if (
                txn_id in self.pending_transactions 
                and not self.pending_transactions[txn_id]['completed']
                and self._is_dependency_satisfied(txn_id)
            ):
                # This transaction's dependencies are now satisfied, send it
                cocotb.start_soon(self._send_to_slave(txn_id))
    
    def _update_statistics(self):
        """Update handler statistics."""
        # Calculate latency statistics
        if self.completed_transactions:
            total_latency = sum(
                info['latency'] for info in self.completed_transactions.values()
            )
            avg_latency = total_latency / len(self.completed_transactions)
            min_latency = min(
                (info['latency'] for info in self.completed_transactions.values()),
                default=float('inf')
            )
            max_latency = max(
                (info['latency'] for info in self.completed_transactions.values()),
                default=0
            )
            
            self.stats['avg_latency'] = avg_latency
            self.stats['min_latency'] = min_latency
            self.stats['max_latency'] = max_latency
    
    def get_stats(self):
        """
        Get handler statistics.
        
        Returns:
            Dictionary with statistics
        """
        # Update statistics before returning
        self._update_statistics()
        return self.stats.copy()
    
    def get_transaction_status(self, txn_id=None):
        """
        Get status of a specific transaction or all transactions.
        
        Args:
            txn_id: Transaction ID to check, or None for all transactions
            
        Returns:
            Transaction status information
        """
        if txn_id is not None:
            # Return status of specific transaction
            if txn_id in self.completed_transactions:
                return {
                    'status': 'completed',
                    'info': self.completed_transactions[txn_id]
                }
            elif txn_id in self.pending_transactions:
                return {
                    'status': 'pending',
                    'info': self.pending_transactions[txn_id]
                }
            else:
                return {'status': 'unknown'}
        else:
            # Return status of all transactions
            return {
                'pending': len(self.pending_transactions),
                'completed': len(self.completed_transactions),
                'ordering': self.transaction_ordering
            }
    
    async def process_sequence(self, sequence):
        """
        Process a GAXI sequence through the master-slave connection.
        
        This method provides a high-level interface for processing an entire sequence
        of transactions, handling dependency tracking and monitoring completion.
        
        Args:
            sequence: GAXISequence to process
            
        Returns:
            Dictionary of responses by transaction index
        """
        # Generate packets from sequence
        packets = sequence.generate_packets()
        
        # Process each packet with dependency awareness
        response_map = {}
        
        # Track dependencies between sequence indexes and transaction IDs
        sequence_to_txn_id = {}
        completed_sequence_indexes = set()
        
        # Process each packet in order, but handling dependencies
        for sequence_index, packet in enumerate(packets):
            # Check for dependencies
            if hasattr(packet, 'depends_on_index'):
                depends_on = packet.depends_on_index
                # Wait for dependency to complete before sending this packet
                while depends_on not in completed_sequence_indexes:
                    await RisingEdge(self.master.clock)
            
            # Send through master
            await self.master.send(packet)
            
            # Get transaction ID
            txn_id = id(packet)
            sequence_to_txn_id[sequence_index] = txn_id
            
            # Wait for completion
            while txn_id not in self.completed_transactions:
                await RisingEdge(self.master.clock)
                
                # If the simulation is ending, break out
                if not self.running:
                    break
            
            # Mark this sequence index as completed
            completed_sequence_indexes.add(sequence_index)
            
            # Store the response
            if txn_id in self.responses:
                response_map[sequence_index] = self.responses[txn_id]
        
        return response_map
