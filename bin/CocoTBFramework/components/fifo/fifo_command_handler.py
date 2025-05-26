"""
FIFO Command Handler for Master-Slave Communication with Enhanced Error Detection

This module provides a command handler to coordinate transactions between
FIFO Master and Slave components, handling packet routing, timing,
response matching, and advanced error detection.
"""

import cocotb
from collections import deque
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time


class FIFOCommandHandler:
    """
    Command handler for FIFO transactions between master and slave components.

    This class coordinates communication between FIFOMaster and FIFOSlave
    components, handling packet routing, timing, and response matching.
    It supports transaction dependencies, provides monitoring
    capabilities for transaction flow, and includes enhanced error detection.
    """

    def __init__(self, master, slave, memory_model=None, log=None, fifo_capacity=8):
        """
        Initialize the FIFO command handler.

        Args:
            master: FIFOMaster instance
            slave: FIFOSlave instance
            memory_model: Optional memory model (if None, uses master's memory model)
            log: Logger instance
            fifo_capacity: FIFO capacity in entries for modeling
        """
        self.master = master
        self.slave = slave
        self.memory_model = memory_model or getattr(master, 'memory_model', None)
        self.log = log or getattr(master, 'log', None)
        self.fifo_capacity = fifo_capacity

        # Transaction tracking
        self.pending_transactions = {}  # txn_id -> transaction info
        self.completed_transactions = {}  # txn_id -> transaction info
        self.transaction_ordering = []  # List of transaction IDs in order of receipt

        # FIFO state tracking
        self.fifo_depth = 0  # Current number of items in FIFO
        self.fifo_state = {
            'depth': 0,
            'empty': True,
            'full': False,
            'overflow_prevented': 0,
            'underflow_prevented': 0,
            'last_check_time': 0,
            'max_depth_reached': 0
        }

        # Response tracking
        self.responses = {}  # txn_id -> response info
        self.callbacks = []  # List of callback functions

        # Error tracking
        self.error_log = []  # List of detected errors with timestamps
        self.error_counts = {
            'overflow_attempts': 0,
            'underflow_attempts': 0,
            'dependency_violations': 0,
            'timeout_errors': 0,
            'protocol_violations': 0
        }

        # Statistics
        self.stats = {
            'total_transactions': 0,
            'completed_transactions': 0,
            'pending_transactions': 0,
            'avg_latency': 0,
            'min_latency': float('inf'),
            'max_latency': 0,
            'fifo_fullness_max': 0,
            'fifo_deadlocks_prevented': 0,
            'error_counts': self.error_counts
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
            await Timer(10, units='ns')
            self.processor_task = None
            self.log.info("FIFO command handler stopped")
        return self

    def add_callback(self, callback):
        """
        Add a callback function to be called when slave responds.

        Args:
            callback: Function to call with response packet

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

    async def _process_transactions(self):
        """
        Main processing loop for transactions from master to slave.

        This monitors the master's sent queue and forwards transactions to the slave,
        then tracks responses through callbacks. Includes enhanced error detection.
        """
        # Set up callbacks for slave responses
        self.slave.add_callback(self._handle_slave_response)

        # Main processing loop
        while self.running:
            # Check for new transactions from master to forward to slave
            await self._forward_transactions()

            # Update FIFO state
            self._update_fifo_state()

            # Check for potential protocol violations
            self._check_protocol_violations()

            # Update statistics
            self._update_statistics()

            # Wait for next cycle
            await RisingEdge(self.master.clock)

    async def _forward_transactions(self):
        """Forward transactions from master to slave when FIFO is not full."""
        # Check if FIFO is full, if so skip forwarding
        if self.fifo_state['full']:
            return

        # Check if master has sent transactions to forward
        if hasattr(self.master, 'sent_queue') and self.master.sent_queue:
            # Take the next transaction from the master's queue
            transaction = self.master.sent_queue.popleft()

            # Generate a unique ID for tracking this transaction
            txn_id = id(transaction)

            # Set a transaction ID on the packet for later identification
            transaction.transaction_id = txn_id

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

            # Update FIFO depth
            self.fifo_depth += 1
            if self.fifo_depth > self.stats['fifo_fullness_max']:
                self.stats['fifo_fullness_max'] = self.fifo_depth

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
            # Log error
            self.error_counts['dependency_violations'] += 1
            self.error_log.append({
                'time': get_sim_time('ns'),
                'type': 'dependency_missing',
                'details': f"Transaction {txn_id} depends on non-existent index {depends_on}"
            })
            return True  # Can't find dependency, proceed anyway

        # Check if the dependent transaction is completed
        dependency_satisfied = dependent_txn_id in self.completed_transactions

        # If not satisfied, log for debugging
        if not dependency_satisfied:
            self.log.debug(f"Transaction {txn_id} waiting for dependency {dependent_txn_id} to complete")

        return dependency_satisfied

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

        # Send to slave using appropriate method
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

        # First try matching by transaction_id if available
        if hasattr(response, 'transaction_id') and response.transaction_id:
            if response.transaction_id in self.pending_transactions:
                matched_txn_id = response.transaction_id

        # If no match by ID, match by order for compatibility
        if matched_txn_id is None:
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

            # Update FIFO depth
            self.fifo_depth -= 1

            # Update statistics
            self.stats['pending_transactions'] -= 1
            self.stats['completed_transactions'] += 1

            # Log completion
            self.log.debug(
                f"Transaction {matched_txn_id} completed, latency: "
                f"{transaction_info['latency']} ns"
            )

            # Execute callbacks
            for callback in self.callbacks:
                try:
                    callback(response)
                except Exception as e:
                    self.log.error(f"Error in callback: {e}")

            # Check if any waiting transactions now have satisfied dependencies
            self._check_waiting_transactions()
        else:
            # No matching transaction found - log warning
            self.log.warning(f"Received response with no matching pending transaction")
            self.error_log.append({
                'time': get_sim_time('ns'),
                'type': 'unmatched_response',
                'details': "Received response with no matching pending transaction"
            })

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

    def _update_fifo_state(self):
        """Update the FIFO state (empty, full, etc.)."""
        # Update state
        current_time = get_sim_time('ns')
        self.fifo_state['last_check_time'] = current_time
        self.fifo_state['depth'] = self.fifo_depth
        self.fifo_state['empty'] = self.fifo_depth == 0
        self.fifo_state['full'] = self.fifo_depth >= self.fifo_capacity

        # Update max depth tracking
        if self.fifo_depth > self.fifo_state['max_depth_reached']:
            self.fifo_state['max_depth_reached'] = self.fifo_depth

        # Check for overflow attempt
        if self.fifo_state['full'] and hasattr(self.master, 'sent_queue') and self.master.sent_queue:
            self.fifo_state['overflow_prevented'] += 1
            self.error_counts['overflow_attempts'] += 1
            self.error_log.append({
                'time': current_time,
                'type': 'overflow_attempt',
                'details': f"Attempted to write to full FIFO (depth={self.fifo_depth}/{self.fifo_capacity})"
            })

        # Check for deadlock
        if self.fifo_state['full'] and self.stats['pending_transactions'] > 0 and self.stats['completed_transactions'] == 0:
            # This could be a deadlock
            self.log.warning("Potential deadlock detected: FIFO full and no transactions completed")
            self.stats['fifo_deadlocks_prevented'] += 1
            self.error_log.append({
                'time': current_time,
                'type': 'potential_deadlock',
                'details': "FIFO full and no transactions completed"
            })

    def _check_protocol_violations(self):
        """Check for potential protocol violations based on component signals."""
        # Only perform checks if we have access to the relevant signals
        if not (hasattr(self.master, 'write_sig') and hasattr(self.master, 'full_sig') and
                hasattr(self.slave, 'read_sig') and hasattr(self.slave, 'empty_sig')):
            return

        current_time = get_sim_time('ns')

        # Check for write-while-full violation
        if (self.master.write_sig.value.is_resolvable and
            self.master.full_sig.value.is_resolvable and
            int(self.master.write_sig.value) == 1 and
            int(self.master.full_sig.value) == 1):

            self.log.warning(f"Protocol violation: Write while full at {current_time}ns")
            self.error_counts['protocol_violations'] += 1
            self.error_log.append({
                'time': current_time,
                'type': 'write_while_full',
                'details': "Write asserted while FIFO is full"
            })

        # Check for read-while-empty violation
        if (self.slave.read_sig.value.is_resolvable and
            self.slave.empty_sig.value.is_resolvable and
            int(self.slave.read_sig.value) == 1 and
            int(self.slave.empty_sig.value) == 1):

            self.log.warning(f"Protocol violation: Read while empty at {current_time}ns")
            self.error_counts['protocol_violations'] += 1
            self.error_log.append({
                'time': current_time,
                'type': 'read_while_empty',
                'details': "Read asserted while FIFO is empty"
            })

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

    def get_fifo_state(self):
        """
        Get current FIFO state.

        Returns:
            Dictionary with FIFO state information
        """
        return self.fifo_state.copy()

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

    def get_error_log(self):
        """
        Get log of detected errors.

        Returns:
            List of error entries with timestamps
        """
        return self.error_log.copy()

    async def process_sequence(self, sequence):
        """
        Process a FIFO sequence through the master-slave connection.

        This method provides a high-level interface for processing an entire sequence
        of transactions, handling dependency tracking and monitoring completion.

        Args:
            sequence: FIFOSequence to process

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
            if hasattr(packet, 'depends_on_index') and packet.depends_on_index is not None:
                depends_on = packet.depends_on_index
                # Wait for dependency to complete before sending this packet
                while depends_on not in completed_sequence_indexes:
                    await RisingEdge(self.master.clock)

            # Send through master
            await self.master.send(packet)

            # Get transaction ID from sent queue
            # Find the transaction in the ordering that matches this packet
            if self.transaction_ordering:
                txn_id = self.transaction_ordering[-1]  # Most recent transaction
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

    def add_error_handler(self, handler_function):
        """
        Add a function to be called when errors are detected.

        Args:
            handler_function: Function to call with error information

        Returns:
            Self for method chaining
        """
        # Create a callback that checks for errors
        def error_check_callback(response):
            if len(self.error_log) > 0:
                # Get the most recent error
                latest_error = self.error_log[-1]
                # Call the handler with the error info
                handler_function(latest_error)

        # Add as a regular callback
        self.add_callback(error_check_callback)
        return self

    def clear_error_log(self):
        """
        Clear the error log.

        Returns:
            Self for method chaining
        """
        self.error_log.clear()
        for key in self.error_counts:
            self.error_counts[key] = 0
        return self