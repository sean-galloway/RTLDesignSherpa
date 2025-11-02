# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GAXICommandHandler
# Purpose: Fixed GAXI Command Handler - Enhanced with sequential data generation
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Fixed GAXI Command Handler - Enhanced with sequential data generation

This version fixes the memory read issue and generates sequential data for reads
to make testing more predictable and easier to debug.
"""

import cocotb
from collections import deque
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time


class GAXICommandHandler:
    """
    Enhanced command handler for GAXI transactions with FIXED response generation.
    
    Key improvements:
    - Sequential data generation for reads
    - Better memory model integration
    - Improved field extraction for both APB and GAXI style packets
    - Enhanced debugging and logging
    """

    def __init__(self, master, slave, memory_model=None, log=None,
                 response_generation_mode=False, **kwargs):
        """Initialize the GAXI command handler."""
        self.master = master
        self.slave = slave
        self.response_generation_mode = response_generation_mode

        # Use unified memory model - either provided or from master
        self.memory_model = memory_model or getattr(master, 'memory_model', None)

        # Use unified logging
        self.log = log or getattr(master, 'log', None)

        # NEW: Sequential data generation for testing
        self.sequential_data_counter = 0x10000000  # Start with recognizable pattern
        self.sequential_data_step = 0x00000001     # Increment by 1 for each read

        # Transaction tracking - same as before
        self.pending_transactions = {}
        self.completed_transactions = {}
        self.transaction_ordering = []

        # Response tracking
        self.responses = {}

        # NEW: Response generation tracking
        self.pending_responses = {}
        self.generated_responses = {}

        # Statistics - enhanced with unified patterns
        self.stats = {
            'total_transactions': 0,
            'completed_transactions': 0,
            'pending_transactions': 0,
            'avg_latency': 0,
            'min_latency': float('inf'),
            'max_latency': 0,
            'dependency_violations': 0,
            'memory_operations': 0,
            'generated_responses': 0,
            'sequential_reads': 0,
            'memory_writes': 0,
            'memory_reads': 0,
            'response_generation_mode': response_generation_mode
        }

        # Processing task
        self.processor_task = None
        self.running = False

        # Response generation task
        self.response_task = None

    async def start(self):
        """Start the command handler processing task."""
        if not self.running:
            self.running = True

            if self.response_generation_mode:
                self.response_task = cocotb.start_soon(self._response_generation_loop())
                if self.log:
                    self.log.info("GAXI command handler started in response generation mode")
            else:
                self.processor_task = cocotb.start_soon(self._process_transactions())
                if self.log:
                    self.log.info("GAXI command handler started in forwarding mode")
        return self

    async def stop(self):
        """Stop the command handler processing task."""
        self.running = False
        if self.processor_task:
            await Timer(10, units='ns')
            self.processor_task = None
        if self.response_task:
            await Timer(10, units='ns')
            self.response_task = None

        if self.log:
            self.log.info("GAXI command handler stopped")
        return self

    async def _response_generation_loop(self):
        """Main loop for response generation mode."""
        if self.log:
            self.log.info("Starting response generation loop")

        while self.running:
            # Check for new transactions received by slave
            await self._check_slave_received_transactions()

            # Update statistics
            self._update_statistics()

            # Wait for next cycle
            await RisingEdge(self.master.clock)

    async def _check_slave_received_transactions(self):
        """Check for transactions received by slave and generate responses."""
        # Get received transactions from slave
        if hasattr(self.slave, '_recvQ') and self.slave._recvQ:
            # Process each received transaction
            while self.slave._recvQ:
                received_transaction = self.slave._recvQ.popleft()

                if self.log:
                    self.log.debug(f"Processing received transaction: {received_transaction}")

                # Generate response for this transaction
                await self._generate_response_for_transaction(received_transaction)

    async def _generate_response_for_transaction(self, cmd_transaction):
        """
        FIXED: Generate a response for a received command transaction.
        
        Now generates sequential data for reads instead of relying on memory.
        """
        try:
            response_id = f"rsp_{id(cmd_transaction)}"
            start_time = get_sim_time('ns')

            # Create response packet
            response_packet = self.master.create_packet()

            # FIXED: Extract command information using improved field extraction
            is_write = self._extract_field_value(cmd_transaction, 'pwrite', 'cmd_pwrite') == 1
            address = self._extract_field_value(cmd_transaction, 'paddr', 'cmd_paddr')

            if self.log:
                self.log.debug(f"Generating response for {'write' if is_write else 'read'} to addr=0x{address:08X}")

            if is_write:
                # Write operation - extract data and write to memory
                write_data = self._extract_field_value(cmd_transaction, 'pwdata', 'cmd_pwdata')
                write_strb = self._extract_field_value(cmd_transaction, 'pstrb', 'cmd_pstrb', default=0xF)

                if self.log:
                    self.log.debug(f"Processing write: addr=0x{address:08X}, data=0x{write_data:08X}, strb=0x{write_strb:X}")

                # Handle memory operation
                success = await self._handle_memory_write(address, write_data, write_strb)
                self.stats['memory_writes'] += 1

                # Set response fields for write (no data response needed)
                self._set_response_field(response_packet, 'prdata', 'rsp_prdata', 0)
                self._set_response_field(response_packet, 'pslverr', 'rsp_pslverr', 0 if success else 1)

            else:
                # Read operation - FIXED: generate sequential data or read from memory
                if self.log:
                    self.log.debug(f"Processing read: addr=0x{address:08X}")

                # FIXED: Try memory first, then fall back to sequential data
                success, read_data = await self._handle_memory_read(address)
                
                if not success or read_data == 0:
                    # Generate sequential data for more predictable testing
                    read_data = self._generate_sequential_data(address)
                    self.stats['sequential_reads'] += 1
                    if self.log:
                        self.log.debug(f"Generated sequential data: addr=0x{address:08X}, data=0x{read_data:08X}")
                else:
                    self.stats['memory_reads'] += 1
                    if self.log:
                        self.log.debug(f"Read from memory: addr=0x{address:08X}, data=0x{read_data:08X}")

                # Set response fields for read
                self._set_response_field(response_packet, 'prdata', 'rsp_prdata', read_data)
                self._set_response_field(response_packet, 'pslverr', 'rsp_pslverr', 0)

            # Track response
            self.pending_responses[response_id] = {
                'response_packet': response_packet,
                'command_transaction': cmd_transaction,
                'start_time': start_time,
                'is_write': is_write,
                'address': address
            }

            # Send the response
            prdata = self._extract_field_value(response_packet, 'prdata', 'rsp_prdata', default=0)
            pslverr = self._extract_field_value(response_packet, 'pslverr', 'rsp_pslverr', default=0)

            if self.log:
                self.log.debug(f"Sending response: prdata=0x{prdata:08X}, pslverr={pslverr}")

            await self.master.send(response_packet)

            # Mark as completed
            end_time = get_sim_time('ns')
            self.generated_responses[response_id] = self.pending_responses.pop(response_id)
            self.generated_responses[response_id]['end_time'] = end_time
            self.generated_responses[response_id]['latency'] = end_time - start_time

            # Update statistics
            self.stats['generated_responses'] += 1
            self.stats['memory_operations'] += 1

        except Exception as e:
            if self.log:
                self.log.error(f"Error generating response: {e}")
                import traceback
                self.log.error(traceback.format_exc())

    def _generate_sequential_data(self, address):
        """
        NEW: Generate sequential data based on address for predictable testing.
        
        Args:
            address: Address being read
            
        Returns:
            Sequential data value
        """
        # Generate data based on address for predictability
        # Use address as part of the data pattern
        data = self.sequential_data_counter + (address >> 2)  # Word-aligned addressing
        self.sequential_data_counter += self.sequential_data_step
        
        # Keep data in 32-bit range
        data = data & 0xFFFFFFFF
        
        return data

    def _extract_field_value(self, transaction, field_name, alt_field_name=None, default=0):
        """
        FIXED: Extract a field value from a transaction supporting both storage methods.
        
        Handles both APB-style attributes and GAXI-style fields dictionary.
        """
        # First try fields dictionary (GAXI style)
        if hasattr(transaction, 'fields') and isinstance(transaction.fields, dict):
            if field_name in transaction.fields:
                value = transaction.fields[field_name]
                if value is not None:
                    return value
        
        # Try primary field name as attribute (APB style)
        if hasattr(transaction, field_name):
            value = getattr(transaction, field_name)
            if value is not None:
                return value

        # Try alternative field name as attribute
        if alt_field_name and hasattr(transaction, alt_field_name):
            value = getattr(transaction, alt_field_name)
            if value is not None:
                return value

        # Try lowercase versions
        if hasattr(transaction, field_name.lower()):
            value = getattr(transaction, field_name.lower())
            if value is not None:
                return value

        if alt_field_name and hasattr(transaction, alt_field_name.lower()):
            value = getattr(transaction, alt_field_name.lower())
            if value is not None:
                return value

        return default

    def _set_response_field(self, response_packet, field_name, alt_field_name=None, value=0):
        """
        FIXED: Set a field value in a response packet supporting both storage methods.
        """
        # First try fields dictionary (GAXI style)
        if hasattr(response_packet, 'fields') and isinstance(response_packet.fields, dict):
            if field_name in response_packet.field_config:
                response_packet.fields[field_name] = value
                return
        
        # Try primary field name as attribute (APB style)
        if hasattr(response_packet, field_name):
            setattr(response_packet, field_name, value)
            return

        # Try alternative field name as attribute
        if alt_field_name and hasattr(response_packet, alt_field_name):
            setattr(response_packet, alt_field_name, value)
            return

        # Try lowercase versions
        if hasattr(response_packet, field_name.lower()):
            setattr(response_packet, field_name.lower(), value)
            return

        if alt_field_name and hasattr(response_packet, alt_field_name.lower()):
            setattr(response_packet, alt_field_name.lower(), value)
            return

        if self.log:
            self.log.warning(f"Could not find field '{field_name}' or '{alt_field_name}' in response packet")

    async def _handle_memory_write(self, address, data, strobe):
        """
        FIXED: Handle memory write operation with better error handling.
        """
        if self.memory_model:
            try:
                # Convert integer to bytearray for memory write
                data_bytes = self.memory_model.integer_to_bytearray(data, 4)  # 32-bit
                
                # Write to memory with proper address masking
                success = self.memory_model.write(address & 0xFFFF, data_bytes, strobe)

                if self.log:
                    self.log.debug(f"Memory write {'successful' if success else 'failed'}: "
                                  f"addr=0x{address:X}, data=0x{data:X}, strobe=0x{strobe:X}")

                return success
            except Exception as e:
                if self.log:
                    self.log.error(f"Memory write error: {e}")
                return False
        else:
            # No memory model - assume success
            if self.log:
                self.log.debug(f"No memory model, assuming write success: addr=0x{address:X}, data=0x{data:X}")
            return True

    async def _handle_memory_read(self, address):
        """
        FIXED: Handle memory read operation with better error handling.
        """
        if self.memory_model:
            try:
                # Read from memory with proper address masking
                data_bytes = self.memory_model.read(address & 0xFFFF, 4)  # 32-bit
                data = self.memory_model.bytearray_to_integer(data_bytes)

                if self.log:
                    self.log.debug(f"Memory read: addr=0x{address:X}, data=0x{data:X}")

                return True, data
            except Exception as e:
                if self.log:
                    self.log.debug(f"Memory read error (will use sequential data): {e}")
                return False, 0
        else:
            # No memory model - will use sequential data
            if self.log:
                self.log.debug(f"No memory model, will use sequential data for addr=0x{address:X}")
            return False, 0

    # Keep existing methods for backward compatibility
    async def _process_transactions(self):
        """Original processing loop for forwarding mode (master→slave)."""
        # Set up callbacks for slave responses
        if hasattr(self.slave, 'add_callback'):
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
        """Forward transactions from master to slave using unified interfaces."""
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

            # Handle memory operations if memory model available
            if self.memory_model:
                await self._handle_memory_operation(transaction)

            # Forward to slave if dependency is satisfied or no dependency
            if self._is_dependency_satisfied(txn_id):
                await self._send_to_slave(txn_id)
            else:
                if self.log:
                    self.log.debug(f"Transaction {txn_id} waiting for dependency to complete")

    async def _handle_memory_operation(self, transaction):
        """Handle memory operations using base MemoryModel directly."""
        try:
            # Use base MemoryModel methods directly
            if hasattr(transaction, 'addr') and hasattr(transaction, 'data'):
                success, error = self.memory_model.write_transaction(
                    transaction,
                    component_name="GAXICommandHandler"
                )

                if success:
                    self.stats['memory_operations'] += 1
                    if self.log:
                        self.log.debug(f"Memory write successful: addr=0x{transaction.addr:X}, data=0x{transaction.data:X}")
                else:
                    if self.log:
                        self.log.warning(f"Memory write failed: {error}")

        except Exception as e:
            if self.log:
                self.log.error(f"Error in memory operation: {e}")

    def _is_dependency_satisfied(self, txn_id):
        """Check if a transaction's dependencies are satisfied."""
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
            if self.log:
                self.log.warning(f"Transaction {txn_id} depends on index {depends_on} which doesn't exist")
            self.stats['dependency_violations'] += 1
            return True  # Can't find dependency, proceed anyway

        # Check if the dependent transaction is completed
        return dependent_txn_id in self.completed_transactions

    async def _send_to_slave(self, txn_id):
        """Send a transaction to the slave using unified interface."""
        transaction_info = self.pending_transactions.get(txn_id)
        if not transaction_info:
            return

        transaction = transaction_info['transaction']

        # Log the forwarding
        if self.log:
            self.log.debug(f"Forwarding transaction {txn_id} to slave")

        # Send to slave using standard interface
        if hasattr(self.slave, 'process_request'):
            await self.slave.process_request(transaction)
        elif hasattr(self.slave, 'send'):
            await self.slave.send(transaction)
        else:
            # Slave is a monitor - transactions will be observed automatically
            if self.log:
                self.log.debug(f"Slave is monitor - transaction will be observed automatically")

    def _handle_slave_response(self, response):
        """Handle a response from the slave."""
        # Match response to a pending transaction
        matched_txn_id = None

        # Try to match by going through pending transactions in order
        for txn_id in self.transaction_ordering:
            if txn_id in self.pending_transactions and not self.pending_transactions[txn_id]['completed']:
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
            if self.log:
                self.log.debug(f"Transaction {matched_txn_id} completed, latency: {transaction_info['latency']} ns")

            # Check if any waiting transactions now have satisfied dependencies
            self._check_waiting_transactions()

    def _check_waiting_transactions(self):
        """Check if any waiting transactions now have satisfied dependencies."""
        for txn_id in self.transaction_ordering:
            if (txn_id in self.pending_transactions and 
                not self.pending_transactions[txn_id]['completed'] and
                self._is_dependency_satisfied(txn_id)):
                # This transaction's dependencies are now satisfied, send it
                cocotb.start_soon(self._send_to_slave(txn_id))

    def _update_statistics(self):
        """Update handler statistics using unified patterns."""
        # Calculate latency statistics
        if self.completed_transactions:
            total_latency = sum(info['latency'] for info in self.completed_transactions.values())
            avg_latency = total_latency / len(self.completed_transactions)
            min_latency = min(info['latency'] for info in self.completed_transactions.values())
            max_latency = max(info['latency'] for info in self.completed_transactions.values())

            self.stats['avg_latency'] = avg_latency
            self.stats['min_latency'] = min_latency
            self.stats['max_latency'] = max_latency

        # Add response generation statistics
        if self.generated_responses:
            total_response_latency = sum(info['latency'] for info in self.generated_responses.values())
            avg_response_latency = total_response_latency / len(self.generated_responses)
            self.stats['avg_response_latency'] = avg_response_latency

    def get_stats(self):
        """Get handler statistics including unified component stats."""
        # Update statistics before returning
        self._update_statistics()

        # Get stats from unified components
        handler_stats = self.stats.copy()

        # Add component stats if available
        if hasattr(self.master, 'get_stats'):
            handler_stats['master_stats'] = self.master.get_stats()
        if hasattr(self.slave, 'get_stats'):
            handler_stats['slave_stats'] = self.slave.get_stats()

        # Add memory stats if available
        if self.memory_model and hasattr(self.memory_model, 'get_stats'):
            handler_stats['memory_stats'] = self.memory_model.get_stats()

        return handler_stats

    def get_transaction_status(self, txn_id=None):
        """Get status of a specific transaction or all transactions."""
        if txn_id is not None:
            # Return status of specific transaction
            if txn_id in self.completed_transactions:
                return {'status': 'completed', 'info': self.completed_transactions[txn_id]}
            elif txn_id in self.pending_transactions:
                return {'status': 'pending', 'info': self.pending_transactions[txn_id]}
            else:
                return {'status': 'unknown'}
        else:
            # Return status of all transactions
            return {
                'pending': len(self.pending_transactions),
                'completed': len(self.completed_transactions),
                'ordering': self.transaction_ordering,
                'pending_responses': len(self.pending_responses),
                'generated_responses': len(self.generated_responses)
            }

    def reset(self):
        """Reset the command handler to initial state."""
        self.pending_transactions.clear()
        self.completed_transactions.clear()
        self.transaction_ordering.clear()
        self.responses.clear()

        # Reset response generation state
        self.pending_responses.clear()
        self.generated_responses.clear()

        # Reset sequential data counter
        self.sequential_data_counter = 0x10000000

        # Reset statistics
        self.stats = {
            'total_transactions': 0,
            'completed_transactions': 0,
            'pending_transactions': 0,
            'avg_latency': 0,
            'min_latency': float('inf'),
            'max_latency': 0,
            'dependency_violations': 0,
            'memory_operations': 0,
            'generated_responses': 0,
            'sequential_reads': 0,
            'memory_writes': 0,
            'memory_reads': 0,
            'response_generation_mode': self.response_generation_mode
        }

        if self.log:
            self.log.info("GAXI command handler reset")

    async def process_sequence(self, sequence):
        """
        Process a GAXI sequence through the master-slave connection.

        This method provides a high-level interface for processing an entire sequence
        of transactions, handling dependency tracking and monitoring completion.

        Updated to work with unified sequence infrastructure.

        Args:
            sequence: GAXISequence to process

        Returns:
            Dictionary of responses by transaction index
        """
        # This method only works in forwarding mode
        if self.response_generation_mode:
            if self.log:
                self.log.warning("process_sequence() not supported in response generation mode")
            return {}

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

            # Send through master using unified interface
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

    def __str__(self):
        """String representation of command handler."""
        mode = "Response Generation" if self.response_generation_mode else "Forwarding"
        if self.response_generation_mode:
            return (f"GAXICommandHandler ({mode}): {self.stats['generated_responses']} responses generated, "
                    f"{self.stats['sequential_reads']} sequential reads")
        else:
            return (f"GAXICommandHandler ({mode}): {self.stats['completed_transactions']}/{self.stats['total_transactions']} "
                    f"completed, {self.stats['pending_transactions']} pending")
