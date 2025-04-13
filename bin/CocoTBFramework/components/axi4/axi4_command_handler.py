"""
AXI4 Command Handler

This module provides command handlers for coordinating AXI4 transactions
between address, data, and response channels, working with the sequence classes
and GAXI components.
"""

import cocotb
from collections import deque, defaultdict
from cocotb.triggers import RisingEdge, Timer, Event
from cocotb.utils import get_sim_time

from .axi4_seq_transaction import AXI4TransactionSequence
from .axi4_seq_address import AXI4AddressSequence
from .axi4_seq_data import AXI4DataSequence
from .axi4_seq_response import AXI4ResponseSequence
from .axi4_seq_protocol import AXI4ProtocolSequence


class AXI4CommandHandler:
    """
    Command handler for coordinating AXI4 transactions between channels.

    This class manages the flow of transactions between AXI4 components,
    translating high-level sequence objects into individual transactions
    that can be processed by the underlying GAXI infrastructure.
    """

    def __init__(self,
                    aw_master=None, w_master=None, b_slave=None,
                    ar_master=None, r_slave=None,
                    memory_model=None, log=None):
        """
        Initialize the AXI4 Command Handler.

        Args:
            aw_master: AW channel master component
            w_master: W channel master component
            b_slave: B channel slave component
            ar_master: AR channel master component
            r_slave: R channel slave component
            memory_model: Memory model for data storage
            log: Logger instance
        """
        # Store components
        self.aw_master = aw_master
        self.w_master = w_master
        self.b_slave = b_slave
        self.ar_master = ar_master
        self.r_slave = r_slave
        self.memory_model = memory_model
        self.log = log

        # Transaction tracking
        self.pending_write_transactions = {}  # id -> transaction info
        self.pending_read_transactions = {}   # id -> transaction info

        # Response tracking
        self.write_responses = {}  # id -> response info
        self.read_responses = {}   # id -> response info

        # Sequence completion events
        self.sequence_complete_events = {}

        # Transaction ordering
        self.transaction_order = []

        # Exclusive access monitoring
        self.exclusive_monitors = {}  # (id, addr) -> monitor info

        # Statistics
        self.stats = {
            'write_transactions': 0,
            'read_transactions': 0,
            'write_beats': 0,
            'read_beats': 0,
            'protocol_violations': 0
        }

        # Processing task
        self.processor_task = None
        self.running = False

    async def start(self):
        """
        Start the command handler processor.

        Returns:
            None
        """
        if not self.running:
            self.running = True

            # Start processor tasks
            if self.aw_master and self.w_master and self.b_slave:
                self.write_processor_task = cocotb.start_soon(self._process_write_transactions())

            if self.ar_master and self.r_slave:
                self.read_processor_task = cocotb.start_soon(self._process_read_transactions())

            self.log.info("AXI4 Command Handler started")

    async def stop(self):
        """
        Stop the command handler processor.

        Returns:
            None
        """
        self.running = False

        # Wait for tasks to complete
        if hasattr(self, 'write_processor_task') and self.write_processor_task:
            await Timer(10, units='ns')

        if hasattr(self, 'read_processor_task') and self.read_processor_task:
            await Timer(10, units='ns')

        self.log.info("AXI4 Command Handler stopped")

    async def process_transaction_sequence(self, sequence: AXI4TransactionSequence):
        """
        Process a complete AXI4 transaction sequence.

        Args:
            sequence: AXI4TransactionSequence to process

        Returns:
            Event that will be set when sequence is complete
        """
        if not self.running:
            await self.start()

        # Create completion event
        sequence_id = id(sequence)
        complete_event = Event(f"sequence_{sequence_id}_complete")
        self.sequence_complete_events[sequence_id] = complete_event

        # Process write address transactions
        await self.process_address_sequence(sequence.write_addr_sequence, is_read=False)

        # Process write data transactions
        await self.process_data_sequence(sequence.write_data_sequence)

        # Process read address transactions with dependencies
        await self.process_address_sequence(sequence.read_addr_sequence, is_read=True)

        # Return the completion event
        return complete_event

    async def process_address_sequence(self, sequence: AXI4AddressSequence, is_read: bool = False):
        """
        Process an AXI4 address sequence.

        Args:
            sequence: AXI4AddressSequence to process
            is_read: True for read (AR), False for write (AW)

        Returns:
            None
        """
        if not self.running:
            await self.start()

        # Generate packets from the sequence
        packets = sequence.generate_packets()

        if not packets:
            self.log.warning(f"Empty {'read' if is_read else 'write'} address sequence")
            return

        # Choose the appropriate master component
        master = self.ar_master if is_read else self.aw_master

        if not master:
            self.log.error(f"{'AR' if is_read else 'AW'} master not available")
            return

        # Send each packet to the master
        for packet in packets:
            # Check protocol compliance
            valid, message = packet.validate_axi4_protocol()
            if not valid:
                self.log.warning(f"Protocol violation: {message}")
                self.stats['protocol_violations'] += 1

            # Extract transaction ID
            id_field = 'arid' if is_read else 'awid'
            id_value = getattr(packet, id_field)

            # Calculate burst addresses
            burst_addresses = packet.get_burst_addresses()

            # Track the transaction
            if is_read:
                self.pending_read_transactions[id_value] = {
                    'packet': packet,
                    'addresses': burst_addresses,
                    'start_time': get_sim_time('ns'),
                    'completed': False
                }
                self.stats['read_transactions'] += 1
            else:
                self.pending_write_transactions[id_value] = {
                    'packet': packet,
                    'addresses': burst_addresses,
                    'start_time': get_sim_time('ns'),
                    'completed': False,
                    'data_complete': False  # Will be set when all data beats are received
                }
                self.stats['write_transactions'] += 1

            # Add to transaction order for dependency tracking
            self.transaction_order.append((id_value, is_read))

            # Check if exclusive access
            lock_field = 'arlock' if is_read else 'awlock'
            if hasattr(packet, lock_field) and getattr(packet, lock_field) == 1:
                # This is an exclusive access transaction
                if is_read:
                    # Set up exclusive monitor for read
                    self.exclusive_monitors[(id_value, burst_addresses[0])] = {
                        'active': True,
                        'start_time': get_sim_time('ns')
                    }
                else:
                    # Check if there's a valid exclusive monitor for this write
                    monitor_key = None
                    for key in self.exclusive_monitors:
                        monitor_id, monitor_addr = key
                        if monitor_addr == burst_addresses[0] and self.exclusive_monitors[key]['active']:
                            monitor_key = key
                            break

                    if monitor_key:
                        # Found valid exclusive monitor
                        self.exclusive_monitors[monitor_key]['expected_write_id'] = id_value
                    else:
                        # No valid monitor - this is a protocol violation
                        self.log.warning(f"Exclusive write without valid exclusive monitor for address 0x{burst_addresses[0]:X}")
                        self.stats['protocol_violations'] += 1

            # Send packet to master
            await master.send(packet)

            self.log.debug(f"Sent {'read' if is_read else 'write'} address packet: ID={id_value}, ADDR=0x{burst_addresses[0]:X}")

    async def process_data_sequence(self, sequence: AXI4DataSequence):
        """
        Process an AXI4 data sequence.

        Args:
            sequence: AXI4DataSequence to process

        Returns:
            None
        """
        if not self.running:
            await self.start()

        # Only support W channel for now
        if sequence.channel != 'W' or not self.w_master:
            self.log.error(f"Only W channel sequences supported, got {sequence.channel}")
            return

        # Generate packets from the sequence
        packets = sequence.generate_packets()

        if not packets:
            self.log.warning("Empty data sequence")
            return

        # Send each packet to the master
        for packet in packets:
            # We need to match data packets with address transactions
            # For simplicity, we'll assume data packets come in the same order as address packets
            # In a real implementation, we'd need a more sophisticated matching algorithm

            # Add to write beats count
            self.stats['write_beats'] += 1

            # Check if this is the last beat in a burst
            if hasattr(packet, 'wlast') and packet.wlast:
                # Find the corresponding address transaction
                # This is simplified - would need more logic in a real implementation
                for id_value, info in self.pending_write_transactions.items():
                    if not info.get('data_complete', False):
                        # Mark this transaction's data as complete
                        info['data_complete'] = True
                        break

            # Send packet to master
            await self.w_master.send(packet)

            self.log.debug(f"Sent write data packet: DATA=0x{packet.wdata:X}, LAST={getattr(packet, 'wlast', 0)}")

    async def process_response_sequence(self, sequence: AXI4ResponseSequence):
        """
        Process an AXI4 response sequence.

        Args:
            sequence: AXI4ResponseSequence to process

        Returns:
            None
        """
        if not self.running:
            await self.start()

        # Only support R channel for now (read responses)
        if sequence.channel != 'R' or not self.r_slave:
            self.log.error(f"Only R channel sequences supported, got {sequence.channel}")
            return

        # Generate packets from the sequence
        packets = sequence.generate_packets()

        if not packets:
            self.log.warning("Empty response sequence")
            return

        # Process packets according to sequence's ordering strategy
        id_to_packets = defaultdict(list)

        # Group packets by ID
        for packet in packets:
            id_value = packet.rid
            id_to_packets[id_value].append(packet)

        # Queue response bursts
        for id_value, id_packets in id_to_packets.items():
            # Set callback to track completion
            for packet in id_packets:
                # Add to read beats count
                self.stats['read_beats'] += 1

                # Send to R channel
                self.r_slave.queue_response(packet)

                self.log.debug(f"Queued read response packet: ID={id_value}, DATA=0x{packet.rdata:X}, LAST={packet.rlast}")

    async def _process_write_transactions(self):
        """
        Process write transactions and monitor responses.

        Returns:
            None
        """
        # Get the clock from one of the components
        clock = None
        if self.aw_master:
            clock = self.aw_master.clock
        elif self.w_master:
            clock = self.w_master.clock
        elif self.b_slave:
            clock = self.b_slave.clock

        if not clock:
            self.log.error("No clock available for write transaction processor")
            return

        # Set up B channel callback
        if self.b_slave:
            self.b_slave.add_callback(self._handle_write_response)

        self.log.debug("Write transaction processor started")

        while self.running:
            # Process write responses
            await self._check_write_completions()

            # Check sequence completions
            await self._check_sequence_completions()

            # Wait for next cycle
            await RisingEdge(clock)

        self.log.debug("Write transaction processor stopped")

    async def _process_read_transactions(self):
        """
        Process read transactions and monitor responses.

        Returns:
            None
        """
        # Get the clock from one of the components
        clock = None
        if self.ar_master:
            clock = self.ar_master.clock
        elif self.r_slave:
            clock = self.r_slave.clock

        if not clock:
            self.log.error("No clock available for read transaction processor")
            return

        # Set up R channel callback
        if self.r_slave:
            self.r_slave.add_callback(self._handle_read_response)

        self.log.debug("Read transaction processor started")

        while self.running:
            # Process read responses
            await self._check_read_completions()

            # Check sequence completions
            await self._check_sequence_completions()

            # Wait for next cycle
            await RisingEdge(clock)

        self.log.debug("Read transaction processor stopped")

    def _handle_write_response(self, response):
        """
        Handle B channel response from slave.

        Args:
            response: B channel response packet

        Returns:
            None
        """
        if not hasattr(response, 'bid'):
            self.log.error("Write response missing BID field")
            return

        id_value = response.bid

        # Store the response
        self.write_responses[id_value] = {
            'packet': response,
            'time': get_sim_time('ns')
        }

        # Check for exclusive access response
        if hasattr(response, 'bresp') and response.bresp == 1:
            for key in list(self.exclusive_monitors.keys()):
                monitor_id, monitor_addr = key
                monitor = self.exclusive_monitors[key]

                if monitor.get('expected_write_id') == id_value:
                    # This is the write we were expecting
                    # Clear the monitor
                    del self.exclusive_monitors[key]

                    self.log.debug(f"Exclusive monitor cleared for address 0x{monitor_addr:X}")

        self.log.debug(f"Received write response: ID={id_value}, RESP={getattr(response, 'bresp', 0)}")

    def _handle_read_response(self, response):
        """
        Handle R channel response from slave.

        Args:
            response: R channel response packet

        Returns:
            None
        """
        if not hasattr(response, 'rid'):
            self.log.error("Read response missing RID field")
            return

        id_value = response.rid

        # Add to read responses for this ID
        if id_value not in self.read_responses:
            self.read_responses[id_value] = {
                'packets': [],
                'start_time': get_sim_time('ns'),
                'complete': False
            }

        # Add this response packet
        self.read_responses[id_value]['packets'].append(response)

        # Check if this is the last packet in the burst
        if hasattr(response, 'rlast') and response.rlast:
            self.read_responses[id_value]['complete'] = True
            self.read_responses[id_value]['end_time'] = get_sim_time('ns')

        self.log.debug(f"Received read response: ID={id_value}, DATA=0x{getattr(response, 'rdata', 0):X}, LAST={getattr(response, 'rlast', 0)}")

    async def _check_write_completions(self):
        """
        Check for completed write transactions.

        Returns:
            None
        """
        for id_value, info in list(self.pending_write_transactions.items()):
            # Check if we have both data and response
            if info.get('data_complete', False) and id_value in self.write_responses:
                # This transaction is complete
                info['completed'] = True
                info['end_time'] = self.write_responses[id_value]['time']

                # Update transaction order
                if (id_value, False) in self.transaction_order:
                    self.transaction_order.remove((id_value, False))

                self.log.debug(f"Write transaction completed: ID={id_value}")

    async def _check_read_completions(self):
        """
        Check for completed read transactions.

        Returns:
            None
        """
        for id_value, info in list(self.pending_read_transactions.items()):
            # Check if we have all responses
            if id_value in self.read_responses and self.read_responses[id_value]['complete']:
                # This transaction is complete
                info['completed'] = True
                info['end_time'] = self.read_responses[id_value]['end_time']

                # Update transaction order
                if (id_value, True) in self.transaction_order:
                    self.transaction_order.remove((id_value, True))

                self.log.debug(f"Read transaction completed: ID={id_value}")

    async def _check_sequence_completions(self):
        """
        Check for completed sequences.

        Returns:
            None
        """
        for sequence_id, event in list(self.sequence_complete_events.items()):
            # Check if all transactions in the sequence are complete
            # Since we don't track which transactions belong to which sequence,
            # we'll use a simpler check - are there any pending transactions?
            if not self.pending_read_transactions and not self.pending_write_transactions:
                # All transactions are complete
                event.set()
                del self.sequence_complete_events[sequence_id]

                self.log.debug(f"Sequence {sequence_id} completed")

    def get_stats(self):
        """
        Get statistics about processed transactions.

        Returns:
            Dictionary with statistics
        """
        return self.stats
