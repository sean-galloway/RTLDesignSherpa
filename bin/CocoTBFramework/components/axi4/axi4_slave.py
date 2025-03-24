"""
AXI4 Slave Component for Verification

This module provides the AXI4Slave class for AXI4 slave interfaces with
support for in-order and out-of-order transaction processing.
"""

import cocotb
import random
from collections import deque
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master, create_gaxi_slave
from CocoTBFramework.components.flex_randomizer import FlexRandomizer

from .axi4_fields_signals import (
    AXI4_AW_FIELD_CONFIG,
    AXI4_W_FIELD_CONFIG,
    AXI4_B_FIELD_CONFIG,
    AXI4_AR_FIELD_CONFIG,
    AXI4_R_FIELD_CONFIG,
    AXI4_MASTER_DEFAULT_CONSTRAINTS,
    adjust_field_configs,
    get_aw_signal_map,
    get_w_signal_map,
    get_b_signal_map,
    get_ar_signal_map,
    get_r_signal_map
)
from .axi4_packets import AXI4Packet


class AXI4Slave:
    """
    AXI4 Slave component that manages multiple channels for AXI4 transactions.

    This class provides:
    - Separate GAXI slaves for each AXI4 channel (AW, W, B, AR, R)
    - Memory model for handling read/write operations
    - AXI4 protocol checking
    - Response ordering control (in-order or out-of-order between different IDs)
    """

    def __init__(self, dut, title, prefix, divider, suffix, clock, channels,
                    id_width=8, addr_width=32, data_width=32, user_width=1,
                    memory_model=None, randomizers=None, check_protocol=False,
                    inorder=False, ooo_strategy='random', log=None):
        """
        Initialize AXI4 Slave component.

        Args:
            dut: Device under test
            title: Component title
            prefix: Signal prefix
            divider: used if there is an '_' between the channel and the signal
            suffix: optional suffix useed at the end
            clock: Clock signal
            channels: a list of the channels to instantiate
            id_width: Width of ID fields (default: 8)
            addr_width: Width of address fields (default: 32)
            data_width: Width of data fields (default: 32)
            user_width: Width of user fields (default: 1)
            memory_model: Memory model for data storage
            randomizers: Dict of randomizers for each channel (keys: 'b', 'r')
            check_protocol: Enable AXI4 protocol checking (default: True)
            inorder: If True, force in-order responses across different IDs (default: False)
            ooo_strategy: Strategy for out-of-order responses ('random', 'round_robin', 'weighted')
            log: Logger instance
        """
        self.title = title
        self.clock = clock
        self.log = log
        self.check_protocol = check_protocol
        self.memory_model = memory_model
        self.inorder = inorder
        self.ooo_strategy = ooo_strategy
        self.channels = [s.upper() for s in channels]

        # Calculate strobe width
        self.strb_width = data_width // 8

        # Adjust field configs for the specified widths
        field_configs = {
            'AW': AXI4_AW_FIELD_CONFIG,
            'W':  AXI4_W_FIELD_CONFIG,
            'B':  AXI4_B_FIELD_CONFIG,
            'AR': AXI4_AR_FIELD_CONFIG,
            'R':  AXI4_R_FIELD_CONFIG
        }
        adjusted_configs = adjust_field_configs(
            field_configs, id_width, addr_width, data_width, user_width
        )

        self.aw_field_config = adjusted_configs['AW']
        self.w_field_config = adjusted_configs['W']
        self.b_field_config = adjusted_configs['B']
        self.ar_field_config = adjusted_configs['AR']
        self.r_field_config = adjusted_configs['R']

        # Prepare signal mappings
        aw_signal_map, aw_optional_signal_map = get_aw_signal_map(prefix, divider, suffix)
        w_signal_map, w_optional_signal_map = get_w_signal_map(prefix, divider, suffix)
        b_signal_map, b_optional_signal_map = get_b_signal_map(prefix, divider, suffix)
        ar_signal_map, ar_optional_signal_map = get_ar_signal_map(prefix, divider, suffix)
        r_signal_map, r_optional_signal_map = get_r_signal_map(prefix, divider, suffix)

        # Get randomizers
        randomizers = randomizers or {}
        b_randomizer = randomizers.get('b', FlexRandomizer(AXI4_MASTER_DEFAULT_CONSTRAINTS))
        r_randomizer = randomizers.get('r', FlexRandomizer(AXI4_MASTER_DEFAULT_CONSTRAINTS))

        # Create channel components
        if 'AW' in self.channels:
            self.aw_slave = create_gaxi_slave(
                dut, f"{title}_AW", "", clock,
                field_config=self.aw_field_config,
                multi_sig=True,
                signal_map=aw_signal_map,
                optional_signal_map=aw_optional_signal_map,
                log=log
            )
            self.aw_slave.add_callback(self._handle_aw_transaction)
        else:
            self.aw_master = None

        if 'W' in self.channels:
            self.w_slave = create_gaxi_slave(
                dut, f"{title}_W", "", clock,
                field_config=self.w_field_config,
                multi_sig=True,
                signal_map=w_signal_map,
                optional_signal_map=w_optional_signal_map,
                log=log
            )
            self.w_slave.add_callback(self._handle_w_transaction)
        else:
            self.w_master = None

        if 'B' in self.channels:
            self.b_master = create_gaxi_master(
                dut, f"{title}_B", "", clock,
                field_config=self.b_field_config,
                randomizer=b_randomizer,
                multi_sig=True,
                signal_map=b_signal_map,
                optional_signal_map=b_optional_signal_map,
                log=log
            )
        else:
            self.b_master = None

        if 'AR' in self.channels:
            self.ar_slave = create_gaxi_slave(
                dut, f"{title}_AR", "", clock,
                field_config=self.ar_field_config,
                multi_sig=True,
                signal_map=ar_signal_map,
                optional_signal_map=ar_optional_signal_map,
                log=log
            )
            self.ar_slave.add_callback(self._handle_ar_transaction)
        else:
            self.ar_slave = None

        if 'R' in self.channels:
            self.r_master = create_gaxi_master(
                dut, f"{title}_R", "", clock,
                field_config=self.r_field_config,
                randomizer=r_randomizer,
                multi_sig=True,
                signal_map=r_signal_map,
                optional_signal_map=r_optional_signal_map,
                log=log
            )
        else:
            self.r_master = None

        # Initialize transaction tracking
        self.pending_writes = {}  # Write address transactions waiting for data
        self.pending_reads = {}   # Read transactions waiting to be processed

        # Queue structure for ordering responses
        self.write_response_queue = deque()  # Queue of write responses to send
        self.read_response_queue = deque()   # Queue of read responses to send

        # Transaction ordering trackers
        self.next_write_id = None  # Next write ID to process for in-order mode
        self.next_read_id = None   # Next read ID to process for in-order mode

        # Weights for weighted OOO strategy - can be adjusted at runtime
        self.ooo_weights = {}

        # Start processor task
        self.processor_task = None
        self.running = False

        self.log.info(f"AXI4Slave '{title}' initialized")

    async def reset_bus(self):
        """Reset all AXI4 channels"""
        if 'AW' in self.channels:
            await self.aw_slave.reset_bus()
        if 'W' in self.channels:
            await self.w_slave.reset_bus()
        if 'B' in self.channels:
            await self.b_master.reset_bus()
        if 'AR' in self.channels:
            await self.ar_slave.reset_bus()
        if 'R' in self.channels:
            await self.r_master.reset_bus()

        # Clear transaction/responsses
        if 'W' in self.channels:
            self.pending_writes.clear()
            self.write_response_queue.clear()

        if 'R' in self.channels:
            self.pending_reads.clear()
            self.read_response_queue.clear()

        # Reset ordering trackers
        self.next_write_id = None
        self.next_read_id = None

    async def start_processor(self):
        """Start transaction processor task"""
        if not self.running:
            self.running = True
            self.processor_task = cocotb.start_soon(self._transaction_processor())
            self.log.info(f"AXI4Slave '{self.title}' processor started")

    async def stop_processor(self):
        """Stop transaction processor task"""
        self.running = False
        if self.processor_task:
            await Timer(10, units='ns')  # Allow task to complete
            self.processor_task = None
            self.log.info(f"AXI4Slave '{self.title}' processor stopped")

    def _handle_aw_transaction(self, transaction):
        """Process Write Address (AW) channel transaction"""
        # Extract ID for tracking
        if not hasattr(transaction, 'awid'):
            self.log.error("AW transaction missing awid field")
            return

        id_value = transaction.awid

        # Validate protocol if enabled
        if self.check_protocol:
            valid, error_msg = transaction.validate_axi4_protocol()
            if not valid:
                self.log.error(f"AXI4 protocol error (AW): {error_msg}")
                # Still process the transaction, but note the error

        # Store the transaction for matching with write data
        self.pending_writes[id_value] = {
            'aw_transaction': transaction,
            'w_transactions': [],
            'start_time': get_sim_time('ns'),
            'addresses': transaction.get_burst_addresses() if hasattr(transaction, 'get_burst_addresses') else [transaction.awaddr],
            'expected_beats': transaction.awlen + 1 if hasattr(transaction, 'awlen') else 1,
            'received_beats': 0,
            'complete': False
        }

        self.log.debug(f"Received write address: ID={id_value}, ADDR=0x{transaction.awaddr:X}, LEN={getattr(transaction, 'awlen', 0)}")

    def _handle_w_transaction(self, transaction):
        """Process Write Data (W) channel transaction"""
        # Match with pending write transactions
        for id_value, pending in self.pending_writes.items():
            # Check if this transaction belongs to this ID
            if pending['received_beats'] < pending['expected_beats']:
                # Get next expected address
                if pending['received_beats'] < len(pending['addresses']):
                    addr = pending['addresses'][pending['received_beats']]
                else:
                    # Should not happen, but handle gracefully
                    addr = pending['addresses'][-1]

                # Validate protocol if enabled
                if self.check_protocol:
                    valid, error_msg = transaction.validate_axi4_protocol()
                    if not valid:
                        self.log.error(f"AXI4 protocol error (W): {error_msg}")

                # Add this transaction to the pending write
                pending['w_transactions'].append(transaction)
                pending['received_beats'] += 1

                # Check if last beat
                if hasattr(transaction, 'wlast') and transaction.wlast == 1:
                    # Mark as complete and ready for processing
                    pending['complete'] = True

                # Check if all expected beats received
                if pending['received_beats'] >= pending['expected_beats']:
                    # Mark as complete and ready for processing
                    pending['complete'] = True

                self.log.debug(f"Received write data: ADDR=0x{addr:X}, DATA=0x{transaction.wdata:X}, STRB=0x{transaction.wstrb:X}, LAST={getattr(transaction, 'wlast', 0)}")

                # Found a match, no need to check other IDs
                break

    def _handle_ar_transaction(self, transaction):
        """Process Read Address (AR) channel transaction"""
        # Extract ID for tracking
        if not hasattr(transaction, 'arid'):
            self.log.error("AR transaction missing arid field")
            return

        id_value = transaction.arid

        # Validate protocol if enabled
        # if self.check_protocol:
        #     valid, error_msg = transaction.validate_axi4_protocol()
        #     if not valid:
        #         self.log.error(f"AXI4 protocol error (AR): {error_msg}")

        # Calculate all addresses in the burst
        addresses = transaction.get_burst_addresses() if hasattr(transaction, 'get_burst_addresses') else [transaction.araddr]

        # Store the transaction for processing
        self.pending_reads[id_value] = {
            'ar_transaction': transaction,
            'start_time': get_sim_time('ns'),
            'addresses': addresses,
            'expected_beats': transaction.arlen + 1 if hasattr(transaction, 'arlen') else 1,
            'processed': False
        }

        self.log.debug(f"Received read address: ID={id_value}, ADDR=0x{transaction.araddr:X}, LEN={getattr(transaction, 'arlen', 0)}")

    async def _transaction_processor(self):
        """Process pending transactions"""
        self.log.debug("AXI4 transaction processor started")

        while self.running:
            # Process write transactions
            await self._process_writes()

            # Process read transactions
            await self._process_reads()

            # Process write responses
            await self._send_write_responses()

            # Process read responses
            await self._send_read_responses()

            # Yield to allow other tasks to run
            await RisingEdge(self.clock)

        self.log.debug("AXI4 transaction processor stopped")

    async def _process_writes(self):
        """Process completed write transactions and queue responses"""

        for id_value, pending in self.pending_writes.items():
            if pending['complete'] and not pending.get('processed', False):
                # Process the write transaction

                # Get original transaction info
                aw_transaction = pending['aw_transaction']
                w_transactions = pending['w_transactions']

                # Check if all data received
                if len(w_transactions) < pending['expected_beats']:
                    self.log.warning(f"Write transaction ID={id_value} marked complete but missing data beats")
                    continue

                # Write to memory if available
                if self.memory_model:
                    for i, addr in enumerate(pending['addresses']):
                        if i < len(w_transactions):
                            data = w_transactions[i].wdata
                            strb = w_transactions[i].wstrb if hasattr(w_transactions[i], 'wstrb') else 0xFF

                            try:
                                # Convert data to bytearray
                                data_bytes = self.memory_model.integer_to_bytearray(data, self.memory_model.bytes_per_line)

                                # Write to memory
                                self.memory_model.write(addr, data_bytes, strb)
                                self.log.debug(f"Write to memory: addr=0x{addr:X}, data=0x{data:X}, strb=0x{strb:X}")
                            except Exception as e:
                                self.log.error(f"Error writing to memory: {e}")

                # Queue response for sending according to ordering rules
                b_packet = AXI4Packet.create_b_packet(
                    bid=id_value,
                    bresp=0,  # OKAY
                    buser=getattr(aw_transaction, 'awuser', 0)
                )

                # Add to response queue
                self.write_response_queue.append({
                    'id': id_value,
                    'packet': b_packet,
                    'timestamp': get_sim_time('ns'),
                    'addr': aw_transaction.awaddr  # For tracking/debugging
                })

                # If this is the first transaction and we're tracking in-order responses,
                # set it as the next to process
                if self.next_write_id is None:
                    self.next_write_id = id_value

                # Mark as processed
                pending['processed'] = True

                self.log.debug(f"Queued write response: ID={id_value}, RESP=0")

    async def _process_reads(self):
        """Process pending read transactions and queue responses"""

        for id_value, pending in self.pending_reads.items():
            if not pending.get('processed', False):
                # Process the read transaction

                # Get original transaction info
                ar_transaction = pending['ar_transaction']
                addresses = pending['addresses']
                expected_beats = pending['expected_beats']

                # For each address in the burst, queue a separate response beat
                for i, addr in enumerate(addresses):
                    if i >= expected_beats:
                        break

                    data = 0
                    resp = 0  # OKAY

                    # Read from memory if available
                    if self.memory_model:
                        try:
                            # Read from memory
                            data_bytes = self.memory_model.read(addr, self.memory_model.bytes_per_line)
                            data = self.memory_model.bytearray_to_integer(data_bytes)
                            self.log.debug(f"Read from memory: addr=0x{addr:X}, data=0x{data:X}")
                        except Exception as e:
                            self.log.error(f"Error reading from memory: {e}")
                            resp = 2  # SLVERR

                    # Create the response packet
                    r_packet = AXI4Packet.create_r_packet(
                        rid=id_value,
                        rdata=data,
                        rresp=resp,
                        rlast=1 if i == expected_beats - 1 else 0,
                        ruser=getattr(ar_transaction, 'aruser', 0)
                    )

                    # Add to response queue
                    self.read_response_queue.append({
                        'id': id_value,
                        'packet': r_packet,
                        'timestamp': get_sim_time('ns'),
                        'addr': addr,
                        'beat': i,
                        'last': i == expected_beats - 1
                    })

                    self.log.debug(f"Queued read data: ID={id_value}, ADDR=0x{addr:X}, DATA=0x{data:X}, " +
                                    f"RESP={resp}, LAST={1 if i == expected_beats - 1 else 0}")

                # If this is the first transaction and we're tracking in-order responses,
                # set it as the next to process
                if self.next_read_id is None:
                    self.next_read_id = id_value

                # Mark as processed
                pending['processed'] = True

                # For weighted OOO strategy, set default weight if not already set
                if self.ooo_strategy == 'weighted' and id_value not in self.ooo_weights:
                    self.ooo_weights[id_value] = 1.0  # Default weight

    async def _send_write_responses(self):
        """Send write responses according to ordering rules"""
        # If no queued responses, nothing to do
        if not self.write_response_queue:
            return

        # For in-order mode, we need to respect transaction order across all IDs
        if self.inorder:
            # Only send the next response if it matches the expected ID
            if self.next_write_id is not None:
                response_idx = next(
                    (
                        i
                        for i, resp in enumerate(self.write_response_queue)
                        if resp['id'] == self.next_write_id
                    ),
                    None,
                )
                if response_idx is not None:
                    # Send this response
                    response = self.write_response_queue.pop(response_idx)
                    await self.b_master.send(response['packet'])
                    self.log.debug(f"Sent in-order write response: ID={response['id']}, RESP=0")

                    # Remove from tracking
                    if self.next_write_id in self.pending_writes:
                        del self.pending_writes[self.next_write_id]

                    # Find next transaction ID
                    self.next_write_id = self._find_next_write_id()
        else:
            # For out-of-order mode, select response based on strategy
            response_idx = self._select_write_response()

            if response_idx is not None:
                # Send selected response
                response = self.write_response_queue.pop(response_idx)
                await self.b_master.send(response['packet'])
                self.log.debug(f"Sent out-of-order write response: ID={response['id']}, RESP=0")

                # Remove from tracking
                if response['id'] in self.pending_writes:
                    del self.pending_writes[response['id']]

                # Update next ID tracking if this was the next expected
                if self.next_write_id == response['id']:
                    self.next_write_id = self._find_next_write_id()

    async def _send_read_responses(self):
        """Send read responses according to ordering rules"""
        # If no queued responses, nothing to do
        if not self.read_response_queue:
            return

        # For both in-order and out-of-order mode, we must maintain ordering within each ID
        id_to_responses = {}

        # Group responses by ID
        for i, resp in enumerate(self.read_response_queue):
            id_value = resp['id']
            if id_value not in id_to_responses:
                id_to_responses[id_value] = []
            id_to_responses[id_value].append((i, resp))

        # Process each ID group separately
        if self.inorder:
            # For in-order mode, only process the next ID
            if self.next_read_id is not None and self.next_read_id in id_to_responses:
                await self._send_read_responses_for_id(self.next_read_id, id_to_responses[self.next_read_id])
        else:
            # For out-of-order mode, select an ID based on strategy
            selected_id = self._select_read_id(id_to_responses)

            if selected_id is not None:
                await self._send_read_responses_for_id(selected_id, id_to_responses[selected_id])

    async def _send_read_responses_for_id(self, id_value, responses):
        """Send a single response beat for the specified ID"""
        # For read responses, we must send them in order by beat number
        # Sort responses by beat number
        responses.sort(key=lambda x: x[1]['beat'])

        # Take just the first one to process
        idx, response = responses[0]

        # Remove from queue
        self.read_response_queue.pop(idx)

        # Send the response
        await self.r_master.send(response['packet'])
        self.log.debug(f"Sent read response: ID={id_value}, ADDR=0x{response['addr']:X}, " +
                        f"BEAT={response['beat']}, LAST={response['last']}")

        # If this was the last beat for this transaction, clean up
        if response['last']:
            # Remove from tracking
            if id_value in self.pending_reads:
                del self.pending_reads[id_value]

            # If this was the next expected ID, find the new next ID
            if self.next_read_id == id_value:
                self.next_read_id = self._find_next_read_id()

    def _find_next_write_id(self):
        """Find the next write ID to process"""
        if not self.pending_writes:
            return None

        # Find the oldest pending write
        oldest_time = float('inf')
        oldest_id = None

        for id_value, pending in self.pending_writes.items():
            if pending.get('start_time', float('inf')) < oldest_time:
                oldest_time = pending['start_time']
                oldest_id = id_value

        return oldest_id

    def _find_next_read_id(self):
        """Find the next read ID to process"""
        if not self.pending_reads:
            return None

        # Find the oldest pending read
        oldest_time = float('inf')
        oldest_id = None

        for id_value, pending in self.pending_reads.items():
            if pending.get('start_time', float('inf')) < oldest_time:
                oldest_time = pending['start_time']
                oldest_id = id_value

        return oldest_id

    def _select_write_response(self):
        """Select a write response to send based on the out-of-order strategy"""
        if not self.write_response_queue:
            return None

        if self.ooo_strategy == 'random':
            # Random selection
            return random.randint(0, len(self.write_response_queue) - 1)

        elif self.ooo_strategy == 'round_robin':
            # Round robin - just take the first one
            return 0

        elif self.ooo_strategy == 'weighted':
            # Weighted random selection
            # Calculate weights for each response
            weights = []
            for resp in self.write_response_queue:
                id_value = resp['id']
                # Default weight is 1.0 if not specified
                weight = self.ooo_weights.get(id_value, 1.0)
                weights.append(weight)

            # Select based on weights
            if sum(weights) > 0:
                return random.choices(range(len(self.write_response_queue)), weights=weights)[0]
            else:
                return 0

        # Default to first response
        return 0

    def _select_read_id(self, id_to_responses):
        """Select a read ID to process based on the out-of-order strategy"""
        if not id_to_responses:
            return None

        ids = list(id_to_responses.keys())

        if self.ooo_strategy == 'random':
            # Random selection
            return random.choice(ids)

        elif self.ooo_strategy == 'round_robin':
            # Round robin - just take the first one
            return ids[0]

        elif self.ooo_strategy == 'weighted':
            # Weighted random selection
            # Calculate weights for each ID
            weights = []
            for id_value in ids:
                # Default weight is 1.0 if not specified
                weight = self.ooo_weights.get(id_value, 1.0)
                weights.append(weight)

            # Select based on weights
            return random.choices(ids, weights=weights)[0] if sum(weights) > 0 else ids[0]
        # Default to first ID
        return ids[0]

    def set_ooo_weight(self, id_value, weight):
        """
        Set the weight for a specific ID in weighted out-of-order strategy.

        Args:
            id_value: Transaction ID
            weight: Weight value (higher values increase selection probability)
        """
        self.ooo_weights[id_value] = weight
