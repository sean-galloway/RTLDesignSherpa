"""
AXI4 Slave Component for Verification

This module provides the AXI4Slave class for AXI4 slave interfaces with
integrated protocol extensions and sequence support.
"""

import cocotb
import random
from collections import deque
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from ..gaxi.gaxi_factories import create_gaxi_master, create_gaxi_slave
from ..flex_randomizer import FlexRandomizer

from .axi4_fields_signals import (
    AXI4_SLAVE_DEFAULT_CONSTRAINTS,
    get_aw_signal_map,
    get_w_signal_map,
    get_b_signal_map,
    get_ar_signal_map,
    get_r_signal_map
)
from .axi4_packet import AXI4Packet
from .axi4_extensions import create_axi4_extension_handlers


class AXI4Slave:
    """
    AXI4 Slave component that manages multiple channels for AXI4 transactions.

    This class provides:
    - Separate GAXI slaves for each AXI4 channel (AW, W, B, AR, R)
    - Memory model for handling read/write operations
    - AXI4 protocol checking
    - Response ordering control (in-order or out-of-order between different IDs)
    - Protocol extensions (QoS, exclusive access, atomic operations, barriers)
    """

    def __init__(self, dut, title, prefix, divider, suffix, clock, channels,
                id_width=8, addr_width=32, data_width=32, user_width=1,
                field_configs=None, memory_model=None, randomizers=None, check_protocol=False,
                inorder=False, ooo_strategy='random', extensions=None, log=None):
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
            field_configs: Dictionary of field configurations for each channel
            memory_model: Memory model for data storage
            randomizers: Dict of randomizers for each channel (keys: 'b', 'r')
            check_protocol: Enable AXI4 protocol checking (default: True)
            inorder: If True, force in-order responses across different IDs (default: False)
            ooo_strategy: Strategy for out-of-order responses ('random', 'round_robin', 'weighted')
            extensions: Dictionary of extension handlers (optional)
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

        # Store width parameters
        self.id_width = id_width
        self.addr_width = addr_width
        self.data_width = data_width
        self.user_width = user_width

        # Calculate strobe width
        self.strb_width = data_width // 8

        # Store field configs
        self.field_configs = field_configs

        # Ensure we have proper field configs for each channel
        if not self.field_configs:
            raise ValueError(f"AXI4Slave '{title}' requires field configs for each channel")

        # Extract field configs for each channel
        self.aw_field_config = self.field_configs.get('AW')
        self.w_field_config = self.field_configs.get('W')
        self.b_field_config = self.field_configs.get('B')
        self.ar_field_config = self.field_configs.get('AR')
        self.r_field_config = self.field_configs.get('R')

        # Prepare signal mappings
        aw_signal_map, aw_optional_signal_map = get_aw_signal_map(prefix, divider, suffix)
        w_signal_map, w_optional_signal_map = get_w_signal_map(prefix, divider, suffix)
        b_signal_map, b_optional_signal_map = get_b_signal_map(prefix, divider, suffix)
        ar_signal_map, ar_optional_signal_map = get_ar_signal_map(prefix, divider, suffix)
        r_signal_map, r_optional_signal_map = get_r_signal_map(prefix, divider, suffix)

        # Get randomizers
        randomizers = randomizers or {}
        b_randomizer = randomizers.get('b', FlexRandomizer(AXI4_SLAVE_DEFAULT_CONSTRAINTS))
        r_randomizer = randomizers.get('r', FlexRandomizer(AXI4_SLAVE_DEFAULT_CONSTRAINTS))

        # Create channel components
        if 'AW' in self.channels and self.aw_field_config:
            self.aw_slave = create_gaxi_slave(
                dut, f"{title}_AW", "", clock,
                field_config=self.aw_field_config,
                packet_class=AXI4Packet,
                multi_sig=True,
                signal_map=aw_signal_map,
                optional_signal_map=aw_optional_signal_map,
                log=log
            )
            self.aw_slave.add_callback(self._handle_aw_transaction)
        else:
            self.aw_slave = None

        if 'W' in self.channels and self.w_field_config:
            self.w_slave = create_gaxi_slave(
                dut, f"{title}_W", "", clock,
                field_config=self.w_field_config,
                packet_class=AXI4Packet,
                multi_sig=True,
                signal_map=w_signal_map,
                optional_signal_map=w_optional_signal_map,
                log=log
            )
            self.w_slave.add_callback(self._handle_w_transaction)
        else:
            self.w_slave = None

        if 'B' in self.channels and self.b_field_config:
            self.b_master = create_gaxi_master(
                dut, f"{title}_B", "", clock,
                field_config=self.b_field_config,
                packet_class=AXI4Packet,
                randomizer=b_randomizer,
                multi_sig=True,
                signal_map=b_signal_map,
                optional_signal_map=b_optional_signal_map,
                log=log
            )
        else:
            self.b_master = None

        if 'AR' in self.channels and self.ar_field_config:
            self.ar_slave = create_gaxi_slave(
                dut, f"{title}_AR", "", clock,
                field_config=self.ar_field_config,
                packet_class=AXI4Packet,
                multi_sig=True,
                signal_map=ar_signal_map,
                optional_signal_map=ar_optional_signal_map,
                log=log
            )
            self.ar_slave.add_callback(self._handle_ar_transaction)
        else:
            self.ar_slave = None

        if 'R' in self.channels and self.r_field_config:
            self.r_master = create_gaxi_master(
                dut, f"{title}_R", "", clock,
                field_config=self.r_field_config,
                packet_class=AXI4Packet,
                randomizer=r_randomizer,
                multi_sig=True,
                signal_map=r_signal_map,
                optional_signal_map=r_optional_signal_map,
                log=log
            )
        else:
            self.r_master = None

        # Initialize extensions
        self.extensions = extensions or {}

        # Create standard extension handlers if none provided and memory model is available
        if not self.extensions and self.memory_model:
            self.extensions = create_axi4_extension_handlers(self.memory_model, self.log)

        # Slave ID - used for exclusive access tracking
        self.slave_id = id(self)

        # Initialize transaction tracking
        self.pending_writes = {}  # Write address transactions waiting for data
        self.pending_reads = {}   # Read transactions waiting to be processed

        # Queue structure for ordering responses
        self.write_response_queue = []  # Queue of write responses to send
        self.read_response_queue = []   # Queue of read responses to send

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
        if 'AW' in self.channels and self.aw_slave:
            await self.aw_slave.reset_bus()
        if 'W' in self.channels and self.w_slave:
            await self.w_slave.reset_bus()
        if 'B' in self.channels and self.b_master:
            await self.b_master.reset_bus()
        if 'AR' in self.channels and self.ar_slave:
            await self.ar_slave.reset_bus()
        if 'R' in self.channels and self.r_master:
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
        address = transaction.awaddr

        # Log detailed information
        self.log.debug(f"Received write address: ID={id_value}, ADDR=0x{address:X}, LEN={getattr(transaction, 'awlen', 0)}")

        # Validate protocol if enabled
        if self.check_protocol:
            valid, error_msg = transaction.validate_axi4_protocol()
            if not valid:
                self.log.error(f"AXI4 protocol error (AW): {error_msg}")
                # Still process the transaction, but note the error

        # Handle exclusive access if applicable
        is_exclusive = bool(hasattr(transaction, 'awlock') and transaction.awlock == 1)

        # Handle QoS if applicable
        qos_value = 0
        if hasattr(transaction, 'awqos'):
            qos_value = transaction.awqos

            # Apply QoS handling if available
            if 'qos' in self.extensions and qos_value > 0:
                # Add to QoS prioritization
                self.extensions['qos'].queue_write_transaction(
                    {'id': id_value, 'transaction': transaction},
                    qos_value
                )

        # Calculate burst addresses for memory access
        addresses = transaction.get_burst_addresses() if hasattr(transaction, 'get_burst_addresses') else [transaction.awaddr]

        # Store the transaction for matching with write data
        self.pending_writes[id_value] = {
            'aw_transaction': transaction,
            'w_transactions': [],
            'start_time': get_sim_time('ns'),
            'addresses': addresses,
            'expected_beats': transaction.awlen + 1 if hasattr(transaction, 'awlen') else 1,
            'received_beats': 0,
            'complete': False,
            'is_exclusive': is_exclusive,
            'qos': qos_value
        }

        # Check for barrier dependencies
        if 'barrier' in self.extensions:
            # Check if this transaction is allowed to proceed
            allowed = self.extensions['barrier'].is_transaction_allowed(id_value)
            if not allowed:
                # Transaction must wait for barriers
                self.pending_writes[id_value]['barrier_blocked'] = True

        # IMPORTANT: Check if we have any stored W data that might belong to this transaction
        # This handles the case where W data arrives before or simultaneously with AW
        if hasattr(self, 'pending_w_data') and self.pending_w_data:
            self.log.debug(f"Checking {len(self.pending_w_data)} pending W transactions for ID={id_value}")
            pending = self.pending_writes[id_value]

            # Check each stored W transaction
            i = 0
            while i < len(self.pending_w_data) and pending['received_beats'] < pending['expected_beats']:
                w_transaction = self.pending_w_data[i]

                # Add this transaction to the pending write
                pending['w_transactions'].append(w_transaction)
                pending['received_beats'] += 1

                # Check if this completes the transaction
                is_last = hasattr(w_transaction, 'wlast') and w_transaction.wlast == 1
                expected_last = pending['received_beats'] >= pending['expected_beats']

                if is_last or expected_last:
                    pending['complete'] = True
                    self.log.debug(f"Transaction ID={id_value} now complete using stored W data, received all {pending['received_beats']} beats")

                # Get the address for this beat
                addr = pending['addresses'][pending['received_beats']-1] if pending['received_beats'] <= len(pending['addresses']) else pending['addresses'][-1]

                self.log.debug(f"Matched stored W data with new AW transaction: ID={id_value}, ADDR=0x{addr:X}, DATA=0x{w_transaction.wdata:X}, beat #{pending['received_beats']}")

                # Remove this W transaction from the buffer
                self.pending_w_data.pop(i)

                # Don't increment i since we removed an item
                # Next iteration will use the new item at index i

    def _handle_w_transaction(self, transaction):
        """Process Write Data (W) channel transaction"""
        # W transactions don't carry ID, so we need to match them with AW transactions

        # Detailed debugging for incoming transaction
        w_data = transaction.wdata if hasattr(transaction, 'wdata') else 'unknown'
        w_strb = transaction.wstrb if hasattr(transaction, 'wstrb') else 'unknown'
        w_last = transaction.wlast if hasattr(transaction, 'wlast') else 'unknown'
        self.log.debug(f"Incoming W transaction: DATA=0x{w_data:X}, STRB=0x{w_strb:X}, LAST={w_last}")

        # Log the current state of pending writes
        if self.pending_writes:
            self.log.debug(f"Current pending writes: {len(self.pending_writes)} transactions")
            for id_val, pending in self.pending_writes.items():
                aw_addr = pending['aw_transaction'].awaddr if 'aw_transaction' in pending else 'unknown'
                received = pending.get('received_beats', 0)
                expected = pending.get('expected_beats', 0)
                self.log.debug(f"  ID={id_val}, ADDR=0x{aw_addr:X}, received={received}/{expected} beats, complete={pending.get('complete', False)}")

        # Track if we found a match
        found_match = False

        # SCENARIO 1: Look for in-progress transactions first
        for id_value, pending in self.pending_writes.items():
            if pending.get('complete', False):
                continue  # Skip complete transactions

            if pending.get('received_beats', 0) > 0:
                # This transaction already has some data, try to match this beat with it
                if pending['received_beats'] < pending['expected_beats']:
                    # Get next expected address
                    addr = pending['addresses'][pending['received_beats']] if pending['received_beats'] < len(pending['addresses']) else pending['addresses'][-1]

                    # Add this transaction to the pending write
                    pending['w_transactions'].append(transaction)
                    pending['received_beats'] += 1

                    # Check if this completes the transaction
                    is_last = hasattr(transaction, 'wlast') and transaction.wlast == 1
                    expected_last = pending['received_beats'] >= pending['expected_beats']

                    if is_last or expected_last:
                        pending['complete'] = True
                        self.log.debug(f"In-progress transaction ID={id_value} now complete, received all {pending['received_beats']} beats")

                    self.log.debug(f"Matched write data with in-progress transaction: ID={id_value}, ADDR=0x{addr:X}, DATA=0x{w_data:X}, beat #{pending['received_beats']}")
                    found_match = True
                    break

        # SCENARIO 2: If no match with in-progress transactions, try to match with a new transaction
        if not found_match:
            # Create a list of pending writes that need data, sorted by start time (oldest first)
            pending_needing_data = []

            for id_value, pending in self.pending_writes.items():
                if not pending.get('complete', False) and pending.get('received_beats', 0) < pending.get('expected_beats', 1):
                    pending_needing_data.append((id_value, pending.get('start_time', float('inf'))))

            # Sort by start time
            pending_needing_data.sort(key=lambda x: x[1])

            # Try to match with the oldest transaction that needs data
            if pending_needing_data:
                oldest_id = pending_needing_data[0][0]
                pending = self.pending_writes[oldest_id]

                # Get next expected address
                addr = pending['addresses'][pending['received_beats']] if pending['received_beats'] < len(pending['addresses']) else pending['addresses'][-1]

                # Add this transaction to the pending write
                pending['w_transactions'].append(transaction)
                pending['received_beats'] += 1

                # Check if this completes the transaction
                is_last = hasattr(transaction, 'wlast') and transaction.wlast == 1
                expected_last = pending['received_beats'] >= pending['expected_beats']

                if is_last or expected_last:
                    pending['complete'] = True
                    self.log.debug(f"New transaction ID={oldest_id} now complete, received all {pending['received_beats']} beats")

                self.log.debug(f"Matched write data with oldest pending transaction: ID={oldest_id}, ADDR=0x{addr:X}, DATA=0x{w_data:X}, beat #{pending['received_beats']}")
                found_match = True

        # SCENARIO 3: Store the data temporarily if no AW transaction has arrived yet
        # This handles the case where W data arrives before or simultaneously with AW
        if not found_match:
            # Store in a temporary buffer keyed by data value as we don't have ID info
            if not hasattr(self, 'pending_w_data'):
                self.pending_w_data = []

            self.pending_w_data.append(transaction)
            self.log.debug(f"No matching AW transaction found yet. Storing W data (0x{w_data:X}) for later matching. Buffer size: {len(self.pending_w_data)}")

    def _handle_ar_transaction(self, transaction):
        """Process Read Address (AR) channel transaction"""
        # Extract ID for tracking
        if not hasattr(transaction, 'arid'):
            self.log.error("AR transaction missing arid field")
            return

        id_value = transaction.arid

        # Validate protocol if enabled
        if self.check_protocol:
            valid, error_msg = transaction.validate_axi4_protocol()
            if not valid:
                self.log.error(f"AXI4 protocol error (AR): {error_msg}")

        # Check for exclusive access
        is_exclusive = False
        if hasattr(transaction, 'arlock') and transaction.arlock == 1:
            is_exclusive = True

            # Handle exclusive read in the extensions
            if 'exclusive' in self.extensions:
                # Register exclusive monitor
                addr = transaction.araddr
                size = 1 << transaction.arsize if hasattr(transaction, 'arsize') else 4
                self.extensions['exclusive'].handle_exclusive_read(
                    id_value, self.slave_id, addr, size
                )

        # Use QoS if enabled
        qos_value = 0
        if hasattr(transaction, 'arqos'):
            qos_value = transaction.arqos

            # Apply QoS handling if available
            if 'qos' in self.extensions and qos_value > 0:
                # Add to QoS prioritization
                self.extensions['qos'].queue_read_transaction(
                    {'id': id_value, 'transaction': transaction},
                    qos_value
                )

        # Calculate all addresses in the burst
        addresses = transaction.get_burst_addresses() if hasattr(transaction, 'get_burst_addresses') else [transaction.araddr]

        # Store the transaction for processing
        self.pending_reads[id_value] = {
            'ar_transaction': transaction,
            'start_time': get_sim_time('ns'),
            'addresses': addresses,
            'expected_beats': transaction.arlen + 1 if hasattr(transaction, 'arlen') else 1,
            'is_exclusive': is_exclusive,
            'qos': qos_value,
            'processed': False
        }

        # Check for barrier dependencies
        if 'barrier' in self.extensions:
            # Check if this transaction is allowed to proceed
            allowed = self.extensions['barrier'].is_transaction_allowed(id_value)
            if not allowed:
                # Transaction must wait for barriers
                self.pending_reads[id_value]['barrier_blocked'] = True

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
        # Skip if no pending writes
        if not self.pending_writes:
            return

        # Check for any pending W data that hasn't been matched yet
        if hasattr(self, 'pending_w_data') and self.pending_w_data and len(self.pending_w_data) > 5:
            self.log.warning(f"Large number of unmatched W transactions: {len(self.pending_w_data)}")

        if pending_complete := [
            id_val
            for id_val, pending in self.pending_writes.items()
            if pending.get('complete', False)
            and not pending.get('processed', False)
        ]:
            self.log.debug(f"Processing writes: {len(pending_complete)} complete transactions waiting to be processed: {pending_complete}")

        # First, check QoS handler if available
        next_qos_transaction = None
        if 'qos' in self.extensions:
            if next_qos_transaction := self.extensions[
                'qos'
            ].get_next_write_transaction():
                # Process this high-priority transaction first
                id_value = next_qos_transaction['id']
                if id_value in self.pending_writes and self.pending_writes[id_value]['complete'] and not self.pending_writes[id_value].get('processed', False):
                    # Force processing of this ID next
                    self.log.debug(f"Processing high-priority QoS transaction ID={id_value}")
                    await self._process_write_id(id_value)
                    return

        # Create a list of IDs that are complete but not processed
        complete_ids = []
        for id_value, pending in self.pending_writes.items():
            if pending.get('complete', False) and not pending.get('processed', False):
                # Skip if barrier blocked
                if pending.get('barrier_blocked', False):
                    self.log.debug(f"Transaction ID={id_value} is complete but barrier blocked")
                    continue

                # Add to the list of processable transactions
                complete_ids.append((id_value, pending.get('start_time', float('inf'))))

        # Sort transactions by start time to process oldest first
        if complete_ids:
            complete_ids.sort(key=lambda x: x[1])
            id_to_process = complete_ids[0][0]

            # Log transaction details
            pending = self.pending_writes[id_to_process]
            self.log.debug(f"Processing oldest complete transaction ID={id_to_process}, ADDR=0x{pending['aw_transaction'].awaddr:X}")

            # Double-check that data is actually available
            if len(pending.get('w_transactions', [])) < pending.get('expected_beats', 1):
                self.log.warning(f"Transaction ID={id_to_process} is marked complete but has {len(pending.get('w_transactions', []))}/{pending.get('expected_beats', 1)} beats")
                # Mark as incomplete to prevent processing
                pending['complete'] = False
                return

            await self._process_write_id(id_to_process)

    async def _process_write_id(self, id_value):
        """Process a specific write transaction by ID"""
        if id_value not in self.pending_writes:
            self.log.error(f"Attempted to process non-existent write ID={id_value}")
            return

        pending = self.pending_writes[id_value]

        # Check if transaction is really complete
        if not pending.get('complete', False):
            self.log.warning(f"Attempted to process incomplete write transaction ID={id_value}")
            return

        # Check if transaction is already processed
        if pending.get('processed', False):
            self.log.warning(f"Attempted to process already processed write transaction ID={id_value}")
            return

        # Get original transaction info
        aw_transaction = pending['aw_transaction']
        w_transactions = pending['w_transactions']

        # Double-check that all data was received
        if len(w_transactions) < pending['expected_beats']:
            self.log.warning(f"Write transaction ID={id_value} marked complete but missing data beats: {len(w_transactions)}/{pending['expected_beats']}")
            # Do not process incomplete transactions
            return

        # Log details for debugging
        self.log.debug(f"Processing write transaction ID={id_value}, ADDR=0x{aw_transaction.awaddr:X}, expected_beats={pending['expected_beats']}, received_beats={pending['received_beats']}")

        # Check with error handler if available
        should_error = False
        error_resp = 0  # Default OKAY
        if 'error_handler' in self.extensions:
            should_error, error_resp = self.extensions['error_handler'].check_for_error(
                aw_transaction.awaddr, id_value
            )

        # If error handler indicates an error, use that response
        if should_error:
            resp_code = error_resp
            self.log.debug(f"Error handler triggered for write ID={id_value}, ADDR=0x{aw_transaction.awaddr:X}, RESP={resp_code}")
        else:
            # Handle exclusive write if applicable
            if pending.get('is_exclusive', False) and 'exclusive' in self.extensions:
                addr = aw_transaction.awaddr
                size = 1 << aw_transaction.awsize if hasattr(aw_transaction, 'awsize') else 4
                exclusive_success = self.extensions['exclusive'].handle_exclusive_write(
                    id_value, self.slave_id, addr, size
                )

                # Determine response code based on exclusive success
                resp_code = 1 if exclusive_success else 0  # 1=EXOKAY, 0=OKAY
            else:
                # Normal write, use OKAY response
                resp_code = 0

            # Write to memory if available and not an error
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
                            resp_code = 2  # SLVERR

        # Queue response for sending according to ordering rules
        b_packet = AXI4Packet.create_b_packet(
            bid=id_value,
            bresp=resp_code,
            buser=getattr(aw_transaction, 'awuser', 0)
        )

        # Add to response queue with detailed information for debugging
        response_entry = {
            'id': id_value,
            'packet': b_packet,
            'timestamp': get_sim_time('ns'),
            'addr': aw_transaction.awaddr,  # For tracking/debugging
            'exclusive': pending.get('is_exclusive', False),
            'qos': pending.get('qos', 0)
        }

        self.write_response_queue.append(response_entry)
        self.log.debug(f"Queued write response: ID={id_value}, RESP={resp_code}, ADDR=0x{aw_transaction.awaddr:X}")

        # If this is the first transaction and we're tracking in-order responses,
        # set it as the next to process
        if self.next_write_id is None:
            self.next_write_id = id_value
            self.log.debug(f"Setting next_write_id={id_value} (was None)")

        # Mark as processed - important for tracking
        pending['processed'] = True

        # Update barrier handler if applicable
        if 'barrier' in self.extensions:
            self.extensions['barrier'].complete_transaction(id_value)

        # Detailed debug log for response queuing
        self.log.debug(f"Write transaction ID={id_value} processed successfully, response queued")

    async def _process_reads(self):
        """Process pending read transactions and queue responses"""
        # First, check QoS handler if available
        next_qos_transaction = None
        if 'qos' in self.extensions:
            if next_qos_transaction := self.extensions[
                'qos'
            ].get_next_read_transaction():
                # Process this high-priority transaction first
                id_value = next_qos_transaction['id']
                if id_value in self.pending_reads and not self.pending_reads[id_value].get('processed', False):
                    # Force processing of this ID next
                    await self._process_read_id(id_value)
                    return

        # Process regular transactions
        for id_value, pending in self.pending_reads.items():
            if not pending.get('processed', False):
                # Check if this transaction is blocked by a barrier
                if pending.get('barrier_blocked', False):
                    # Skip this transaction until barrier is resolved
                    continue

                # Process this read transaction
                await self._process_read_id(id_value)
                # Only process one transaction per cycle to avoid overwhelming
                return

    async def _process_read_id(self, id_value):
        """Process a specific read transaction by ID"""
        if id_value not in self.pending_reads:
            return
        pending = self.pending_reads[id_value]

        # Debug
        self.log.debug(f"Processing read ID={id_value}, addresses={[hex(a) for a in pending['addresses']]}")

        # Get original transaction info
        ar_transaction = pending['ar_transaction']
        addresses = pending['addresses']
        expected_beats = pending['expected_beats']

        # For each address in the burst, queue a separate response beat
        for i, addr in enumerate(addresses):
            if i >= expected_beats:
                break

            # Check with error handler if available
            should_error = False
            error_resp = 0  # Default OKAY
            if 'error_handler' in self.extensions:
                should_error, error_resp = self.extensions['error_handler'].check_for_error(
                    addr, id_value
                )

            # If error handler indicates an error, use that response
            if should_error:
                resp = error_resp
                data = 0  # For errors, data is typically undefined
                self.log.debug(f"Error handler triggered for read ID={id_value}, ADDR=0x{addr:X}, RESP={resp}")
            else:
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

                # Handle atomic operations if applicable
                if 'atomic' in self.extensions and hasattr(ar_transaction, 'aratomic') and ar_transaction.aratomic:
                    # Extract atomic operation type if available
                    op_type = getattr(ar_transaction, 'aratomicop', 0)
                    value = getattr(ar_transaction, 'aratomicvalue', 0)
                    compare_value = getattr(ar_transaction, 'aratomiccompare', None)

                    # Perform atomic operation
                    success, old_value = self.extensions['atomic'].perform_atomic_operation(
                        op_type, addr, value, compare_value
                    )

                    # Use old_value as data if successful
                    if success:
                        data = old_value
                    else:
                        resp = 2  # SLVERR on failure

            # Create the response packet
            r_packet = AXI4Packet.create_r_packet(
                rid=id_value,
                rdata=data,
                rresp=resp,
                rlast=1 if i == expected_beats - 1 else 0,
                ruser=getattr(ar_transaction, 'aruser', 0)
            )

            # Debug - log packet creation
            self.log.debug(f"Created response packet for ID={id_value}, addr=0x{addr:X}, beat={i}, data=0x{data:X}, last={1 if i == expected_beats - 1 else 0}")

            # Add to response queue
            self.read_response_queue.append({
                'id': id_value,
                'packet': r_packet,
                'timestamp': get_sim_time('ns'),
                'addr': addr,
                'beat': i,
                'last': i == expected_beats - 1,
                'exclusive': pending.get('is_exclusive', False),
                'qos': pending.get('qos', 0)
            })

            self.log.debug(f"Queued read data: ID={id_value}, ADDR=0x{addr:X}, DATA=0x{data:X}, " +
                            f"RESP={resp}, LAST={1 if i == expected_beats - 1 else 0}")

        # If this is the first transaction and we're tracking in-order responses,
        # set it as the next to process
        if self.next_read_id is None:
            self.next_read_id = id_value
            self.log.debug(f"Setting next_read_id={id_value} (was None)")

        # Mark as processed
        pending['processed'] = True

        # Update barrier handler if applicable
        if 'barrier' in self.extensions:
            # Only complete if all responses are sent, which hasn't happened yet
            # We'll mark it for completion after the last response
            pending['barrier_complete_pending'] = True

    async def _send_write_responses(self):
        """Send write responses according to ordering rules"""
        # If no queued responses, nothing to do
        if not self.write_response_queue:
            return

        id_list = [resp['id'] for resp in self.write_response_queue]
        self.log.debug(f"Write response queue state: {len(self.write_response_queue)} responses for IDs {id_list}, next_write_id={self.next_write_id}")

        # Check if the B channel master is busy
        if hasattr(self.b_master, 'transfer_busy') and self.b_master.transfer_busy:
            self.log.debug("B-channel master is busy, deferring response send")
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
                    # Get the response but don't pop it yet - wait for successful send
                    response = self.write_response_queue[response_idx]

                    try:
                        # Send this response with minimal delay
                        # This addresses the issue of the long delay between W and B
                        if hasattr(self.b_master, 'set_randomizer'):
                            # Store the original randomizer to restore later
                            original_randomizer = self.b_master.get_randomizer()

                            # Set a minimal delay (fixed 2 cycles) for this response
                            from ..flex_randomizer import FlexRandomizer
                            fixed_delay = {
                                'valid_delay': ([[2, 2]], [1.0])  # Always wait exactly 2 cycles
                            }
                            self.b_master.set_randomizer(FlexRandomizer(fixed_delay))

                        # Send the response
                        self.log.debug(f"Sending in-order write response: ID={response['id']}, RESP={response['packet'].bresp}, ADDR=0x{response['addr']:X}")
                        await self.b_master.send(response['packet'])

                        # Restore original randomizer if we changed it
                        if hasattr(self.b_master, 'set_randomizer') and original_randomizer:
                            self.b_master.set_randomizer(original_randomizer)

                        # Now remove it after successful send
                        self.write_response_queue.pop(response_idx)

                        # Log detailed successful send
                        self.log.debug(f"Sent in-order write response: ID={response['id']}, RESP={response['packet'].bresp}")

                        # Remove from tracking
                        if self.next_write_id in self.pending_writes:
                            del self.pending_writes[self.next_write_id]

                        # Find next transaction ID
                        old_next = self.next_write_id
                        self.next_write_id = self._find_next_write_id()
                        self.log.debug(f"Updated next_write_id from {old_next} to {self.next_write_id}")

                    except Exception as e:
                        # Log failure but don't remove from queue - will retry
                        self.log.error(f"Failed to send write response for ID={response['id']}: {str(e)}")

                        # Restore original randomizer if we changed it
                        if hasattr(self.b_master, 'set_randomizer') and original_randomizer:
                            self.b_master.set_randomizer(original_randomizer)
        else:
            # For out-of-order mode, select response based on strategy
            response_idx = self._select_write_response()

            if response_idx is not None:
                # Get the response but don't pop it yet
                response = self.write_response_queue[response_idx]

                try:
                    # Set minimal delay for B-channel response
                    if hasattr(self.b_master, 'set_randomizer'):
                        # Store the original randomizer to restore later
                        original_randomizer = self.b_master.get_randomizer()

                        # Set a minimal delay (fixed 2 cycles) for this response
                        from ..flex_randomizer import FlexRandomizer
                        fixed_delay = {
                            'valid_delay': ([[2, 2]], [1.0])  # Always wait exactly 2 cycles
                        }
                        self.b_master.set_randomizer(FlexRandomizer(fixed_delay))

                    # Send selected response
                    self.log.debug(f"Sending out-of-order write response: ID={response['id']}, RESP={response['packet'].bresp}, ADDR=0x{response['addr']:X}")
                    await self.b_master.send(response['packet'])

                    # Restore original randomizer if we changed it
                    if hasattr(self.b_master, 'set_randomizer') and original_randomizer:
                        self.b_master.set_randomizer(original_randomizer)

                    # Now remove it after successful send
                    self.write_response_queue.pop(response_idx)

                    # Log successful send
                    self.log.debug(f"Sent out-of-order write response: ID={response['id']}, RESP={response['packet'].bresp}")

                    # Remove from tracking
                    if response['id'] in self.pending_writes:
                        del self.pending_writes[response['id']]

                    # Update next ID tracking if this was the next expected
                    if self.next_write_id == response['id']:
                        old_next = self.next_write_id
                        self.next_write_id = self._find_next_write_id()
                        self.log.debug(f"Updated next_write_id from {old_next} to {self.next_write_id}")

                except Exception as e:
                    # Log failure but don't remove from queue - will retry
                    self.log.error(f"Failed to send write response for ID={response['id']}: {str(e)}")

                    # Restore original randomizer if we changed it
                    if hasattr(self.b_master, 'set_randomizer') and original_randomizer:
                        self.b_master.set_randomizer(original_randomizer)

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

        # Debug - log the start of response processing
        if id_to_responses:
            self.log.debug(f"Starting response processing, inorder={self.inorder}, next_read_id={self.next_read_id}")
            self.log.debug(f"IDs in queue: {list(id_to_responses.keys())}")

        # Process each ID group separately
        if self.inorder:
            # For in-order mode, only process the next ID
            if self.next_read_id is not None and self.next_read_id in id_to_responses:
                self.log.debug(f"Processing in-order response for ID={self.next_read_id}")
                await self._send_read_responses_for_id(self.next_read_id, id_to_responses[self.next_read_id])
            elif self.next_read_id is not None:
                self.log.debug(f"next_read_id={self.next_read_id} not in response queue, IDs available: {list(id_to_responses.keys())}")
            else:
                self.log.debug(f"next_read_id is None, but response queue has IDs: {list(id_to_responses.keys())}")
                # We have responses but no next_read_id, attempt to set it
                self.next_read_id = self._find_next_read_id()
                self.log.debug(f"Resetting next_read_id to {self.next_read_id}")
        else:
            # For out-of-order mode, select an ID based on strategy
            selected_id = self._select_read_id(id_to_responses)

            if selected_id is not None:
                self.log.debug(f"Processing out-of-order response for ID={selected_id}")
                await self._send_read_responses_for_id(selected_id, id_to_responses[selected_id])

    async def _send_read_responses_for_id(self, id_value, responses):
        """Send a single response beat for the specified ID"""
        # For read responses, we must send them in order by beat number
        # Sort responses by beat number
        responses.sort(key=lambda x: x[1]['beat'])

        # Take just the first one to process
        idx, response = responses[0]

        # Debug - log what we're about to do
        self.log.debug(f"Sending response: ID={id_value}, ADDR=0x{response['addr']:X}, " +
                    f"BEAT={response['beat']}, LAST={response['last']}, DATA=0x{response['packet'].rdata:X}")

        # Remove from queue
        self.read_response_queue.pop(idx)

        # Send the response
        await self.r_master.send(response['packet'])
        self.log.debug(f"Sent read response: ID={id_value}, ADDR=0x{response['addr']:X}, " +
                        f"BEAT={response['beat']}, LAST={response['last']}")

        # If this was the last beat for this transaction, clean up
        if response['last']:
            # Complete barrier if pending
            if id_value in self.pending_reads and self.pending_reads[id_value].get('barrier_complete_pending', False) and 'barrier' in self.extensions:
                self.extensions['barrier'].complete_transaction(id_value)

            # Remove from tracking
            if id_value in self.pending_reads:
                self.log.debug(f"Deleting completed transaction ID={id_value} from pending_reads")
                del self.pending_reads[id_value]

            # If this was the next expected ID, find the new next ID
            if self.next_read_id == id_value:
                old_next_id = self.next_read_id
                self.next_read_id = self._find_next_read_id()
                self.log.debug(f"Updated next_read_id from {old_next_id} to {self.next_read_id}")

    def _find_next_write_id(self):
        """Find the next write ID to process"""
        if not self.pending_writes:
            self.log.debug("No pending writes available for next ID selection")
            return None

        # Log current state for debugging
        self.log.debug(f"Finding next write ID among {len(self.pending_writes)} pending transactions")

        # Find transactions that are complete and processed, but not yet responded to
        complete_ids = []
        for id_value, pending in self.pending_writes.items():
            is_complete = pending.get('complete', False)
            is_processed = pending.get('processed', False)

            # Log status of each transaction
            self.log.debug(f"  ID={id_value}, ADDR=0x{pending['aw_transaction'].awaddr:X}, complete={is_complete}, processed={is_processed}, start_time={pending['start_time']}")

            if is_complete and is_processed:
                complete_ids.append((id_value, pending['start_time']))

        # If there are any complete and processed transactions, use the oldest
        if complete_ids:
            # Sort by timestamp (ascending)
            complete_ids.sort(key=lambda x: x[1])
            oldest_id = complete_ids[0][0]
            self.log.debug(f"Selected oldest complete transaction ID={oldest_id} with start_time={complete_ids[0][1]}")
            return oldest_id

        # Otherwise, find the oldest transaction that is complete but not yet processed
        oldest_time = float('inf')
        oldest_id = None

        for id_value, pending in self.pending_writes.items():
            if pending.get('complete', False) and not pending.get('processed', False):
                if pending.get('start_time', float('inf')) < oldest_time:
                    oldest_time = pending['start_time']
                    oldest_id = id_value

        if oldest_id is not None:
            self.log.debug(f"Selected oldest complete but unprocessed transaction ID={oldest_id} with start_time={oldest_time}")
            return oldest_id

        # If no complete transactions, use the oldest pending transaction
        oldest_time = float('inf')
        oldest_id = None

        for id_value, pending in self.pending_writes.items():
            if pending.get('start_time', float('inf')) < oldest_time:
                oldest_time = pending['start_time']
                oldest_id = id_value

        self.log.debug(f"Selected oldest pending transaction ID={oldest_id} with start_time={oldest_time}")
        return oldest_id

    def _find_next_read_id(self):
        """Find the next read ID to process"""
        if not self.pending_reads:
            self.log.debug("_find_next_read_id: No pending reads, returning None")
            return None

        # Find the oldest pending read
        oldest_time = float('inf')
        oldest_id = None

        for id_value, pending in self.pending_reads.items():
            start_time = pending.get('start_time', float('inf'))
            self.log.debug(f"_find_next_read_id: ID={id_value}, start_time={start_time}, processed={pending.get('processed', False)}")
            if start_time < oldest_time:
                oldest_time = start_time
                oldest_id = id_value

        self.log.debug(f"_find_next_read_id: Selected ID={oldest_id} with start_time={oldest_time}")
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

                # Factor in QoS if applicable
                if resp.get('qos', 0) > 0:
                    # Higher QoS means higher weight
                    weight *= (1.0 + resp['qos'] / 8.0)

                weights.append(weight)

            # Select based on weights
            if sum(weights) > 0:
                return random.choices(range(len(self.write_response_queue)), weights=weights)[0]
            else:
                return 0

        # Default to first response
        return 0

    def _select_read_id(self, id_to_responses):  # sourcery skip: extract-method
        """Select a read ID to process based on the out-of-order strategy"""
        if not id_to_responses:
            return None

        ids = list(id_to_responses.keys())
        self.log.debug(f"_select_read_id: Available IDs: {ids}, strategy={self.ooo_strategy}")

        if self.ooo_strategy == 'random':
            # Do not use random - for debugging, use consistent ordering instead
            # return random.choice(ids)
            result = ids[0]  # Always choose the first ID for consistent behavior
            self.log.debug(f"_select_read_id: Using first ID {result} instead of random for debugging")
            return result

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

                # Factor in QoS if applicable
                for idx, resp in id_to_responses[id_value]:
                    if resp.get('qos', 0) > 0:
                        # Higher QoS means higher weight
                        weight *= (1.0 + resp['qos'] / 8.0)
                        break

                weights.append(weight)

            self.log.debug(f"_select_read_id: IDs with weights: {list(zip(ids, weights))}")

            # Select based on weights - but for debugging, use deterministic ordering
            # return random.choices(ids, weights=weights)[0] if sum(weights) > 0 else ids[0]

            # Just use the highest weighted ID for consistent behavior
            max_weight_idx = weights.index(max(weights))
            result = ids[max_weight_idx]
            self.log.debug(f"_select_read_id: Selected highest weighted ID {result}")
            return result

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

    def get_extension_stats(self):
        """
        Get statistics from all extension handlers.

        Returns:
            Dictionary with statistics from all extensions
        """
        return {
            name: handler.get_stats()
            for name, handler in self.extensions.items()
            if hasattr(handler, 'get_stats')
        }

    async def register_exclusive_region(self, start_address, end_address):
        """
        Register a memory region that requires exclusive access.

        Args:
            start_address: Start address of the region
            end_address: End address of the region
        """
        if 'exclusive' in self.extensions:
            self.extensions['exclusive'].register_exclusive_region(start_address, end_address)
        else:
            self.log.error("Exclusive access not available - no exclusive extension handler")

    def _debug_print_response_queue(self, prefix=""):
        """Print the current state of the read response queue for debugging"""
        self.log.debug(f"{prefix} Read response queue state:")
        self.log.debug(f"  next_read_id = {self.next_read_id}")
        self.log.debug(f"  inorder = {self.inorder}")
        self.log.debug(f"  Queue length: {len(self.read_response_queue)}")

        # Group responses by ID for easier visualization
        id_resp_map = {}
        for i, resp in enumerate(self.read_response_queue):
            id_val = resp['id']
            if id_val not in id_resp_map:
                id_resp_map[id_val] = []
            id_resp_map[id_val].append((i, resp))

        # Print grouped by ID
        for id_val, responses in id_resp_map.items():
            self.log.debug(f"  ID {id_val}: {len(responses)} responses")
            for idx, (queue_idx, resp) in enumerate(responses):
                self.log.debug(f"    {idx}: addr=0x{resp['addr']:X}, beat={resp['beat']}, last={resp['last']}, data=0x{resp['packet'].rdata:X}")

    def _debug_pending_reads(self, prefix=""):
        """Print the current state of pending reads for debugging"""
        self.log.debug(f"{prefix} Pending reads state:")
        self.log.debug(f"  Count: {len(self.pending_reads)}")

        for id_val, pending in self.pending_reads.items():
            self.log.debug(f"  ID {id_val}:")
            self.log.debug(f"    processed: {pending.get('processed', False)}")
            self.log.debug(f"    addresses: {[hex(addr) for addr in pending.get('addresses', [])]}")
            self.log.debug(f"    expected_beats: {pending.get('expected_beats', 0)}")

    async def debug_dump_state(self):
        """Dump the complete internal state for debugging purposes"""
        self.log.debug("====================== AXI4 SLAVE STATE DUMP ======================")
        self.log.debug(f"Title: {self.title}")
        self.log.debug(f"inorder: {self.inorder}")
        self.log.debug(f"ooo_strategy: {self.ooo_strategy}")
        self.log.debug(f"next_read_id: {self.next_read_id}")
        self.log.debug(f"next_write_id: {self.next_write_id}")
        self._debug_pending_reads("State dump")
        self._debug_print_response_queue("State dump")
        self.log.debug("================================================================")