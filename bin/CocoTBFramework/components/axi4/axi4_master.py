"""
AXI4 Master Component for Verification

This module provides the AXI4Master class for AXI4 master interfaces with
integrated protocol extensions and sequence support.
"""

import cocotb
from collections import deque
from cocotb.triggers import RisingEdge, Event
from cocotb.utils import get_sim_time

from ..gaxi.gaxi_factories import create_gaxi_master, create_gaxi_slave
from ..flex_randomizer import FlexRandomizer

from .axi4_fields_signals import (
    AXI4_MASTER_DEFAULT_CONSTRAINTS,
    get_aw_signal_map,
    get_w_signal_map,
    get_b_signal_map,
    get_ar_signal_map,
    get_r_signal_map
)
from .axi4_packet import AXI4Packet
from .axi4_seq_transaction import AXI4TransactionSequence
from .axi4_seq_address import AXI4AddressSequence
from .axi4_seq_data import AXI4DataSequence
from .axi4_extensions import create_axi4_extension_handlers
from ..debug_object import print_object_details, print_dict_to_log


class AXI4Master:
    """
    AXI4 Master component that manages multiple channels for AXI4 transactions.

    This class provides:
    - Separate GAXI masters for each AXI4 channel (AW, W, B, AR, R)
    - Coordinated transaction management across channels
    - AXI4 protocol checking
    - Integrated sequence support
    - Protocol extensions (QoS, exclusive access, atomic operations, barriers)
    """

    def __init__(self, dut, title, prefix, divider, suffix, clock, channels,
                id_width=8, addr_width=32, data_width=32, user_width=1,
                field_configs=None, aw_randomizer=None, w_randomizer=None, ar_randomizer=None,
                check_protocol=True, inorder=False, ooo_strategy='random',
                memory_model=None, extensions=None, log=None):
        """
        Initialize AXI4 Master component.

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
            aw_randomizer: Timing randomizer for AW channel
            w_randomizer: Timing randomizer for W channel
            ar_randomizer: Timing randomizer for AR channel
            check_protocol: Enable AXI4 protocol checking (default: True)
            inorder: Force in-order responses across different IDs (default: False)
            ooo_strategy: Strategy for out-of-order responses ('random', 'round_robin', 'weighted')
            memory_model: Memory model for data storage (optional)
            extensions: Dictionary of extension handlers (optional)
            log: Logger instance
        """
        self.title = title
        self.clock = clock
        self.log = log
        self.check_protocol = check_protocol
        self.inorder = inorder
        self.ooo_strategy = ooo_strategy
        self.memory_model = memory_model
        self.channels = [s.upper() for s in channels]

        # Store width parameters for sequence creation
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
            raise ValueError(f"AXI4Master '{title}' requires field configs for each channel")

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

        # Create randomizers if not provided
        self.aw_randomizer = aw_randomizer or FlexRandomizer(AXI4_MASTER_DEFAULT_CONSTRAINTS)
        self.w_randomizer = w_randomizer or FlexRandomizer(AXI4_MASTER_DEFAULT_CONSTRAINTS)
        self.ar_randomizer = ar_randomizer or FlexRandomizer(AXI4_MASTER_DEFAULT_CONSTRAINTS)

        print_object_details(self, self.log, f"AXI4 Master '{self.title}' INIT")
        # Create channel components
        if 'AW' in self.channels and self.aw_field_config:
            self.aw_master = create_gaxi_master(
                dut, f"{title}_AW", "", clock,
                field_config=self.aw_field_config,
                packet_class=AXI4Packet,
                randomizer=self.aw_randomizer,
                multi_sig=True,
                signal_map=aw_signal_map,
                optional_signal_map=aw_optional_signal_map,
                log=log
            )
        else:
            self.aw_master = None

        if 'W' in self.channels and self.w_field_config:
            self.w_master = create_gaxi_master(
                dut, f"{title}_W", "", clock,
                field_config=self.w_field_config,
                packet_class=AXI4Packet,
                randomizer=self.w_randomizer,
                multi_sig=True,
                signal_map=w_signal_map,
                optional_signal_map=w_optional_signal_map,
                log=log
            )
        else:
            self.w_master = None

        if 'B' in self.channels and self.b_field_config:
            self.b_slave = create_gaxi_slave(
                dut, f"{title}_B", "", clock,
                field_config=self.b_field_config,
                packet_class=AXI4Packet,
                multi_sig=True,
                signal_map=b_signal_map,
                optional_signal_map=b_optional_signal_map,
                log=log
            )
        else:
            self.b_slave = None

        if 'AR' in self.channels and self.ar_field_config:
            self.ar_master = create_gaxi_master(
                dut, f"{title}_AR", "", clock,
                field_config=self.ar_field_config,
                packet_class=AXI4Packet,
                randomizer=self.ar_randomizer,
                multi_sig=True,
                signal_map=ar_signal_map,
                optional_signal_map=ar_optional_signal_map,
                log=log
            )
        else:
            self.ar_master = None

        if 'R' in self.channels and self.r_field_config:
            self.r_slave = create_gaxi_slave(
                dut, f"{title}_R", "", clock,
                field_config=self.r_field_config,
                packet_class=AXI4Packet,
                multi_sig=True,
                signal_map=r_signal_map,
                optional_signal_map=r_optional_signal_map,
                log=log
            )
        else:
            self.r_slave = None

        # Initialize transaction tracking
        self.write_responses = {}  # Maps IDs to pending write transactions
        self.read_responses = {}   # Maps IDs to pending read transactions

        # Add callbacks to track responses
        if 'B' in self.channels and self.b_slave:
            self.b_slave.add_callback(self._handle_b_response)
        if 'R' in self.channels and self.r_slave:
            self.r_slave.add_callback(self._handle_r_response)

        # Initialize extensions
        self.extensions = extensions or {}

        # Create standard extension handlers if none provided and memory model is available
        if not self.extensions and self.memory_model:
            self.extensions = create_axi4_extension_handlers(self.memory_model, self.log)

        # Master ID - used for exclusive access tracking
        self.master_id = id(self)

        # Create sequence support
        self._initialize_sequence_support()

        self.log.info(f"AXI4Master '{title}' initialized")

    def _initialize_sequence_support(self):
        """Initialize sequence support with default transaction sequence."""
        # Create a default transaction sequence
        self.transaction_sequence = AXI4TransactionSequence(
            name=f"{self.title}_seq",
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width
        )

        # Create sequence events tracking
        self.sequence_events = {}

        # Sequence execution task
        self.sequence_task = None

    async def reset_bus(self):
        """Reset all AXI4 channels"""
        if 'AW' in self.channels and self.aw_master:
            await self.aw_master.reset_bus()
        if 'W' in self.channels and self.w_master:
            await self.w_master.reset_bus()
        if 'B' in self.channels and self.b_slave:
            await self.b_slave.reset_bus()
        if 'AR' in self.channels and self.ar_master:
            await self.ar_master.reset_bus()
        if 'R' in self.channels and self.r_slave:
            await self.r_slave.reset_bus()

        # Clear transaction tracking
        if 'B' in self.channels:
            self.write_responses.clear()
        if 'R' in self.channels:
            self.read_responses.clear()

        # Reset sequence support
        self.sequence_events.clear()
        self.transaction_sequence = AXI4TransactionSequence(
            name=f"{self.title}_seq",
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width
        )

    def _handle_b_response(self, transaction):
        """Callback for B channel responses"""
        if hasattr(transaction, 'bid') and transaction.bid in self.write_responses:
            pending_transaction = self.write_responses[transaction.bid]

            # Log response
            self.log.debug(f"Received write response: ID={transaction.bid}, RESP={transaction.bresp}")

            # Update response info
            pending_transaction['response'] = transaction

            # Check if this is the last expected response
            if pending_transaction.get('response_count', 0) <= 1:
                # Mark as complete
                pending_transaction['complete'] = True

                # Set completion event if this is part of a sequence
                if transaction.bid in self.sequence_events:
                    self.sequence_events[transaction.bid].set()

                # Check if this was an exclusive write
                if ('exclusive_access' in pending_transaction and
                    hasattr(transaction, 'bresp') and transaction.bresp == 1):  # EXOKAY
                    pending_transaction['exclusive_success'] = True
            else:
                # Decrement response count
                pending_transaction['response_count'] -= 1

    def _handle_r_response(self, transaction):
        """Callback for R channel responses"""
        if hasattr(transaction, 'rid') and transaction.rid in self.read_responses:
            pending_transaction = self.read_responses[transaction.rid]

            # Log response
            self.log.debug(f"Received read data: ID={transaction.rid}, DATA=0x{transaction.rdata:X}, RESP={transaction.rresp}, LAST={transaction.rlast}")

            # Add to response data
            if 'responses' not in pending_transaction:
                pending_transaction['responses'] = []
            pending_transaction['responses'].append(transaction)

            # Check if this is the last data beat
            if transaction.rlast:
                # Mark as complete
                pending_transaction['complete'] = True

                # Set completion event if this is part of a sequence
                if transaction.rid in self.sequence_events:
                    self.sequence_events[transaction.rid].set()

    async def read(self, addr, size=2, burst=1, id=0, length=0, cache=0, prot=0, qos=0, region=0, user=0):
        """
        Execute an AXI4 read transaction.

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
        # Create AR packet
        ar_packet = AXI4Packet.create_ar_packet(
            arid=id,
            araddr=addr,
            arlen=length,
            arsize=size,
            arburst=burst,
            arlock=0,
            arcache=cache,
            arprot=prot,
            arqos=qos,
            arregion=region,
            aruser=user
        )

        # Validate AR packet if protocol checking is enabled
        if self.check_protocol:
            valid, error_msg = ar_packet.validate_axi4_protocol()
            if not valid:
                self.log.error(f"AXI4 protocol error: {error_msg}")
                raise ValueError(f"AXI4 protocol error: {error_msg}")

        # Apply QoS if handler available
        if 'qos' in self.extensions and qos > 0:
            self.log.debug(f"Using QoS={qos} for read transaction ID={id}")
            # Note: QoS is already set in the packet, just log it

        # Create pending transaction entry
        self.read_responses[id] = {
            'ar_packet': ar_packet,
            'responses': [],
            'complete': False,
            'start_time': get_sim_time('ns')
        }

        # Send AR packet
        await self.ar_master.send(ar_packet)

        # Wait for completion or timeout
        timeout_ns = 1000 * (length + 1)  # Scale timeout with burst length
        start_time = get_sim_time('ns')

        while not self.read_responses[id].get('complete', False):
            await RisingEdge(self.clock)

            # Check for timeout
            if get_sim_time('ns') - start_time > timeout_ns:
                self.log.error(f"Timeout waiting for read response for ID {id}")
                break

        # Get result
        result = self.read_responses[id]
        result['end_time'] = get_sim_time('ns')
        result['duration'] = result['end_time'] - result['start_time']

        # Extract data values for convenience
        result['data'] = [r.rdata for r in result.get('responses', [])]

        # Clean up
        if id in self.read_responses:
            del self.read_responses[id]

        return result

    async def write(self, addr, data, size=2, burst=1, strobe=None, id=0, length=0, cache=0, prot=0, qos=0, region=0, user=0):
        """
        Execute an AXI4 write transaction.

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
            dict: Transaction results with response
        """
        # Convert scalar data to list for consistent handling
        if not isinstance(data, (list, bytearray)):
            data = [data]

        # Calculate actual length from data if not specified
        if length == 0 and len(data) > 1:
            length = len(data) - 1

        # Create AW packet
        aw_packet = AXI4Packet.create_aw_packet(
            awid=id,
            awaddr=addr,
            awlen=length,
            awsize=size,
            awburst=burst,
            awlock=0,
            awcache=cache,
            awprot=prot,
            awqos=qos,
            awregion=region,
            awuser=user
        )

        # Validate AW packet if protocol checking is enabled
        if self.check_protocol:
            valid, error_msg = aw_packet.validate_axi4_protocol()
            if not valid:
                self.log.error(f"AXI4 protocol error: {error_msg}")
                raise ValueError(f"AXI4 protocol error: {error_msg}")

        # Apply QoS if handler available
        if 'qos' in self.extensions and qos > 0:
            self.log.debug(f"Using QoS={qos} for write transaction ID={id}")
            # Note: QoS is already set in the packet, just log it

        # Create default strobe if not specified (all bytes enabled)
        if strobe is None:
            strobe = (1 << self.strb_width) - 1

        # Create W packets
        w_packets = []
        for i, d in enumerate(data):
            is_last = i in [len(data) - 1, length]
            w_packet = AXI4Packet.create_w_packet(
                wdata=d,
                wstrb=strobe,
                wlast=1 if is_last else 0,
                wuser=user
            )
            w_packets.append(w_packet)

        # Create pending transaction entry
        self.write_responses[id] = {
            'aw_packet': aw_packet,
            'w_packets': w_packets,
            'response': None,
            'complete': False,
            'start_time': get_sim_time('ns')
        }

        # Send AW packet
        await self.aw_master.send(aw_packet)

        # Send W packets
        for w_packet in w_packets:
            await self.w_master.send(w_packet)

        # Wait for completion or timeout
        timeout_ns = 1000 * (length + 1)  # Scale timeout with burst length
        start_time = get_sim_time('ns')

        while not self.write_responses[id].get('complete', False):
            await RisingEdge(self.clock)

            # Check for timeout
            if get_sim_time('ns') - start_time > timeout_ns:
                self.log.error(f"Timeout waiting for write response for ID {id}")
                break

        # Get result
        result = self.write_responses[id]
        result['end_time'] = get_sim_time('ns')
        result['duration'] = result['end_time'] - result['start_time']

        # Clean up
        if id in self.write_responses:
            del self.write_responses[id]

        return result

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
        # Create AR packet with lock=1 for exclusive access
        ar_packet = AXI4Packet.create_ar_packet(
            arid=id,
            araddr=addr,
            arlen=length,
            arsize=size,
            arburst=burst,
            arlock=1,  # Set lock for exclusive access
            arcache=cache,
            arprot=prot,
            arqos=qos,
            arregion=region,
            aruser=user
        )

        # Validate AR packet if protocol checking is enabled
        if self.check_protocol:
            valid, error_msg = ar_packet.validate_axi4_protocol()
            if not valid:
                self.log.error(f"AXI4 protocol error: {error_msg}")
                raise ValueError(f"AXI4 protocol error: {error_msg}")

        # Register exclusive monitor in extension handler
        if 'exclusive' in self.extensions:
            self.extensions['exclusive'].handle_exclusive_read(
                id, self.master_id, addr, 1 << size
            )

        # Create pending transaction entry with exclusive flag
        self.read_responses[id] = {
            'ar_packet': ar_packet,
            'responses': [],
            'complete': False,
            'start_time': get_sim_time('ns'),
            'exclusive_access': True
        }

        # Send AR packet
        await self.ar_master.send(ar_packet)

        # Wait for completion or timeout
        timeout_ns = 1000 * (length + 1)  # Scale timeout with burst length
        start_time = get_sim_time('ns')

        while not self.read_responses[id].get('complete', False):
            await RisingEdge(self.clock)

            # Check for timeout
            if get_sim_time('ns') - start_time > timeout_ns:
                self.log.error(f"Timeout waiting for exclusive read response for ID {id}")
                break

        # Get result
        result = self.read_responses[id]
        result['end_time'] = get_sim_time('ns')
        result['duration'] = result['end_time'] - result['start_time']

        # Extract data values for convenience
        result['data'] = [r.rdata for r in result.get('responses', [])]

        # Clean up
        if id in self.read_responses:
            del self.read_responses[id]

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
        # Convert scalar data to list for consistent handling
        if not isinstance(data, (list, bytearray)):
            data = [data]

        # Calculate actual length from data if not specified
        if length == 0 and len(data) > 1:
            length = len(data) - 1

        # Create AW packet with lock=1 for exclusive access
        aw_packet = AXI4Packet.create_aw_packet(
            awid=id,
            awaddr=addr,
            awlen=length,
            awsize=size,
            awburst=burst,
            awlock=1,  # Set lock for exclusive access
            awcache=cache,
            awprot=prot,
            awqos=qos,
            awregion=region,
            awuser=user
        )

        # Validate AW packet if protocol checking is enabled
        if self.check_protocol:
            valid, error_msg = aw_packet.validate_axi4_protocol()
            if not valid:
                self.log.error(f"AXI4 protocol error: {error_msg}")
                raise ValueError(f"AXI4 protocol error: {error_msg}")

        # Create default strobe if not specified (all bytes enabled)
        if strobe is None:
            strobe = (1 << self.strb_width) - 1

        # Create W packets
        w_packets = []
        for i, d in enumerate(data):
            is_last = i in [len(data) - 1, length]
            w_packet = AXI4Packet.create_w_packet(
                wdata=d,
                wstrb=strobe,
                wlast=1 if is_last else 0,
                wuser=user
            )
            w_packets.append(w_packet)

        # Create pending transaction entry with exclusive flag
        self.write_responses[id] = {
            'aw_packet': aw_packet,
            'w_packets': w_packets,
            'response': None,
            'complete': False,
            'start_time': get_sim_time('ns'),
            'exclusive_access': True,
            'exclusive_success': False
        }

        # Send AW packet
        await self.aw_master.send(aw_packet)

        # Send W packets
        for w_packet in w_packets:
            await self.w_master.send(w_packet)

        # Wait for completion or timeout
        timeout_ns = 1000 * (length + 1)  # Scale timeout with burst length
        start_time = get_sim_time('ns')

        while not self.write_responses[id].get('complete', False):
            await RisingEdge(self.clock)

            # Check for timeout
            if get_sim_time('ns') - start_time > timeout_ns:
                self.log.error(f"Timeout waiting for exclusive write response for ID {id}")
                break

        # Get result
        result = self.write_responses[id]

        # Check exclusive status in extension handler
        if 'exclusive' in self.extensions:
            success = self.extensions['exclusive'].handle_exclusive_write(
                id, self.master_id, addr, 1 << size
            )
            result['exclusive_success'] = success

        result['end_time'] = get_sim_time('ns')
        result['duration'] = result['end_time'] - result['start_time']

        # Clean up
        if id in self.write_responses:
            del self.write_responses[id]

        return result

    async def atomic_operation(self, op_type, addr, value, compare_value=None, id=0, qos=0):
        """
        Execute an atomic operation.

        Args:
            op_type: Type of atomic operation (ATOMIC_ADD, ATOMIC_SWAP, etc.)
            addr: Target address
            value: Operation value
            compare_value: Comparison value for compare-and-swap
            id: Transaction ID
            qos: Quality of Service

        Returns:
            Tuple of (success, old_value)
        """
        if 'atomic' not in self.extensions:
            self.log.error("Atomic operations not available - no atomic extension handler")
            return False, 0

        # Perform atomic operation via handler
        return self.extensions['atomic'].perform_atomic_operation(
            op_type, addr, value, compare_value
        )

    async def create_barrier(self, barrier_type):
        """
        Create a barrier to ensure transaction ordering.

        Args:
            barrier_type: Type of barrier (BARRIER_MEMORY, BARRIER_DEVICE, BARRIER_SYSTEM)

        Returns:
            Barrier ID or -1 if barriers not supported
        """
        if 'barrier' not in self.extensions:
            self.log.error("Barriers not available - no barrier extension handler")
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
        else:
            self.log.error("Barriers not available - no barrier extension handler")

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
        else:
            self.log.error("Barriers not available - no barrier extension handler")

    async def complete_transaction(self, transaction_id):
        """
        Mark a transaction as complete for barrier tracking.

        Args:
            transaction_id: Transaction ID
        """
        if 'barrier' in self.extensions:
            self.extensions['barrier'].complete_transaction(transaction_id)
        else:
            self.log.error("Barriers not available - no barrier extension handler")

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

    async def execute_transaction_sequence(self, sequence=None):
        """
        Execute a transaction sequence.

        Args:
            sequence: Transaction sequence to execute, or use the default one if None

        Returns:
            Dictionary with transaction results
        """
        # Use provided sequence or the default one
        seq = sequence or self.transaction_sequence

        # Process all write transactions
        write_results = {}
        for write_id in seq.get_write_ids():
            # Get AW and W packets
            aw_packet = seq.get_write_addr_packet(write_id)
            w_packets = seq.get_write_data_packets(write_id)

            if not aw_packet or not w_packets:
                self.log.warning(f"Missing packets for write ID {write_id}")
                continue

            # Create completion event
            completion_event = Event(f"write_{write_id}_complete")
            self.sequence_events[write_id] = completion_event

            # Check if this is an exclusive write
            is_exclusive = False
            if hasattr(aw_packet, 'awlock') and aw_packet.awlock == 1:
                is_exclusive = True

            # Execute write transaction
            if is_exclusive:
                # Use exclusive write method
                result = await self.exclusive_write(
                    addr=aw_packet.awaddr,
                    data=[p.wdata for p in w_packets],
                    size=aw_packet.awsize,
                    burst=aw_packet.awburst,
                    strobe=w_packets[0].wstrb if hasattr(w_packets[0], 'wstrb') else None,
                    id=write_id,
                    length=aw_packet.awlen,
                    cache=aw_packet.awcache if hasattr(aw_packet, 'awcache') else 0,
                    prot=aw_packet.awprot if hasattr(aw_packet, 'awprot') else 0,
                    qos=aw_packet.awqos if hasattr(aw_packet, 'awqos') else 0,
                    region=aw_packet.awregion if hasattr(aw_packet, 'awregion') else 0,
                    user=aw_packet.awuser if hasattr(aw_packet, 'awuser') else 0
                )
            else:
                # Use standard write method
                await self.aw_master.send(aw_packet)
                for w_packet in w_packets:
                    await self.w_master.send(w_packet)

            # Store for result tracking
            write_results[write_id] = {
                'aw_packet': aw_packet,
                'w_packets': w_packets,
                'complete': False
            }

        # Process all read transactions
        read_results = {}
        for read_id in seq.get_read_ids():
            # Get AR packet
            ar_packet = seq.get_read_addr_packet(read_id)

            if not ar_packet:
                self.log.warning(f"Missing packet for read ID {read_id}")
                continue

            if dependencies := seq.get_dependencies(read_id, is_read=True):
                # Wait for dependencies to complete
                for dep_id in dependencies:
                    if dep_id in self.sequence_events:
                        await self.sequence_events[dep_id].wait()

            # Create completion event
            completion_event = Event(f"read_{read_id}_complete")
            self.sequence_events[read_id] = completion_event

            # Check if this is an exclusive read
            is_exclusive = False
            if hasattr(ar_packet, 'arlock') and ar_packet.arlock == 1:
                is_exclusive = True

            # Execute read transaction
            if is_exclusive:
                # Use exclusive read method
                result = await self.exclusive_read(
                    addr=ar_packet.araddr,
                    size=ar_packet.arsize,
                    burst=ar_packet.arburst,
                    id=read_id,
                    length=ar_packet.arlen,
                    cache=ar_packet.arcache if hasattr(ar_packet, 'arcache') else 0,
                    prot=ar_packet.arprot if hasattr(ar_packet, 'arprot') else 0,
                    qos=ar_packet.arqos if hasattr(ar_packet, 'arqos') else 0,
                    region=ar_packet.arregion if hasattr(ar_packet, 'arregion') else 0,
                    user=ar_packet.aruser if hasattr(ar_packet, 'aruser') else 0
                )
            else:
                # Use standard read method
                await self.ar_master.send(ar_packet)

            # Store for result tracking
            read_results[read_id] = {
                'ar_packet': ar_packet,
                'complete': False
            }

        # Wait for all transactions to complete
        for write_id in write_results:
            if write_id in self.sequence_events:
                await self.sequence_events[write_id].wait()
                write_results[write_id]['complete'] = True

        for read_id in read_results:
            if read_id in self.sequence_events:
                await self.sequence_events[read_id].wait()
                read_results[read_id]['complete'] = True

        # Clear events
        self.sequence_events.clear()

        # Return results
        return {
            'write_results': write_results,
            'read_results': read_results
        }

    async def execute_write_transaction(self, addr, data_values, id_value=None, exclusive=False, **kwargs):
        """
        Execute a write transaction and add it to the transaction sequence.

        Args:
            addr: Target address
            data_values: List of data values to write
            id_value: Transaction ID (auto-generated if None)
            exclusive: True for exclusive access
            **kwargs: Additional arguments for write_transaction

        Returns:
            Transaction ID
        """
        # Add to transaction sequence
        tx_id = self.transaction_sequence.add_write_transaction(
            addr=addr,
            data_values=data_values,
            id_value=id_value,
            lock=1 if exclusive else 0,
            **kwargs
        )

        # Get packets
        aw_packet = self.transaction_sequence.get_write_addr_packet(tx_id)
        w_packets = self.transaction_sequence.get_write_data_packets(tx_id)

        # Create completion event
        completion_event = Event(f"write_{tx_id}_complete")
        self.sequence_events[tx_id] = completion_event

        # Execute transaction
        if exclusive:
            # Use exclusive write method
            result = await self.exclusive_write(
                addr=addr,
                data=data_values,
                id=tx_id,
                **kwargs
            )
        else:
            # Use standard write method
            await self.aw_master.send(aw_packet)
            for w_packet in w_packets:
                await self.w_master.send(w_packet)

        # Wait for completion
        await completion_event.wait()

        # Return transaction ID
        return tx_id

    async def execute_read_transaction(self, addr, burst_len=0, id_value=None, exclusive=False, **kwargs):
        """
        Execute a read transaction and add it to the transaction sequence.

        Args:
            addr: Target address
            burst_len: Burst length
            id_value: Transaction ID (auto-generated if None)
            exclusive: True for exclusive access
            **kwargs: Additional arguments for read_transaction

        Returns:
            Transaction ID and data values
        """
        # Add to transaction sequence
        tx_id = self.transaction_sequence.add_read_transaction(
            addr=addr,
            burst_len=burst_len,
            id_value=id_value,
            lock=1 if exclusive else 0,
            **kwargs
        )

        # Get packet
        ar_packet = self.transaction_sequence.get_read_addr_packet(tx_id)

        # Create completion event
        completion_event = Event(f"read_{tx_id}_complete")
        self.sequence_events[tx_id] = completion_event

        # Execute transaction
        if exclusive:
            # Use exclusive read method
            result = await self.exclusive_read(
                addr=addr,
                id=tx_id,
                length=burst_len,
                **kwargs
            )
        else:
            # Use standard read method
            await self.ar_master.send(ar_packet)

        # Wait for completion
        await completion_event.wait()

        # Get response data
        data_values = []
        if tx_id in self.read_responses and 'responses' in self.read_responses[tx_id]:
            data_values = [r.rdata for r in self.read_responses[tx_id]['responses']]

        # Return transaction ID and data values
        return tx_id, data_values
