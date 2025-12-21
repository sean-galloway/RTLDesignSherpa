# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI5 Interfaces
# Purpose: AXI5 Interface Classes for Master and Slave Read/Write operations.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-15

"""
AXI5 Interface Classes - Master and Slave Read/Write implementations.

This module provides interface classes for AXI5 protocol operations with support
for all AXI5-specific features including:
- Atomic operations (ATOP)
- Memory Tagging Extension (MTE) - TAG, TAGOP, TAGUPDATE, TAGMATCH
- Memory Partitioning and Monitoring (MPAM)
- Memory Encryption Context (MECID)
- Chunked transfers
- Poison indicators
- Transaction tracing

Key Design Principles:
1. Composition of GAXI channel objects
2. Transaction coordination between related channels
3. Simple, intuitive APIs (write_single, read_single)
4. Proper ID management and response tracking
5. AXI5-specific signal handling
"""

import asyncio
import random
from typing import List, Dict, Any, Optional, Union

from cocotb.triggers import RisingEdge
import cocotb

# Import GAXI components and AXI5 field configs
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.axi5.axi5_field_configs import AXI5FieldConfigHelper


class AXI5MasterRead:
    """
    AXI5 Master Read Interface.

    Manages read address requests (AR) and read data responses (R) with
    full AXI5 signal support including NSAID, MPAM, MECID, TAGOP, chunking, etc.
    """

    def __init__(self, dut, clock, prefix="", log=None, ifc_name="", **kwargs):
        """
        Initialize AXI5 Master Read interface.

        Args:
            dut: Device under test
            clock: Clock signal
            prefix: Signal name prefix
            log: Logger instance
            ifc_name: Interface name suffix
            **kwargs: Configuration parameters including:
                - data_width: Data bus width (default 32)
                - id_width: ID field width (default 8)
                - addr_width: Address bus width (default 32)
                - user_width: User signal width (default 1)
                - nsaid_width: NSAID field width (default 4)
                - mpam_width: MPAM field width (default 11)
                - mecid_width: MECID field width (default 16)
                - tagop_width: TAGOP field width (default 2)
                - tag_width: Single tag width (default 4)
                - chunknum_width: Chunk number width (default 4)
                - multi_sig: Use individual signals (default True)
                - timeout_cycles: Transaction timeout (default 5000)
        """
        self.super_debug = True
        self.clock = clock
        self.log = log
        self.ifc_name = f"_{ifc_name}" if ifc_name else ""

        # Extract configuration parameters
        self.data_width = kwargs.get('data_width', 32)
        self.id_width = kwargs.get('id_width', 8)
        self.addr_width = kwargs.get('addr_width', 32)
        self.user_width = kwargs.get('user_width', 1)
        self.nsaid_width = kwargs.get('nsaid_width', 4)
        self.mpam_width = kwargs.get('mpam_width', 11)
        self.mecid_width = kwargs.get('mecid_width', 16)
        self.tagop_width = kwargs.get('tagop_width', 2)
        self.tag_width = kwargs.get('tag_width', 4)
        self.chunknum_width = kwargs.get('chunknum_width', 4)
        self.multi_sig = kwargs.get('multi_sig', True)

        # AR Channel (Address Read) - Master drives
        self.ar_channel = GAXIMaster(
            dut=dut,
            title=f"AR_Master{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI5FieldConfigHelper.create_ar_field_config(
                self.id_width, self.addr_width, self.user_width,
                self.nsaid_width, self.mpam_width, self.mecid_width,
                self.tagop_width
            ),
            pkt_prefix="ar",
            multi_sig=self.multi_sig,
            protocol_type='axi5_ar_master',
            super_debug=self.super_debug,
            log=log
        )

        # R Channel - Slave receives responses
        self.r_channel = GAXISlave(
            dut=dut,
            title=f"R_Slave{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI5FieldConfigHelper.create_r_field_config(
                self.id_width, self.data_width, self.user_width,
                self.chunknum_width, self.tag_width
            ),
            pkt_prefix="r",
            multi_sig=self.multi_sig,
            protocol_type='axi5_r_slave',
            super_debug=self.super_debug,
            log=log
        )

        # Timeout configuration
        self.timeout_cycles = kwargs.get('timeout_cycles', 5000)

    async def read_transaction(
        self,
        address: int,
        burst_len: int = 1,
        **transaction_kwargs
    ) -> List[Dict[str, Any]]:
        """
        High-level read transaction with AXI5 features.

        Args:
            address: Read address
            burst_len: Number of beats (default 1)
            **transaction_kwargs: Additional fields including:
                - id: Transaction ID
                - size: Burst size encoding
                - burst: Burst type (FIXED=0, INCR=1, WRAP=2)
                - lock: Lock type
                - cache: Cache attributes
                - prot: Protection attributes
                - qos: Quality of service
                - user: User signal
                - nsaid: Non-secure access ID
                - trace: Enable tracing
                - mpam: Memory partitioning info
                - mecid: Memory encryption context
                - unique: Unique/exclusive access
                - chunken: Enable chunking
                - tagop: Tag operation type

        Returns:
            List of response dictionaries with data and AXI5-specific info
        """
        # Create AR packet with AXI5 fields
        ar_packet = self.ar_channel.create_packet(
            addr=address,
            len=burst_len - 1,
            id=transaction_kwargs.get('id', 0),
            size=transaction_kwargs.get('size', 2),
            burst=transaction_kwargs.get('burst', 1),
            lock=transaction_kwargs.get('lock', 0),
            cache=transaction_kwargs.get('cache', 0),
            prot=transaction_kwargs.get('prot', 0),
            qos=transaction_kwargs.get('qos', 0),
            user=transaction_kwargs.get('user', 0),
            # AXI5-specific fields
            nsaid=transaction_kwargs.get('nsaid', 0),
            trace=transaction_kwargs.get('trace', 0),
            mpam=transaction_kwargs.get('mpam', 0),
            mecid=transaction_kwargs.get('mecid', 0),
            unique=transaction_kwargs.get('unique', 0),
            chunken=transaction_kwargs.get('chunken', 0),
            tagop=transaction_kwargs.get('tagop', 0),
        )

        # Record initial queue state
        initial_count = len(self.r_channel._recvQ)
        expected_count = initial_count + burst_len

        # Send read address
        await self.ar_channel.send(ar_packet)

        # Wait for R responses
        cycles_waited = 0
        while len(self.r_channel._recvQ) < expected_count:
            await RisingEdge(self.clock)
            cycles_waited += 1

            if cycles_waited > self.timeout_cycles:
                received = len(self.r_channel._recvQ) - initial_count
                raise TimeoutError(
                    f"AXI5 read timeout after {cycles_waited} cycles: "
                    f"got {received} of {burst_len} responses at address 0x{address:08X}"
                )

        # Extract data and AXI5-specific info from response packets
        responses = []
        for i in range(burst_len):
            packet = self.r_channel._recvQ[initial_count + i]

            response = {
                'data': getattr(packet, 'data', 0),
                'resp': getattr(packet, 'resp', 0),
                'last': getattr(packet, 'last', 0),
                'id': getattr(packet, 'id', 0),
                # AXI5-specific fields
                'trace': getattr(packet, 'trace', 0),
                'poison': getattr(packet, 'poison', 0),
                'chunkv': getattr(packet, 'chunkv', 0),
                'chunknum': getattr(packet, 'chunknum', 0),
                'chunkstrb': getattr(packet, 'chunkstrb', 0),
                'tag': getattr(packet, 'tag', 0),
                'tagmatch': getattr(packet, 'tagmatch', 0),
            }
            responses.append(response)

            # Check for errors
            if response['resp'] != 0:
                resp_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
                resp_name = resp_names.get(response['resp'], 'UNKNOWN')
                if self.log:
                    self.log.warning(f"AXI5 read response: {resp_name}")

            # Check for poison
            if response['poison']:
                if self.log:
                    self.log.warning(f"AXI5 read: POISON indicator set for beat {i}")

        return responses

    async def single_read(self, address: int, **kwargs) -> int:
        """
        Convenience method for single read.

        Args:
            address: Read address
            **kwargs: Additional transaction parameters

        Returns:
            Read data value
        """
        responses = await self.read_transaction(address, burst_len=1, **kwargs)
        return responses[0]['data']

    def create_ar_packet(self, **kwargs):
        """Create AR packet with current configuration."""
        return self.ar_channel.create_packet(**kwargs)


class AXI5MasterWrite:
    """
    AXI5 Master Write Interface.

    Manages write address requests (AW), write data (W), and write responses (B)
    with full AXI5 signal support including ATOP, MTE, MPAM, etc.
    """

    def __init__(self, dut, clock, prefix="", log=None, ifc_name="", **kwargs):
        """
        Initialize AXI5 Master Write interface.

        Args:
            dut: Device under test
            clock: Clock signal
            prefix: Signal name prefix
            log: Logger instance
            ifc_name: Interface name suffix
            **kwargs: Configuration parameters (see AXI5MasterRead)
        """
        self.clock = clock
        self.log = log
        self.ifc_name = f"_{ifc_name}" if ifc_name else ""

        # Extract configuration parameters
        self.data_width = kwargs.get('data_width', 32)
        self.id_width = kwargs.get('id_width', 8)
        self.addr_width = kwargs.get('addr_width', 32)
        self.user_width = kwargs.get('user_width', 1)
        self.nsaid_width = kwargs.get('nsaid_width', 4)
        self.mpam_width = kwargs.get('mpam_width', 11)
        self.mecid_width = kwargs.get('mecid_width', 16)
        self.atop_width = kwargs.get('atop_width', 6)
        self.tagop_width = kwargs.get('tagop_width', 2)
        self.tag_width = kwargs.get('tag_width', 4)
        self.multi_sig = kwargs.get('multi_sig', True)

        # Calculate derived widths
        self.num_tags = max(1, self.data_width // 128)
        self.total_tag_width = self.tag_width * self.num_tags

        # AW Channel (Address Write) - Master drives
        self.aw_channel = GAXIMaster(
            dut=dut,
            title=f"AW_Master{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI5FieldConfigHelper.create_aw_field_config(
                self.id_width, self.addr_width, self.user_width,
                self.nsaid_width, self.mpam_width, self.mecid_width,
                self.atop_width, self.tagop_width, self.tag_width,
                self.data_width
            ),
            pkt_prefix="aw",
            multi_sig=self.multi_sig,
            protocol_type='axi5_aw_master',
            log=log
        )

        # W Channel (Write Data) - Master drives
        self.w_channel = GAXIMaster(
            dut=dut,
            title=f"W_Master{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI5FieldConfigHelper.create_w_field_config(
                self.data_width, self.user_width, self.tag_width
            ),
            pkt_prefix="w",
            multi_sig=self.multi_sig,
            protocol_type='axi5_w_master',
            log=log
        )

        # B Channel (Write Response) - Slave receives responses
        self.b_channel = GAXISlave(
            dut=dut,
            title=f"B_Slave{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI5FieldConfigHelper.create_b_field_config(
                self.id_width, self.user_width, self.tag_width, self.data_width
            ),
            pkt_prefix="b",
            multi_sig=self.multi_sig,
            protocol_type='axi5_b_slave',
            log=log
        )

        # Timeout configuration
        self.timeout_cycles = kwargs.get('timeout_cycles', 5000)

    async def write_transaction(
        self,
        address: int,
        data: Union[int, List[int]],
        burst_len: Optional[int] = None,
        **transaction_kwargs
    ) -> Dict[str, Any]:
        """
        High-level write transaction with AXI5 features.

        Args:
            address: Write address
            data: Write data (single value or list for burst)
            burst_len: Burst length (auto-detected from data if not specified)
            **transaction_kwargs: Additional fields including:
                - id: Transaction ID
                - size: Burst size encoding
                - burst: Burst type
                - lock: Lock type
                - cache: Cache attributes
                - prot: Protection attributes
                - qos: Quality of service
                - user: User signal
                - strb: Write strobe
                - atop: Atomic operation type
                - nsaid: Non-secure access ID
                - trace: Enable tracing
                - mpam: Memory partitioning info
                - mecid: Memory encryption context
                - unique: Unique/exclusive access
                - tagop: Tag operation type
                - tag: Memory tags (AW and W)
                - poison: Poison indicator (W)
                - tagupdate: Tag update indicators (W)

        Returns:
            Response dictionary with status and AXI5-specific info
        """
        aw_packet = None

        try:
            # Handle data formatting
            if isinstance(data, list):
                data_list = data
                if burst_len is None:
                    burst_len = len(data_list)
                else:
                    data_list = data_list[:burst_len]
            else:
                if burst_len is None:
                    burst_len = 1
                data_list = [data] * burst_len

            # Create AW packet with AXI5 fields
            aw_packet = self.aw_channel.create_packet(
                addr=address,
                len=burst_len - 1,
                id=transaction_kwargs.get('id', 0),
                size=transaction_kwargs.get('size', 2),
                burst=transaction_kwargs.get('burst', 1),
                lock=transaction_kwargs.get('lock', 0),
                cache=transaction_kwargs.get('cache', 0),
                prot=transaction_kwargs.get('prot', 0),
                qos=transaction_kwargs.get('qos', 0),
                user=transaction_kwargs.get('user', 0),
                # AXI5-specific fields
                atop=transaction_kwargs.get('atop', 0),
                nsaid=transaction_kwargs.get('nsaid', 0),
                trace=transaction_kwargs.get('trace', 0),
                mpam=transaction_kwargs.get('mpam', 0),
                mecid=transaction_kwargs.get('mecid', 0),
                unique=transaction_kwargs.get('unique', 0),
                tagop=transaction_kwargs.get('tagop', 0),
                tag=transaction_kwargs.get('tag', 0),
            )

            # Send address
            await self.aw_channel.send(aw_packet)

            # Send data beats with AXI5 fields
            strb_width = self.data_width // 8
            default_strb = (1 << strb_width) - 1

            for i, data_value in enumerate(data_list):
                w_packet = self.w_channel.create_packet(
                    data=data_value,
                    last=1 if i == len(data_list) - 1 else 0,
                    strb=transaction_kwargs.get('strb', default_strb),
                    user=transaction_kwargs.get('wuser', 0),
                    # AXI5-specific fields
                    poison=transaction_kwargs.get('poison', 0),
                    tag=transaction_kwargs.get('wtag', 0),
                    tagupdate=transaction_kwargs.get('tagupdate', 0),
                )
                await self.w_channel.send(w_packet)

            # Wait for write response
            initial_b_count = len(self.b_channel._recvQ)
            expected_b_count = initial_b_count + 1

            cycles_waited = 0
            while len(self.b_channel._recvQ) < expected_b_count:
                await RisingEdge(self.clock)
                cycles_waited += 1

                if cycles_waited > self.timeout_cycles:
                    raise TimeoutError(
                        f"AXI5 write timeout after {cycles_waited} cycles: "
                        f"waiting for B response at address 0x{address:08X}"
                    )

            # Get B response packet
            b_response = self.b_channel._recvQ[initial_b_count]

            result = {
                'success': True,
                'response': getattr(b_response, 'resp', 0),
                'id': getattr(b_response, 'id', 0),
                # AXI5-specific fields
                'trace': getattr(b_response, 'trace', 0),
                'tag': getattr(b_response, 'tag', 0),
                'tagmatch': getattr(b_response, 'tagmatch', 0),
            }

            # Check for errors
            if result['response'] != 0:
                resp_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
                resp_name = resp_names.get(result['response'], 'UNKNOWN')
                raise RuntimeError(f"AXI5 write error: {resp_name}")

            return result

        except Exception as e:
            if self.log:
                addr_str = f"addr=0x{address:08X}" if address is not None else "addr=None"
                self.log.error(f"AXI5 write transaction failed: {addr_str}, error: {str(e)}")

            return {
                'success': False,
                'error': str(e),
                'response': None,
                'id': None
            }

    async def single_write(self, address: int, data: int, **kwargs) -> Dict[str, Any]:
        """Convenience method for single write."""
        return await self.write_transaction(address, data, burst_len=1, **kwargs)

    async def atomic_operation(
        self,
        address: int,
        data: int,
        atop: int,
        **kwargs
    ) -> Dict[str, Any]:
        """
        Perform an atomic operation.

        Args:
            address: Target address
            data: Operand data
            atop: Atomic operation type (6-bit encoding)
            **kwargs: Additional transaction parameters

        Returns:
            Response dictionary with result
        """
        kwargs['atop'] = atop
        return await self.write_transaction(address, data, burst_len=1, **kwargs)


class AXI5SlaveRead:
    """
    AXI5 Slave Read Interface.

    Handles read requests from masters and generates appropriate responses
    with full AXI5 signal support.
    """

    def __init__(self, dut, clock, prefix="", log=None, ifc_name="", **kwargs):
        """
        Initialize AXI5 Slave Read interface.

        Args:
            dut: Device under test
            clock: Clock signal
            prefix: Signal name prefix
            log: Logger instance
            ifc_name: Interface name suffix
            **kwargs: Configuration parameters including:
                - memory_model: Memory model for data storage
                - base_addr: Base address offset
                - response_delay: Response delay cycles
                - enable_ooo: Enable out-of-order responses
                - ooo_config: OOO configuration dict
        """
        self.clock = clock
        self.log = log
        self.ifc_name = f"_{ifc_name}" if ifc_name else ""

        # Extract configuration parameters
        self.data_width = kwargs.get('data_width', 32)
        self.id_width = kwargs.get('id_width', 8)
        self.addr_width = kwargs.get('addr_width', 32)
        self.user_width = kwargs.get('user_width', 1)
        self.nsaid_width = kwargs.get('nsaid_width', 4)
        self.mpam_width = kwargs.get('mpam_width', 11)
        self.mecid_width = kwargs.get('mecid_width', 16)
        self.tagop_width = kwargs.get('tagop_width', 2)
        self.tag_width = kwargs.get('tag_width', 4)
        self.chunknum_width = kwargs.get('chunknum_width', 4)
        self.multi_sig = kwargs.get('multi_sig', True)

        # Memory model
        self.memory_model = kwargs.get('memory_model')
        self.base_addr = kwargs.get('base_addr', 0)

        # Response configuration
        self.response_delay_cycles = kwargs.get('response_delay', 1)

        # OOO configuration
        self.enable_ooo = kwargs.get('enable_ooo', False)
        self.ooo_config = kwargs.get('ooo_config', {
            'mode': 'random',
            'reorder_probability': 0.3,
            'min_delay_cycles': 1,
            'max_delay_cycles': 50,
            'pattern': None,
        })

        # OOO state tracking
        self.ooo_transaction_sequence = 0
        self.ooo_transaction_metadata = {}
        self.ooo_last_completed_seq = {}

        # In-order serialization
        self.in_order_active = {}
        self.in_order_queue = {}

        # AR Channel - Slave drives arready
        self.ar_channel = GAXISlave(
            dut=dut,
            title=f"AR_Slave{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI5FieldConfigHelper.create_ar_field_config(
                self.id_width, self.addr_width, self.user_width,
                self.nsaid_width, self.mpam_width, self.mecid_width,
                self.tagop_width
            ),
            pkt_prefix="ar",
            multi_sig=self.multi_sig,
            protocol_type='axi5_ar_slave',
            log=log,
        )

        # R Channel - Master drives responses
        self.r_channel = GAXIMaster(
            dut=dut,
            title=f"R_Master{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI5FieldConfigHelper.create_r_field_config(
                self.id_width, self.data_width, self.user_width,
                self.chunknum_width, self.tag_width
            ),
            pkt_prefix="r",
            multi_sig=self.multi_sig,
            protocol_type='axi5_r_master',
            log=log,
            super_debug=True,
        )

        # Set up callback from AR slave to trigger R responses
        self.ar_channel.add_callback(self._ar_callback)

        if self.log:
            mode_str = "OOO mode ENABLED" if self.enable_ooo else "In-order mode"
            self.log.info(f"AXI5SlaveRead initialized: {mode_str}")

    def _ar_callback(self, ar_packet):
        """Handle AR packet reception and schedule R response."""
        transaction_id = getattr(ar_packet, 'id', 0)
        addr = getattr(ar_packet, 'addr', 0)

        # Assign sequence number for OOO tracking
        if self.enable_ooo:
            txn_sequence = self.ooo_transaction_sequence
            self.ooo_transaction_sequence += 1
            self.ooo_transaction_metadata[txn_sequence] = {
                'id': transaction_id,
                'addr': addr
            }
            ar_packet._ooo_sequence = txn_sequence

        if self.log:
            self.log.debug(f"AXI5SlaveRead: AR callback - addr=0x{addr:08X}, id={transaction_id}")

        # Schedule R response generation
        if self.enable_ooo:
            delay_cycles = self._calculate_ooo_delay(ar_packet)
            cocotb.start_soon(self._generate_read_response_delayed(ar_packet, delay_cycles))
        else:
            cocotb.start_soon(self._generate_read_response_serialized(ar_packet))

    def _calculate_ooo_delay(self, ar_packet):
        """Calculate delay for OOO response."""
        txn_sequence = getattr(ar_packet, '_ooo_sequence', None)
        if txn_sequence is None:
            return 1

        transaction_id = getattr(ar_packet, 'id', 0)
        txn_meta = self.ooo_transaction_metadata.get(txn_sequence, {})
        txn_id = txn_meta.get('id', transaction_id)

        # Check for blocking same-ID transactions
        last_completed = self.ooo_last_completed_seq.get(txn_id, -1)
        blocking_sequences = [
            seq for seq, meta in self.ooo_transaction_metadata.items()
            if meta['id'] == txn_id and seq < txn_sequence and seq > last_completed
        ]

        if blocking_sequences:
            return 100  # Wait for earlier same-ID transactions

        mode = self.ooo_config.get('mode', 'random')
        if mode == 'random':
            min_delay = self.ooo_config.get('min_delay_cycles', 1)
            max_delay = self.ooo_config.get('max_delay_cycles', 50)
            base_delay = random.randint(min_delay, max_delay)

            if random.random() < self.ooo_config.get('reorder_probability', 0.3):
                return base_delay + random.randint(20, 50)
            return base_delay

        return 1

    async def _generate_read_response_serialized(self, ar_packet):
        """Generate read response with serialization for in-order mode."""
        transaction_id = getattr(ar_packet, 'id', 0)

        if transaction_id not in self.in_order_queue:
            self.in_order_queue[transaction_id] = []
            self.in_order_active[transaction_id] = False

        self.in_order_queue[transaction_id].append(ar_packet)

        if self.in_order_active[transaction_id]:
            return

        self.in_order_active[transaction_id] = True

        while self.in_order_queue[transaction_id]:
            packet = self.in_order_queue[transaction_id].pop(0)
            await self._generate_read_response(packet)

        self.in_order_active[transaction_id] = False

    async def _generate_read_response_delayed(self, ar_packet, delay_cycles):
        """Generate read response after delay (OOO mode)."""
        for _ in range(delay_cycles):
            await RisingEdge(self.clock)
        await self._generate_read_response(ar_packet)

    async def _generate_read_response(self, ar_packet):
        """Generate R response for an AR request."""
        try:
            address = getattr(ar_packet, 'addr', 0)
            burst_len = getattr(ar_packet, 'len', 0) + 1
            packet_id = getattr(ar_packet, 'id', 0)
            size_encoding = getattr(ar_packet, 'size', 2)
            bytes_per_beat = 1 << size_encoding

            # Extract AXI5-specific AR fields for response generation
            ar_trace = getattr(ar_packet, 'trace', 0)
            ar_tagop = getattr(ar_packet, 'tagop', 0)
            ar_chunken = getattr(ar_packet, 'chunken', 0)

            if self.log:
                self.log.debug(
                    f"AXI5SlaveRead: Generating {burst_len} beat response "
                    f"for addr=0x{address:08X}, id={packet_id}"
                )

            # Add configurable delay
            for _ in range(self.response_delay_cycles):
                await RisingEdge(self.clock)

            # Generate response data beats
            r_packets = []
            for i in range(burst_len):
                current_addr = address + (i * bytes_per_beat)

                # Read from memory model if available
                if self.memory_model:
                    try:
                        memory_offset = current_addr - self.base_addr
                        data_bytes = self.memory_model.read(memory_offset, bytes_per_beat)
                        data = self.memory_model.bytearray_to_integer(data_bytes)
                    except Exception as e:
                        if self.log:
                            self.log.warning(f"Memory read failed at 0x{current_addr:08X}: {e}")
                        data = current_addr
                else:
                    data = current_addr

                # Create R response packet with AXI5 fields
                is_last = (i == burst_len - 1)
                r_packet = self.r_channel.create_packet(
                    id=packet_id,
                    data=data,
                    resp=0,
                    last=1 if is_last else 0,
                    # AXI5-specific fields
                    trace=ar_trace,
                    poison=0,
                    chunkv=1 if ar_chunken else 0,
                    chunknum=i if ar_chunken else 0,
                    chunkstrb=0,
                    tag=0,
                    tagmatch=0 if ar_tagop == 0 else 1,  # Simple tag match simulation
                )
                r_packets.append(r_packet)

            # Add all beats to queue
            for r_packet in r_packets:
                self.r_channel.transmit_queue.append(r_packet)

            # Start pipeline if not running
            if not self.r_channel.transmit_coroutine:
                self.r_channel.transmit_coroutine = cocotb.start_soon(
                    self.r_channel._transmit_pipeline()
                )

            # Update OOO tracking
            if self.enable_ooo:
                txn_sequence = getattr(ar_packet, '_ooo_sequence', None)
                if txn_sequence is not None:
                    txn_meta = self.ooo_transaction_metadata.get(txn_sequence, {})
                    txn_id = txn_meta.get('id', packet_id)
                    self.ooo_last_completed_seq[txn_id] = txn_sequence

        except Exception as e:
            if self.log:
                self.log.error(f"AXI5SlaveRead: Error generating response: {e}")


class AXI5SlaveWrite:
    """
    AXI5 Slave Write Interface.

    Handles write requests from masters including AXI5-compliant W-before-AW handling
    and generates appropriate B responses with full AXI5 signal support.
    """

    def __init__(self, dut, clock, prefix="", log=None, ifc_name="", **kwargs):
        """
        Initialize AXI5 Slave Write interface.

        Args:
            dut: Device under test
            clock: Clock signal
            prefix: Signal name prefix
            log: Logger instance
            ifc_name: Interface name suffix
            **kwargs: Configuration parameters (see AXI5SlaveRead)
        """
        self.clock = clock
        self.log = log
        self.ifc_name = f"_{ifc_name}" if ifc_name else ""

        # Extract configuration parameters
        self.data_width = kwargs.get('data_width', 32)
        self.id_width = kwargs.get('id_width', 8)
        self.addr_width = kwargs.get('addr_width', 32)
        self.user_width = kwargs.get('user_width', 1)
        self.nsaid_width = kwargs.get('nsaid_width', 4)
        self.mpam_width = kwargs.get('mpam_width', 11)
        self.mecid_width = kwargs.get('mecid_width', 16)
        self.atop_width = kwargs.get('atop_width', 6)
        self.tagop_width = kwargs.get('tagop_width', 2)
        self.tag_width = kwargs.get('tag_width', 4)
        self.multi_sig = kwargs.get('multi_sig', True)

        # Memory model
        self.memory_model = kwargs.get('memory_model')
        self.base_addr = kwargs.get('base_addr', 0)

        # Response configuration
        self.response_delay_cycles = kwargs.get('response_delay', 1)

        # OOO configuration
        self.enable_ooo = kwargs.get('enable_ooo', False)
        self.ooo_config = kwargs.get('ooo_config', {
            'mode': 'random',
            'reorder_probability': 0.3,
            'min_delay_cycles': 1,
            'max_delay_cycles': 50,
            'pattern': None,
        })

        # OOO state tracking
        self.ooo_transaction_sequence = 0
        self.ooo_transaction_metadata = {}
        self.ooo_last_completed_seq = {}

        # AW Channel - Slave drives awready
        self.aw_channel = GAXISlave(
            dut=dut,
            title=f"AW_Slave{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI5FieldConfigHelper.create_aw_field_config(
                self.id_width, self.addr_width, self.user_width,
                self.nsaid_width, self.mpam_width, self.mecid_width,
                self.atop_width, self.tagop_width, self.tag_width,
                self.data_width
            ),
            pkt_prefix="aw",
            multi_sig=self.multi_sig,
            protocol_type='axi5_aw_slave',
            log=log,
        )

        # W Channel - Slave drives wready
        self.w_channel = GAXISlave(
            dut=dut,
            title=f"W_Slave{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI5FieldConfigHelper.create_w_field_config(
                self.data_width, self.user_width, self.tag_width
            ),
            pkt_prefix="w",
            multi_sig=self.multi_sig,
            protocol_type='axi5_w_slave',
            log=log,
        )

        # B Channel - Master drives responses
        self.b_channel = GAXIMaster(
            dut=dut,
            title=f"B_Master{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI5FieldConfigHelper.create_b_field_config(
                self.id_width, self.user_width, self.tag_width, self.data_width
            ),
            pkt_prefix="b",
            multi_sig=self.multi_sig,
            protocol_type='axi5_b_master',
            log=log,
        )

        # Set up callbacks
        self.aw_channel.add_callback(self._aw_callback)
        self.w_channel.add_callback(self._w_callback)

        # Transaction tracking
        self.pending_transactions = {}
        self.orphaned_w_packets = []
        self.w_transaction_queue = []
        self.completion_locks = {}

        if self.log:
            mode_str = "OOO mode ENABLED" if self.enable_ooo else "In-order mode"
            self.log.info(f"AXI5SlaveWrite initialized: {mode_str}")

    def _aw_callback(self, aw_packet):
        """Handle AW packet reception."""
        transaction_id = getattr(aw_packet, 'id', 0)
        burst_len = getattr(aw_packet, 'len', 0) + 1
        addr = getattr(aw_packet, 'addr', 0)

        # Track AXI5-specific fields
        atop = getattr(aw_packet, 'atop', 0)
        tagop = getattr(aw_packet, 'tagop', 0)

        # Assign sequence number
        txn_sequence = self.ooo_transaction_sequence
        self.ooo_transaction_sequence += 1
        if self.enable_ooo:
            self.ooo_transaction_metadata[txn_sequence] = {
                'id': transaction_id,
                'addr': addr,
                'atop': atop,
            }

        if transaction_id not in self.pending_transactions:
            self.pending_transactions[transaction_id] = []

        self.pending_transactions[transaction_id].append({
            'aw_packet': aw_packet,
            'w_packets': [],
            'expected_beats': burst_len,
            'complete': False,
            'sequence': txn_sequence,
            'atop': atop,
            'tagop': tagop,
        })

        if self.log:
            self.log.debug(
                f"AXI5SlaveWrite: AW received - id={transaction_id}, "
                f"addr=0x{addr:08X}, atop={atop}, tagop={tagop}"
            )

        self._match_orphaned_w_packets()

    def _w_callback(self, w_packet):
        """Handle W packet reception."""
        is_last = getattr(w_packet, 'last', 0)
        data_val = getattr(w_packet, 'data', 0)
        poison = getattr(w_packet, 'poison', 0)

        if self.log:
            self.log.debug(
                f"AXI5SlaveWrite: W received - data=0x{data_val:08X}, "
                f"last={is_last}, poison={poison}"
            )

        # Handle W-before-AW case
        if not self.pending_transactions:
            self.orphaned_w_packets.append(w_packet)
            if is_last:
                self.w_transaction_queue.append(self.orphaned_w_packets.copy())
                self.orphaned_w_packets.clear()
            return

        # Find matching transaction
        transaction_id = None
        min_sequence = None
        for tid in self.pending_transactions:
            for txn in self.pending_transactions[tid]:
                if not txn['complete']:
                    txn_seq = txn.get('sequence', float('inf'))
                    if min_sequence is None or txn_seq < min_sequence:
                        min_sequence = txn_seq
                        transaction_id = tid
                    break

        if transaction_id is not None and transaction_id in self.pending_transactions:
            transaction_list = self.pending_transactions[transaction_id]
            transaction = None
            for txn in transaction_list:
                if not txn['complete']:
                    transaction = txn
                    break

            if transaction:
                transaction['w_packets'].append(w_packet)

                # Check for poison
                if poison:
                    transaction['has_poison'] = True

                if is_last or len(transaction['w_packets']) >= transaction['expected_beats']:
                    transaction['complete'] = True
                    if self.enable_ooo:
                        delay_cycles = self._calculate_ooo_delay(transaction_id)
                        cocotb.start_soon(
                            self._complete_write_transaction_delayed(transaction_id, delay_cycles)
                        )
                    else:
                        cocotb.start_soon(self._complete_write_transaction(transaction_id))

    def _match_orphaned_w_packets(self):
        """Match orphaned W packets to AW transactions."""
        if not self.w_transaction_queue and not self.orphaned_w_packets:
            return

        for aw_id, aw_transaction_list in self.pending_transactions.items():
            for aw_transaction in aw_transaction_list:
                if aw_transaction['complete']:
                    continue

                if self.w_transaction_queue:
                    w_burst = self.w_transaction_queue.pop(0)
                    aw_transaction['w_packets'] = w_burst
                    aw_transaction['complete'] = True
                    cocotb.start_soon(self._complete_write_transaction(aw_id))
                    return
                elif self.orphaned_w_packets:
                    aw_transaction['w_packets'] = self.orphaned_w_packets.copy()
                    self.orphaned_w_packets.clear()
                    return

    def _calculate_ooo_delay(self, transaction_id):
        """Calculate delay for OOO response."""
        if transaction_id not in self.pending_transactions:
            return 1

        txn_list = self.pending_transactions[transaction_id]
        if not txn_list:
            return 1

        txn = txn_list[0]
        txn_sequence = txn.get('sequence')
        if txn_sequence is None:
            return 1

        txn_meta = self.ooo_transaction_metadata.get(txn_sequence, {})
        txn_id = txn_meta.get('id', transaction_id)

        # Check for blocking same-ID transactions
        last_completed = self.ooo_last_completed_seq.get(txn_id, -1)
        blocking_sequences = [
            seq for seq, meta in self.ooo_transaction_metadata.items()
            if meta['id'] == txn_id and seq < txn_sequence and seq > last_completed
        ]

        if blocking_sequences:
            return 100

        mode = self.ooo_config.get('mode', 'random')
        if mode == 'random':
            min_delay = self.ooo_config.get('min_delay_cycles', 1)
            max_delay = self.ooo_config.get('max_delay_cycles', 50)
            base_delay = random.randint(min_delay, max_delay)

            if random.random() < self.ooo_config.get('reorder_probability', 0.3):
                return base_delay + random.randint(20, 50)
            return base_delay

        return 1

    async def _complete_write_transaction_delayed(self, transaction_id, delay_cycles):
        """Complete write transaction after delay (OOO mode)."""
        for _ in range(delay_cycles):
            await RisingEdge(self.clock)
        await self._complete_write_transaction(transaction_id)

    async def _complete_write_transaction(self, transaction_id):
        """Complete write transaction and send B response."""
        if transaction_id not in self.completion_locks:
            self.completion_locks[transaction_id] = asyncio.Lock()

        async with self.completion_locks[transaction_id]:
            if transaction_id not in self.pending_transactions:
                return

            transaction_list = self.pending_transactions[transaction_id]
            if not transaction_list:
                return

            transaction = None
            for txn in transaction_list:
                if txn['complete'] and not txn.get('completing', False):
                    transaction = txn
                    break

            if transaction is None:
                return

            transaction['completing'] = True

        # Update OOO tracking
        if self.enable_ooo:
            txn_sequence = transaction.get('sequence')
            if txn_sequence is not None:
                txn_meta = self.ooo_transaction_metadata.get(txn_sequence, {})
                txn_id = txn_meta.get('id', transaction_id)
                self.ooo_last_completed_seq[txn_id] = txn_sequence

        aw_packet = transaction['aw_packet']
        w_packets = transaction['w_packets']

        try:
            base_addr = getattr(aw_packet, 'addr', 0)
            size_encoding = getattr(aw_packet, 'size', 2)
            bytes_per_beat = 1 << size_encoding
            aw_trace = getattr(aw_packet, 'trace', 0)
            aw_tagop = getattr(aw_packet, 'tagop', 0)
            aw_atop = getattr(aw_packet, 'atop', 0)

            # Write data to memory if available
            if self.memory_model:
                for i, w_packet in enumerate(w_packets):
                    addr = base_addr + (i * bytes_per_beat)
                    memory_offset = addr - self.base_addr
                    data = getattr(w_packet, 'data', 0)
                    strb = getattr(w_packet, 'strb', 0xF)

                    try:
                        data_bytes = self.memory_model.integer_to_bytearray(data, bytes_per_beat)
                        self.memory_model.write(memory_offset, data_bytes, strb)
                    except Exception as mem_error:
                        if self.log:
                            self.log.warning(f"Memory write failed: {mem_error}")

            # Add response delay
            if self.response_delay_cycles > 0:
                for _ in range(self.response_delay_cycles):
                    await RisingEdge(self.clock)

            if transaction_id not in self.pending_transactions:
                return

            # Determine tag match result based on tagop
            tagmatch = 0
            if aw_tagop != 0:
                tagmatch = 1  # Simple simulation

            # Send B response with AXI5 fields
            b_packet = self.b_channel.create_packet(
                id=transaction_id,
                resp=0,
                trace=aw_trace,
                tag=0,
                tagmatch=tagmatch,
            )

            await self.b_channel.send(b_packet)

            if self.log:
                self.log.debug(
                    f"AXI5SlaveWrite: B response sent - id={transaction_id}, "
                    f"addr=0x{base_addr:08X}, beats={len(w_packets)}"
                )

        except Exception as e:
            if self.log:
                self.log.error(f"AXI5SlaveWrite: Error completing transaction: {e}")
        finally:
            if transaction_id in self.pending_transactions:
                transaction_list = self.pending_transactions[transaction_id]
                if transaction in transaction_list:
                    transaction_list.remove(transaction)
                if not transaction_list:
                    del self.pending_transactions[transaction_id]
