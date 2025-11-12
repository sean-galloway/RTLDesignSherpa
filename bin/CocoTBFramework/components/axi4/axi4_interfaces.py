# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI4MasterRead
# Purpose: AXI4 Interface Classes - Enhanced with Integrated Compliance Checking
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Interface Classes - Enhanced with Integrated Compliance Checking

MODIFICATION: Added seamless compliance checking integration to all AXI4 interfaces
without changing any existing APIs or requiring testbench modifications.

The compliance checker is automatically enabled when AXI4_COMPLIANCE_CHECK=1 is set
and silently disabled otherwise, maintaining full backward compatibility.
"""

import asyncio
import random
from typing import List, Dict, Any, Optional, Union

from cocotb.triggers import RisingEdge
import cocotb

# Import GAXI components and field configs
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.axi4.axi4_field_configs import AXI4FieldConfigHelper
from CocoTBFramework.components.axi4.axi4_packet import AXI4Packet
from CocoTBFramework.components.axi4.axi4_compliance_checker import AXI4ComplianceChecker


class AXI4MasterRead:
    """
    AXI4 Master Read Interface - Enhanced with integrated compliance checking.

    Manages read address requests (AR) and read data responses (R).
    
    ENHANCEMENT: Automatically includes compliance checking when enabled via environment.
    """

    def __init__(self, dut, clock, prefix="", log=None, ifc_name="", **kwargs):
        """Initialize AXI4 Master Read interface with optional compliance checking."""
        self.super_debug = True
        self.clock = clock
        self.log = log
        self.ifc_name = f"_{ifc_name}" if ifc_name else ""

        # Extract configuration parameters
        self.data_width = kwargs.get('data_width', 32)
        self.id_width = kwargs.get('id_width', 8)
        self.addr_width = kwargs.get('addr_width', 32)
        self.user_width = kwargs.get('user_width', 1)
        self.multi_sig = kwargs.get('multi_sig', True)  # AXI4 uses individual signals by default

        # AR Channel (Address Read) - Master drives
        self.ar_channel = GAXIMaster(
            dut=dut,
            title=f"AR_Master{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI4FieldConfigHelper.create_ar_field_config(
                self.id_width, self.addr_width, self.user_width
            ),
            pkt_prefix="ar",
            multi_sig=self.multi_sig,
            protocol_type='axi4_ar_master',  # Use AXI4-specific patterns
            super_debug=self.super_debug,
            log=log
        )

        # R Channel needs to drive rready - use GAXISlave
        self.r_channel = GAXISlave(
            dut=dut,
            title=f"R_Slave{self.ifc_name}",  # Slave role - drives rready, receives R data
            prefix=prefix,
            clock=clock,
            field_config=AXI4FieldConfigHelper.create_r_field_config(
                self.id_width, self.data_width, self.user_width
            ),
            pkt_prefix="r",
            multi_sig=self.multi_sig,
            protocol_type='axi4_r_slave',  # Use AXI4-specific patterns
            super_debug=self.super_debug,
            log=log
        )

        # Store parameters for transaction methods
        # Large timeout to handle worst-case backpressure through skid buffers
        self.timeout_cycles = kwargs.get('timeout_cycles', 5000)

        # ENHANCEMENT: Integrate compliance checker automatically
        self.compliance_checker = AXI4ComplianceChecker.create_if_enabled(
            dut=dut,
            clock=clock,
            prefix=prefix,
            log=log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            user_width=self.user_width,
            multi_sig=self.multi_sig
        )
        
        if self.compliance_checker and log:
            log.info("AXI4MasterRead: Compliance checking enabled")

    async def read_transaction(self, address: int, burst_len: int = 1, **transaction_kwargs) -> List[int]:
        """
        High-level read transaction using generic field names.
        UNCHANGED: All existing functionality preserved.
        """
        # Create AR packet with GENERIC field names
        ar_packet = self.ar_channel.create_packet(
            addr=address,
            len=burst_len - 1,
            id=transaction_kwargs.get('id', 0),
            size=transaction_kwargs.get('size', 2),
            burst=transaction_kwargs.get('burst_type', 1),
            lock=transaction_kwargs.get('lock', 0),
            cache=transaction_kwargs.get('cache', 0),
            prot=transaction_kwargs.get('prot', 0),
            qos=transaction_kwargs.get('qos', 0),
            region=transaction_kwargs.get('region', 0),
            **{k: v for k, v in transaction_kwargs.items()
            if k in ['user'] and hasattr(ar_packet, k)}
        )

        # Record initial queue state
        initial_count = len(self.r_channel._recvQ)
        expected_count = initial_count + burst_len

        # Send read address
        await self.ar_channel.send(ar_packet)

        # Wait for R responses using clock edges
        cycles_waited = 0

        while len(self.r_channel._recvQ) < expected_count:
            await RisingEdge(self.clock)
            cycles_waited += 1

            if cycles_waited > self.timeout_cycles:
                received = len(self.r_channel._recvQ) - initial_count
                raise TimeoutError(f"AXI4 read timeout after {cycles_waited} cycles: "
                                    f"got {received} of {burst_len} responses at address 0x{address:08X}")

        # Extract data from new packets using GENERIC field names
        read_data = []
        for i in range(burst_len):
            packet = self.r_channel._recvQ[initial_count + i]
            data_value = getattr(packet, 'data', 0)
            read_data.append(data_value)

            # Check for errors using GENERIC field names
            if hasattr(packet, 'resp') and packet.resp != 0:
                resp_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
                resp_name = resp_names.get(packet.resp, 'UNKNOWN')
                raise RuntimeError(f"AXI4 read error: {resp_name} (0x{packet.resp:X})")

        return read_data

    async def single_read(self, address: int, **kwargs) -> int:
        """Convenience method for single read. UNCHANGED."""
        data_list = await self.read_transaction(address, burst_len=1, **kwargs)
        return data_list[0]

    def create_ar_packet(self, **kwargs) -> AXI4Packet:
        """Create AR packet with current configuration using generic field names. UNCHANGED."""
        return self.ar_channel.create_packet(**kwargs)

    def get_compliance_report(self) -> Optional[Dict[str, Any]]:
        """
        ENHANCEMENT: Get compliance report if compliance checking is enabled.
        
        Returns:
            Compliance report dictionary or None if compliance checking disabled
        """
        if self.compliance_checker:
            return self.compliance_checker.get_compliance_report()
        return None

    def print_compliance_report(self):
        """ENHANCEMENT: Print compliance report if compliance checking is enabled."""
        if self.compliance_checker:
            self.compliance_checker.print_compliance_report()
        elif self.log:
            self.log.debug("AXI4MasterRead: Compliance checking is disabled")


class AXI4MasterWrite:
    """
    AXI4 Master Write Interface - Enhanced with integrated compliance checking.

    Manages write address requests (AW), write data (W), and write responses (B).
    
    ENHANCEMENT: Automatically includes compliance checking when enabled via environment.
    """

    def __init__(self, dut, clock, prefix="", log=None, ifc_name="", **kwargs):
        """Initialize AXI4 Master Write interface with optional compliance checking."""
        self.clock = clock
        self.log = log
        self.ifc_name = f"_{ifc_name}" if ifc_name else ""

        # Extract configuration parameters
        self.data_width = kwargs.get('data_width', 32)
        self.id_width = kwargs.get('id_width', 8)
        self.addr_width = kwargs.get('addr_width', 32)
        self.user_width = kwargs.get('user_width', 1)
        self.multi_sig = kwargs.get('multi_sig', True)  # AXI4 uses individual signals by default

        # AW Channel (Address Write) - Master drives
        self.aw_channel = GAXIMaster(
            dut=dut,
            title=f"AW_Master{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI4FieldConfigHelper.create_aw_field_config(
                self.id_width, self.addr_width, self.user_width
            ),
            pkt_prefix="aw",
            multi_sig=self.multi_sig,
            protocol_type='axi4_aw_master',  # Use AXI4-specific patterns
            log=log
        )

        # W Channel (Write Data) - Master drives
        self.w_channel = GAXIMaster(
            dut=dut,
            title=f"W_Master{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI4FieldConfigHelper.create_w_field_config(
                self.data_width, self.user_width
            ),
            pkt_prefix="w",
            multi_sig=self.multi_sig,
            protocol_type='axi4_w_master',  # Use AXI4-specific patterns
            log=log
        )

        # B Channel (Write Response) - Slave receives responses
        self.b_channel = GAXISlave(
            dut=dut,
            title=f"B_Slave{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI4FieldConfigHelper.create_b_field_config(
                self.id_width, self.user_width
            ),
            pkt_prefix="b",
            multi_sig=self.multi_sig,
            protocol_type='axi4_b_slave',  # Use AXI4-specific patterns
            log=log
        )

        # Store parameters for transaction methods
        # Large timeout to handle worst-case backpressure through skid buffers
        self.timeout_cycles = kwargs.get('timeout_cycles', 5000)

        # ENHANCEMENT: Integrate compliance checker automatically
        self.compliance_checker = AXI4ComplianceChecker.create_if_enabled(
            dut=dut,
            clock=clock,
            prefix=prefix,
            log=log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            user_width=self.user_width,
            multi_sig=self.multi_sig
        )
        
        if self.compliance_checker and log:
            log.info("AXI4MasterWrite: Compliance checking enabled")

    async def write_transaction(self, address: int, data: Union[int, List[int]],
                            burst_len: Optional[int] = None, **transaction_kwargs) -> Dict[str, Any]:
        """
        High-level write transaction using generic field names.
        UNCHANGED: All existing functionality preserved.
        """
        # Initialize aw_packet to None to prevent UnboundLocalError
        aw_packet = None
        
        try:
            # Handle data formatting
            if isinstance(data, list):
                data_list = data
                if burst_len is None:
                    burst_len = len(data_list)
                else:
                    data_list = data_list[:burst_len]  # Truncate if needed
            else:
                if burst_len is None:
                    burst_len = 1
                data_list = [data] * burst_len

            # Create AW packet with GENERIC field names
            aw_packet = self.aw_channel.create_packet(
                addr=address,
                len=burst_len - 1,
                id=transaction_kwargs.get('id', 0),
                size=transaction_kwargs.get('size', 2),
                burst=transaction_kwargs.get('burst_type', 1),
                lock=transaction_kwargs.get('lock', 0),
                cache=transaction_kwargs.get('cache', 0),
                prot=transaction_kwargs.get('prot', 0),
                qos=transaction_kwargs.get('qos', 0),
                region=transaction_kwargs.get('region', 0),
                **{k: v for k, v in transaction_kwargs.items()
                if k in ['user'] and hasattr(aw_packet, k)}
            )

            # Send address
            await self.aw_channel.send(aw_packet)

            # Send data beats using GENERIC field names
            strb_width = self.data_width // 8
            default_strb = (1 << strb_width) - 1  # All bytes enabled

            for i, data_value in enumerate(data_list):
                w_packet = self.w_channel.create_packet(
                    data=data_value,
                    last=1 if i == len(data_list) - 1 else 0,
                    strb=transaction_kwargs.get('strb', default_strb),
                    **{k: v for k, v in transaction_kwargs.items() if k.startswith('w')}
                )
                await self.w_channel.send(w_packet)

            # Wait for write response using _recvQ pattern (same as read master)
            initial_b_count = len(self.b_channel._recvQ)
            expected_b_count = initial_b_count + 1  # Expecting 1 B response

            cycles_waited = 0
            while len(self.b_channel._recvQ) < expected_b_count:
                await RisingEdge(self.clock)
                cycles_waited += 1

                if cycles_waited > self.timeout_cycles:
                    raise TimeoutError(f"AXI4 write timeout after {cycles_waited} cycles: "
                                        f"waiting for B response at address 0x{address:08X}")

            # Get the B response packet
            b_response = self.b_channel._recvQ[initial_b_count]

            # Check for errors using GENERIC field names
            if hasattr(b_response, 'resp') and b_response.resp != 0:
                resp_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
                resp_name = resp_names.get(b_response.resp, 'UNKNOWN')
                raise RuntimeError(f"AXI4 write error: {resp_name} (0x{b_response.resp:X})")

            return {
                'success': True,
                'response': b_response.resp if hasattr(b_response, 'resp') else 0,
                'id': b_response.id if hasattr(b_response, 'id') else 0
            }

        except Exception as e:
            # Log the error with details about what we tried to do
            if self.log:
                addr_str = f"addr=0x{address:08X}" if address is not None else "addr=None"
                data_str = f"data=0x{data:08X}" if isinstance(data, int) else f"data={type(data).__name__}"
                packet_str = f"aw_packet={'created' if aw_packet is not None else 'not_created'}"
                self.log.error(f"AXI4 write transaction failed: {addr_str}, {data_str}, {packet_str}, error: {str(e)}")
            
            # Return failure result
            return {
                'success': False,
                'error': str(e),
                'response': None,
                'id': None
            }

    async def single_write(self, address: int, data: int, **kwargs) -> Dict[str, Any]:
        """Convenience method for single write. UNCHANGED."""
        return await self.write_transaction(address, data, burst_len=1, **kwargs)

    def get_compliance_report(self) -> Optional[Dict[str, Any]]:
        """
        ENHANCEMENT: Get compliance report if compliance checking is enabled.
        
        Returns:
            Compliance report dictionary or None if compliance checking disabled
        """
        if self.compliance_checker:
            return self.compliance_checker.get_compliance_report()
        return None

    def print_compliance_report(self):
        """ENHANCEMENT: Print compliance report if compliance checking is enabled."""
        if self.compliance_checker:
            self.compliance_checker.print_compliance_report()
        elif self.log:
            self.log.debug("AXI4MasterWrite: Compliance checking is disabled")


class AXI4SlaveRead:
    """
    AXI4 Slave Read Interface - Enhanced with integrated compliance checking.

    Uses GAXISlave for AR (drives arready) with callback to GAXIMaster for R (drives responses).

    ENHANCEMENT: Automatically includes compliance checking when enabled via environment.
    """

    def __init__(self, dut, clock, prefix="", log=None, ifc_name="", **kwargs):
        """Initialize AXI4 Slave Read interface with proper architecture and compliance checking."""
        self.clock = clock
        self.log = log
        self.ifc_name = f"_{ifc_name}" if ifc_name else ""

        # Extract configuration parameters
        self.data_width = kwargs.get('data_width', 32)
        self.id_width = kwargs.get('id_width', 8)
        self.addr_width = kwargs.get('addr_width', 32)
        self.user_width = kwargs.get('user_width', 1)
        self.multi_sig = kwargs.get('multi_sig', True)  # AXI4 uses individual signals by default

        # Store memory model if provided
        self.memory_model = kwargs.get('memory_model')

        # Base address offset (for memory-mapped slaves)
        # If provided, incoming AXI addresses will have base_addr subtracted
        # before accessing memory_model (which expects 0-based offsets)
        self.base_addr = kwargs.get('base_addr', 0)

        # Response configuration
        self.response_delay_cycles = kwargs.get('response_delay', 1)

        # Out-of-order response configuration
        self.enable_ooo = kwargs.get('enable_ooo', False)
        self.ooo_config = kwargs.get('ooo_config', {
            'mode': 'random',                # 'random' or 'deterministic'
            'reorder_probability': 0.3,      # Probability to delay a transaction
            'min_delay_cycles': 1,           # Minimum delay before response
            'max_delay_cycles': 50,          # Maximum delay before response
            'pattern': None,                 # For deterministic mode: [sequence_order]
        })

        # OOO state tracking (AXI4 compliant: same ID must stay in order)
        self.ooo_transaction_sequence = 0    # Global transaction counter
        self.ooo_transaction_metadata = {}   # {txn_seq: {'id': id, 'addr': addr}}
        self.ooo_last_completed_seq = {}     # {id: last_completed_sequence}

        # In-order mode serialization: ensure same-ID transactions complete serially
        self.in_order_active = {}            # {id: bool} - track if ID is actively responding
        self.in_order_queue = {}             # {id: [ar_packets]} - queue of waiting requests per ID

        # AR Channel (Address Read) - GAXISlave drives arready and receives AR requests
        self.ar_channel = GAXISlave(
            dut=dut,
            title=f"AR_Slave{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI4FieldConfigHelper.create_ar_field_config(
                self.id_width, self.addr_width, self.user_width
            ),
            pkt_prefix="ar",
            multi_sig=self.multi_sig,
            protocol_type='axi4_ar_slave',  # Use AXI4-specific patterns
            log=log,
        )

        # R Channel (Read Data + Response) - GAXIMaster drives R responses
        self.r_channel = GAXIMaster(
            dut=dut,
            title=f"R_Master{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI4FieldConfigHelper.create_r_field_config(
                self.id_width, self.data_width, self.user_width
            ),
            pkt_prefix="r",
            multi_sig=self.multi_sig,
            protocol_type='axi4_r_master',  # Use AXI4-specific patterns
            log=log,
            super_debug=True,
        )

        # CRITICAL: Set up callback from AR slave to trigger R responses
        self.ar_channel.add_callback(self._ar_callback)

        # ENHANCEMENT: Integrate compliance checker automatically
        self.compliance_checker = AXI4ComplianceChecker.create_if_enabled(
            dut=dut,
            clock=clock,
            prefix=prefix,
            log=log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            user_width=self.user_width,
            multi_sig=self.multi_sig
        )

        if self.log:
            mode_str = "OOO mode ENABLED" if self.enable_ooo else "In-order mode"
            if self.enable_ooo:
                mode_str += f" (reorder_prob={self.ooo_config.get('reorder_probability', 0.3)}, " \
                        f"delay=[{self.ooo_config.get('min_delay_cycles', 1)}, " \
                        f"{self.ooo_config.get('max_delay_cycles', 50)}])"
            self.log.info(f"AXI4SlaveRead initialized: AR callback linked to R master, {mode_str}")
            if self.compliance_checker:
                self.log.info("AXI4SlaveRead: Compliance checking enabled")

    def _ar_callback(self, ar_packet):
        """
        Callback triggered when AR slave receives a packet.
        Supports both in-order and OOO response modes. Tracks sequence for AXI4 compliance.
        """
        transaction_id = getattr(ar_packet, 'id', 0)
        addr = getattr(ar_packet, 'addr', 0)

        # Assign sequence number if OOO enabled (for AXI4 same-ID ordering)
        if self.enable_ooo:
            txn_sequence = self.ooo_transaction_sequence
            self.ooo_transaction_sequence += 1
            self.ooo_transaction_metadata[txn_sequence] = {
                'id': transaction_id,
                'addr': addr
            }
            # Store sequence in packet for later retrieval
            ar_packet._ooo_sequence = txn_sequence
            seq_str = f", seq={txn_sequence}"
        else:
            seq_str = ""

        if self.log:
            self.log.debug(f"AXI4SlaveRead: AR callback triggered - "
                        f"addr=0x{addr:08X}, id={transaction_id}{seq_str}")

        # Schedule R response generation with appropriate delay
        if self.enable_ooo:
            delay_cycles = self._calculate_ooo_delay_read(ar_packet)
            if self.log:
                self.log.debug(f"AXI4SlaveRead: Scheduling OOO completion for "
                            f"txn {transaction_id} after {delay_cycles} cycles")
            cocotb.start_soon(self._generate_read_response_delayed(ar_packet, delay_cycles))
        else:
            # In-order mode: serialize responses for same ID using lock
            cocotb.start_soon(self._generate_read_response_serialized(ar_packet))

    def _calculate_ooo_delay_read(self, ar_packet):
        """
        Calculate delay cycles for OOO read response (AXI4 compliant: same ID must stay in order).

        Args:
            ar_packet: AR packet with transaction details

        Returns:
            Delay in clock cycles before sending response
        """
        # Get transaction metadata from packet
        txn_sequence = getattr(ar_packet, '_ooo_sequence', None)
        if txn_sequence is None:
            return 1  # OOO not enabled

        transaction_id = getattr(ar_packet, 'id', 0)
        txn_meta = self.ooo_transaction_metadata.get(txn_sequence, {})
        txn_id = txn_meta.get('id', transaction_id)

        # AXI4 COMPLIANCE: Check if previous same-ID transactions have completed
        last_completed = self.ooo_last_completed_seq.get(txn_id, -1)

        # Find all pending same-ID transactions with lower sequence numbers
        blocking_sequences = []
        for seq, meta in self.ooo_transaction_metadata.items():
            if meta['id'] == txn_id and seq < txn_sequence and seq > last_completed:
                blocking_sequences.append(seq)

        # If there are blocking transactions, we MUST wait
        if blocking_sequences:
            if self.log:
                self.log.debug(f"AXI4SlaveRead: Transaction seq={txn_sequence} id={txn_id} "
                            f"blocked by {len(blocking_sequences)} earlier same-ID transactions")
            return 100  # Long delay to let earlier transactions complete

        mode = self.ooo_config.get('mode', 'random')

        if mode == 'deterministic':
            # Pattern specifies SEQUENCE order (not ID order!)
            pattern = self.ooo_config.get('pattern', [])
            if pattern and txn_sequence < len(pattern):
                try:
                    target_position = pattern.index(txn_sequence)
                    current_position = len([s for s in self.ooo_last_completed_seq.values() if s >= 0])

                    if target_position > current_position:
                        delay = (target_position - current_position) * 20
                    else:
                        delay = 1

                    if self.log:
                        self.log.debug(f"AXI4SlaveRead: Deterministic OOO seq={txn_sequence} "
                                    f"id={txn_id}, pattern_pos={target_position}, delay={delay}")

                    return delay
                except ValueError:
                    return self.ooo_config.get('min_delay_cycles', 1)
            else:
                return self.ooo_config.get('min_delay_cycles', 1)

        elif mode == 'random':
            # Random delay within range (same-ID ordering already enforced above)
            min_delay = self.ooo_config.get('min_delay_cycles', 1)
            max_delay = self.ooo_config.get('max_delay_cycles', 50)
            base_delay = random.randint(min_delay, max_delay)

            reorder_prob = self.ooo_config.get('reorder_probability', 0.3)
            if random.random() < reorder_prob:
                extra_delay = random.randint(20, 50)
                return base_delay + extra_delay
            else:
                return base_delay

        else:
            return 1

    async def _generate_read_response_serialized(self, ar_packet):
        """
        Generate read response with serialization for in-order mode (enable_ooo=False).
        Ensures that all responses for the same ID complete serially using queue-based serialization.

        Args:
            ar_packet: AR packet with transaction details
        """
        from cocotb.triggers import RisingEdge
        transaction_id = getattr(ar_packet, 'id', 0)

        # Initialize queue and active flag for this ID if needed
        if transaction_id not in self.in_order_queue:
            self.in_order_queue[transaction_id] = []
            self.in_order_active[transaction_id] = False

        # Add packet to queue
        self.in_order_queue[transaction_id].append(ar_packet)

        # If another response for this ID is already active, just return (it will process the queue)
        if self.in_order_active[transaction_id]:
            if self.log:
                self.log.debug(f"AXI4SlaveRead: Queued request for id={transaction_id} "
                            f"(queue_len={len(self.in_order_queue[transaction_id])})")
            return

        # Mark this ID as active
        self.in_order_active[transaction_id] = True

        # Process all queued packets for this ID serially
        while self.in_order_queue[transaction_id]:
            packet = self.in_order_queue[transaction_id].pop(0)

            if self.log:
                self.log.debug(f"AXI4SlaveRead: Starting serialized response for id={transaction_id} "
                            f"(remaining={len(self.in_order_queue[transaction_id])})")

            # Generate response
            await self._generate_read_response(packet)

            if self.log:
                self.log.debug(f"AXI4SlaveRead: Completed serialized response for id={transaction_id}")

        # Mark this ID as no longer active
        self.in_order_active[transaction_id] = False

    async def _generate_read_response_delayed(self, ar_packet, delay_cycles):
        """
        Generate read response after specified delay (for OOO mode).

        Args:
            ar_packet: AR packet with transaction details
            delay_cycles: Number of clock cycles to wait before completion
        """
        # Wait for specified delay
        for _ in range(delay_cycles):
            await RisingEdge(self.clock)

        transaction_id = getattr(ar_packet, 'id', 0)
        if self.log:
            self.log.debug(f"AXI4SlaveRead: OOO delay complete for txn {transaction_id}, sending R response")

        # Now generate the response normally
        await self._generate_read_response(ar_packet)

    async def _generate_read_response(self, ar_packet):
        """Generate R response for an AR request using generic field names. UNCHANGED."""
        try:
            # Extract AR packet fields using GENERIC field names
            address = getattr(ar_packet, 'addr', 0)
            burst_len = getattr(ar_packet, 'len', 0) + 1
            packet_id = getattr(ar_packet, 'id', 0)
            size_encoding = getattr(ar_packet, 'size', 2)
            bytes_per_beat = 1 << size_encoding

            if self.log:
                self.log.debug(f"AXI4SlaveRead: Generating {burst_len} beat response for "
                            f"addr=0x{address:08X}, id={packet_id}")

            # Add configurable delay
            for _ in range(self.response_delay_cycles):
                await RisingEdge(self.clock)

            # Generate response data beats
            # PERFORMANCE FIX: Generate all beats synchronously, queue directly to transmit_queue,
            # then trigger pipeline once at end. This eliminates per-beat async overhead.
            r_packets = []
            for i in range(burst_len):
                current_addr = address + (i * bytes_per_beat)

                # Read from memory model if available
                if self.memory_model:
                    try:
                        # Apply base address offset before accessing memory model
                        # (RTL sends absolute addresses, memory model expects 0-based offsets)
                        memory_offset = current_addr - self.base_addr

                        # Read bytes from memory model
                        data_bytes = self.memory_model.read(memory_offset, bytes_per_beat)
                        # Convert to integer using memory model's utility
                        data = self.memory_model.bytearray_to_integer(data_bytes)

                        if self.log:
                            self.log.debug(f"AXI4SlaveRead: Read from memory - "
                                        f"addr=0x{current_addr:08X}, data=0x{data:08X}")
                    except Exception as e:
                        if self.log:
                            self.log.warning(f"Memory read failed at 0x{current_addr:08X}: {e}")
                        data = current_addr  # Fallback pattern
                else:
                    # Simple address-based pattern for testing
                    data = current_addr

                # Create R response packet using GENERIC field names
                is_last = (i == burst_len - 1)
                r_packet = self.r_channel.create_packet(
                    id=packet_id,
                    data=data,
                    resp=0,
                    last=1 if is_last else 0
                )

                r_packets.append(r_packet)

            # PERFORMANCE: Add all beats to queue synchronously (no per-beat await overhead)
            # This keeps the queue full and prevents the pipeline from going idle
            for r_packet in r_packets:
                self.r_channel.transmit_queue.append(r_packet)

            if self.log:
                self.log.debug(f"AXI4SlaveRead: Queued {len(r_packets)} beats for burst (id={packet_id})")

            # Start pipeline if not already running
            # Note: if pipeline is already active, it will process the newly queued beats
            if not self.r_channel.transmit_coroutine:
                if self.log:
                    self.log.debug(f"AXI4SlaveRead: Starting transmit pipeline for id={packet_id}")
                self.r_channel.transmit_coroutine = cocotb.start_soon(self.r_channel._transmit_pipeline())

            # Update OOO tracking: mark this transaction as completed after all beats sent
            if self.enable_ooo:
                txn_sequence = getattr(ar_packet, '_ooo_sequence', None)
                if txn_sequence is not None:
                    txn_meta = self.ooo_transaction_metadata.get(txn_sequence, {})
                    txn_id = txn_meta.get('id', packet_id)
                    # Record this as the last completed sequence for this ID
                    self.ooo_last_completed_seq[txn_id] = txn_sequence
                    if self.log:
                        self.log.debug(f"AXI4SlaveRead: Marked txn seq={txn_sequence} "
                                    f"(id={txn_id}) as completed")

        except Exception as e:
            if self.log:
                self.log.error(f"AXI4SlaveRead: Error generating response: {e}")

    def get_compliance_report(self) -> Optional[Dict[str, Any]]:
        """
        ENHANCEMENT: Get compliance report if compliance checking is enabled.
        
        Returns:
            Compliance report dictionary or None if compliance checking disabled
        """
        if self.compliance_checker:
            return self.compliance_checker.get_compliance_report()
        return None

    def print_compliance_report(self):
        """ENHANCEMENT: Print compliance report if compliance checking is enabled."""
        if self.compliance_checker:
            self.compliance_checker.print_compliance_report()
        elif self.log:
            self.log.debug("AXI4SlaveRead: Compliance checking is disabled")


class AXI4SlaveWrite:
    """
    AXI4 Slave Write Interface - Enhanced with integrated compliance checking.

    Properly handles AXI4 specification requirement that W data can arrive before AW address.
    Uses GAXISlave for AW/W (drives ready signals) with callback to GAXIMaster for B (drives responses).

    ENHANCEMENT: Automatically includes compliance checking when enabled via environment.
    """

    def __init__(self, dut, clock, prefix="", log=None, ifc_name="", **kwargs):
        """Initialize AXI4 Slave Write interface with compliance checking."""
        self.clock = clock
        self.log = log
        self.ifc_name = f"_{ifc_name}" if ifc_name else ""

        # Extract configuration parameters
        self.data_width = kwargs.get('data_width', 32)
        self.id_width = kwargs.get('id_width', 8)
        self.addr_width = kwargs.get('addr_width', 32)
        self.user_width = kwargs.get('user_width', 1)
        self.multi_sig = kwargs.get('multi_sig', True)  # AXI4 uses individual signals by default

        # Store memory model if provided
        self.memory_model = kwargs.get('memory_model')

        # Base address offset (for memory-mapped slaves)
        # If provided, incoming AXI addresses will have base_addr subtracted
        # before accessing memory_model (which expects 0-based offsets)
        self.base_addr = kwargs.get('base_addr', 0)

        # Response configuration
        self.response_delay_cycles = kwargs.get('response_delay', 1)

        # Out-of-order response configuration
        self.enable_ooo = kwargs.get('enable_ooo', False)
        self.ooo_config = kwargs.get('ooo_config', {
            'mode': 'random',                # 'random' or 'deterministic'
            'reorder_probability': 0.3,      # Probability to delay a transaction
            'min_delay_cycles': 1,           # Minimum delay before response
            'max_delay_cycles': 50,          # Maximum delay before response
            'pattern': None,                 # For deterministic mode: [sequence_order]
        })

        # OOO state tracking (AXI4 compliant: same ID must stay in order)
        self.ooo_transaction_sequence = 0    # Global transaction counter
        self.ooo_transaction_metadata = {}   # {txn_seq: {'id': id, 'addr': addr}}
        self.ooo_last_completed_seq = {}     # {id: last_completed_sequence}

        # AW Channel - GAXISlave drives awready and receives AW requests
        self.aw_channel = GAXISlave(
            dut=dut,
            title=f"AW_Slave{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI4FieldConfigHelper.create_aw_field_config(
                self.id_width, self.addr_width, self.user_width
            ),
            pkt_prefix="aw",
            multi_sig=self.multi_sig,
            protocol_type='axi4_aw_slave',  # Use AXI4-specific patterns
            log=log,
        )

        # W Channel - GAXISlave drives wready and receives W data
        self.w_channel = GAXISlave(
            dut=dut,
            title=f"W_Slave{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI4FieldConfigHelper.create_w_field_config(
                self.data_width, self.user_width
            ),
            pkt_prefix="w",
            multi_sig=self.multi_sig,
            protocol_type='axi4_w_slave',  # Use AXI4-specific patterns
            log=log,
        )

        # B Channel - GAXIMaster drives B responses
        self.b_channel = GAXIMaster(
            dut=dut,
            title=f"B_Master{self.ifc_name}",
            prefix=prefix,
            clock=clock,
            field_config=AXI4FieldConfigHelper.create_b_field_config(
                self.id_width, self.user_width
            ),
            pkt_prefix="b",
            multi_sig=self.multi_sig,
            protocol_type='axi4_b_master',  # Use AXI4-specific patterns
            log=log,
        )

        # Set up callbacks
        self.aw_channel.add_callback(self._aw_callback)
        self.w_channel.add_callback(self._w_callback)

        # AXI4-compliant transaction tracking
        # id -> list of transactions (to handle multiple outstanding transactions with same ID)
        # Each transaction: {aw_packet: ..., w_packets: [...], complete: bool, expected_beats: ...}
        self.pending_transactions = {}  # id -> [transaction_list] (FIFO order)

        # AXI4-compliant W-before-AW buffering
        self.orphaned_w_packets = []    # W packets that arrived before corresponding AW
        self.w_transaction_queue = []   # Queue of complete W burst sequences

        # Lock to prevent race condition in transaction completion
        self.completion_locks = {}      # id -> asyncio.Lock

        # ENHANCEMENT: Integrate compliance checker automatically
        self.compliance_checker = AXI4ComplianceChecker.create_if_enabled(
            dut=dut,
            clock=clock,
            prefix=prefix,
            log=log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            user_width=self.user_width,
            multi_sig=self.multi_sig
        )

        if self.log:
            mode_str = "OOO mode ENABLED" if self.enable_ooo else "In-order mode"
            if self.enable_ooo:
                mode_str += f" (reorder_prob={self.ooo_config.get('reorder_probability', 0.3)}, " \
                        f"delay=[{self.ooo_config.get('min_delay_cycles', 1)}, " \
                        f"{self.ooo_config.get('max_delay_cycles', 50)}])"
            self.log.info(f"AXI4SlaveWrite initialized: AW/W callbacks linked to B master with W-before-AW support, {mode_str}")
            if self.compliance_checker:
                self.log.info("AXI4SlaveWrite: Compliance checking enabled")

    def _aw_callback(self, aw_packet):
        """Handle AW packet reception using generic field names. Tracks sequence for AXI4-compliant OOO."""
        transaction_id = getattr(aw_packet, 'id', 0)
        burst_len = getattr(aw_packet, 'len', 0) + 1
        addr = getattr(aw_packet, 'addr', 0)

        # Assign sequence number if OOO enabled (for AXI4 same-ID ordering)
        if self.enable_ooo:
            txn_sequence = self.ooo_transaction_sequence
            self.ooo_transaction_sequence += 1
            self.ooo_transaction_metadata[txn_sequence] = {
                'id': transaction_id,
                'addr': addr
            }
        else:
            txn_sequence = None

        # AXI4-compliant: Allow multiple transactions with same ID (must complete in-order)
        if transaction_id not in self.pending_transactions:
            self.pending_transactions[transaction_id] = []  # Initialize list for this ID

        # Append new transaction to list (FIFO order)
        self.pending_transactions[transaction_id].append({
            'aw_packet': aw_packet,
            'w_packets': [],
            'expected_beats': burst_len,
            'complete': False,
            'sequence': txn_sequence  # For OOO tracking
        })

        if self.log:
            seq_str = f", seq={txn_sequence}" if self.enable_ooo else ""
            self.log.debug(f"AXI4SlaveWrite: AW received - id={transaction_id}, "
                        f"addr=0x{addr:08X}, expected_beats={burst_len}{seq_str}")

        # AXI4-compliant: Check if we have orphaned W packets that can now be matched
        self._match_orphaned_w_packets()

    def _w_callback(self, w_packet):
        """Handle W packet reception - AXI4 compliant W-before-AW handling. UNCHANGED."""
        is_last = getattr(w_packet, 'last', 0)
        data_val = getattr(w_packet, 'data', 0)

        if self.log:
            self.log.debug(f"AXI4SlaveWrite: W received - data=0x{data_val:08X}, last={is_last}")

        # AXI4-compliant: Handle W-before-AW case
        if not self.pending_transactions:
            if self.log:
                self.log.debug("AXI4SlaveWrite: W arrived before AW - buffering (AXI4 compliant)")
            self.orphaned_w_packets.append(w_packet)
            
            # If this is a complete burst (last=1), queue it for later matching
            if is_last:
                # Move all orphaned W packets to transaction queue
                self.w_transaction_queue.append(self.orphaned_w_packets.copy())
                self.orphaned_w_packets.clear()
                if self.log:
                    self.log.debug(f"AXI4SlaveWrite: Complete W burst queued ({len(self.w_transaction_queue[-1])} beats)")
            return

        # Normal case: Match W to existing AW transaction
        # In OOO mode, match based on which transaction is expecting data
        # In FIFO mode, match to first incomplete transaction for this ID

        if self.enable_ooo:
            # OOO mode: Find transaction that needs this W packet
            transaction_id = self._find_matching_transaction_ooo()
        else:
            # FIFO mode: First transaction ID (backward compatible)
            transaction_id = list(self.pending_transactions.keys())[0] if self.pending_transactions else None

        if transaction_id is not None and transaction_id in self.pending_transactions:
            # Find first incomplete transaction in the list for this ID
            transaction_list = self.pending_transactions[transaction_id]
            transaction = None
            for txn in transaction_list:
                if not txn['complete']:
                    transaction = txn
                    break

            if transaction is None:
                if self.log:
                    self.log.warning(f"AXI4SlaveWrite: No incomplete transaction found for id={transaction_id}")
                return

            # Add W packet to this transaction
            transaction['w_packets'].append(w_packet)

            if self.log:
                self.log.debug(f"AXI4SlaveWrite: W matched to txn_id={transaction_id}")

            # Check if transaction is complete
            if len(transaction['w_packets']) >= transaction['expected_beats']:
                transaction['complete'] = True
                if self.log:
                    self.log.debug(f"AXI4SlaveWrite: Transaction {transaction_id} complete")

                # Schedule completion with appropriate delay
                if self.enable_ooo:
                    delay_cycles = self._calculate_ooo_delay(transaction_id)
                    if self.log:
                        self.log.debug(f"AXI4SlaveWrite: Scheduling OOO completion for "
                                    f"txn {transaction_id} after {delay_cycles} cycles")
                    cocotb.start_soon(self._complete_write_transaction_delayed(
                        transaction_id, delay_cycles))
                else:
                    # FIFO mode: immediate completion
                    cocotb.start_soon(self._complete_write_transaction(transaction_id))

    def _match_orphaned_w_packets(self):
        """Match orphaned W packets to newly arrived AW transactions."""
        if not self.w_transaction_queue:
            return

        # Try to match queued W bursts to pending AW transactions
        matched_any = False

        for aw_id, aw_transaction_list in self.pending_transactions.items():
            # Find first incomplete transaction in the list
            for aw_transaction in aw_transaction_list:
                if aw_transaction['complete']:
                    continue

                if self.w_transaction_queue:
                    # Match the first queued W burst to this AW
                    w_burst = self.w_transaction_queue.pop(0)
                    aw_transaction['w_packets'] = w_burst
                    aw_transaction['complete'] = True
                    matched_any = True

                    if self.log:
                        self.log.debug(f"AXI4SlaveWrite: Matched orphaned W burst ({len(w_burst)} beats) to AW id={aw_id}")

                    # Complete the transaction
                    cocotb.start_soon(self._complete_write_transaction(aw_id))
                    break

            if matched_any:
                break

        if matched_any and self.log:
            self.log.debug(f"AXI4SlaveWrite: W-before-AW matching complete, remaining queued bursts: {len(self.w_transaction_queue)}")

    def _find_matching_transaction_ooo(self):
        """
        Find which transaction should receive the next W packet in OOO mode.

        Strategy:
        - Find incomplete transactions (have AW, need more W beats)
        - Return lowest transaction ID that needs data
        - This allows W data to arrive in any order

        Returns:
            transaction_id or None if no match
        """
        for txn_id in sorted(self.pending_transactions.keys()):
            txn_list = self.pending_transactions[txn_id]
            # Check all transactions in the list for this ID
            for txn in txn_list:
                if len(txn['w_packets']) < txn['expected_beats']:
                    # This transaction needs more W beats
                    return txn_id
        return None

    def _calculate_ooo_delay(self, transaction_id):
        """
        Calculate delay cycles for OOO response (AXI4 compliant: same ID must stay in order).

        Modes:
        - 'deterministic': Use pattern[sequence] to determine completion order
        - 'random': Random delay, but respects same-ID ordering

        Args:
            transaction_id: Transaction ID completing

        Returns:
            Delay in clock cycles before sending response
        """
        # Get transaction metadata
        if transaction_id not in self.pending_transactions:
            return 1

        # Get first transaction in the list (FIFO order)
        txn_list = self.pending_transactions[transaction_id]
        if not txn_list:
            return 1
        txn = txn_list[0]
        txn_sequence = txn.get('sequence')
        if txn_sequence is None:
            return 1  # OOO not enabled for this transaction

        # Get transaction metadata from tracking
        txn_meta = self.ooo_transaction_metadata.get(txn_sequence, {})
        txn_id = txn_meta.get('id', transaction_id)

        # AXI4 COMPLIANCE: Check if previous same-ID transactions have completed
        last_completed = self.ooo_last_completed_seq.get(txn_id, -1)

        # Find all pending same-ID transactions with lower sequence numbers
        blocking_sequences = []
        for seq, meta in self.ooo_transaction_metadata.items():
            if meta['id'] == txn_id and seq < txn_sequence and seq > last_completed:
                blocking_sequences.append(seq)

        # If there are blocking transactions, we MUST wait
        if blocking_sequences:
            if self.log:
                self.log.debug(f"AXI4SlaveWrite: Transaction seq={txn_sequence} id={txn_id} "
                            f"blocked by {len(blocking_sequences)} earlier same-ID transactions")
            # Add large delay to ensure earlier same-ID transactions complete first
            # This will be checked again when this transaction is retried
            return 100  # Long delay to let earlier transactions complete

        mode = self.ooo_config.get('mode', 'random')

        if mode == 'deterministic':
            # Pattern specifies SEQUENCE order (not ID order!)
            pattern = self.ooo_config.get('pattern', [])
            if pattern and txn_sequence < len(pattern):
                # Pattern[i] tells us which sequence number should complete at position i
                target_sequence = pattern[txn_sequence]

                # Find our position in the pattern
                try:
                    target_position = pattern.index(txn_sequence)
                    current_position = len([s for s in self.ooo_last_completed_seq.values() if s >= 0])

                    # Delay based on how far ahead we are in the pattern
                    if target_position > current_position:
                        delay = (target_position - current_position) * 20
                    else:
                        delay = 1  # Ready to complete now

                    if self.log:
                        self.log.debug(f"AXI4SlaveWrite: Deterministic OOO seq={txn_sequence} "
                                    f"id={txn_id}, pattern_pos={target_position}, delay={delay}")

                    return delay
                except ValueError:
                    # Sequence not in pattern, use min delay
                    return self.ooo_config.get('min_delay_cycles', 1)
            else:
                return self.ooo_config.get('min_delay_cycles', 1)

        elif mode == 'random':
            # Random delay within range (but same-ID ordering already enforced above)
            min_delay = self.ooo_config.get('min_delay_cycles', 1)
            max_delay = self.ooo_config.get('max_delay_cycles', 50)
            base_delay = random.randint(min_delay, max_delay)

            # With reorder probability, add extra delay
            # This causes reordering BETWEEN different IDs, not within same ID
            reorder_prob = self.ooo_config.get('reorder_probability', 0.3)
            if random.random() < reorder_prob:
                extra_delay = random.randint(20, 50)
                return base_delay + extra_delay
            else:
                return base_delay

        else:
            # Unknown mode, use default
            return 1

    async def _complete_write_transaction_delayed(self, transaction_id, delay_cycles):
        """
        Complete write transaction after specified delay (for OOO mode).

        Args:
            transaction_id: ID of transaction to complete
            delay_cycles: Number of clock cycles to wait before completion
        """
        # Wait for specified delay
        for _ in range(delay_cycles):
            await RisingEdge(self.clock)

        if self.log:
            self.log.debug(f"AXI4SlaveWrite: OOO delay complete for txn {transaction_id}, sending B response")

        # Now complete the transaction normally
        await self._complete_write_transaction(transaction_id)

    async def _complete_write_transaction(self, transaction_id):
            """Complete write transaction and send B response using generic field names."""
            # Create lock for this transaction ID if it doesn't exist
            if transaction_id not in self.completion_locks:
                self.completion_locks[transaction_id] = asyncio.Lock()

            # Use lock to ensure atomic check-and-set of completing flag
            async with self.completion_locks[transaction_id]:
                # Prevent race condition - check if transaction still exists
                if transaction_id not in self.pending_transactions:
                    if self.log:
                        self.log.debug(f"AXI4SlaveWrite: Transaction {transaction_id} already completed - skipping")
                    return

                # Get the transaction list for this ID
                transaction_list = self.pending_transactions[transaction_id]
                if not transaction_list:
                    if self.log:
                        self.log.debug(f"AXI4SlaveWrite: Transaction list for {transaction_id} is empty - skipping")
                    return

                # Get first complete transaction that's not already completing (FIFO order)
                transaction = None
                for txn in transaction_list:
                    if txn['complete'] and not txn.get('completing', False):
                        transaction = txn
                        break

                if transaction is None:
                    if self.log:
                        self.log.debug(f"AXI4SlaveWrite: No uncompleted transaction found for {transaction_id} - skipping")
                    return

                # Mark as completing to prevent race condition
                # This is now atomic because we're inside the lock
                transaction['completing'] = True

            # Update OOO tracking: mark this transaction as completed
            if self.enable_ooo:
                txn_sequence = transaction.get('sequence')
                if txn_sequence is not None:
                    txn_meta = self.ooo_transaction_metadata.get(txn_sequence, {})
                    txn_id = txn_meta.get('id', transaction_id)
                    # Record this as the last completed sequence for this ID
                    self.ooo_last_completed_seq[txn_id] = txn_sequence
                    if self.log:
                        self.log.debug(f"AXI4SlaveWrite: Completed seq={txn_sequence} id={txn_id}")

            aw_packet = transaction['aw_packet']
            w_packets = transaction['w_packets']

            try:
                # Extract address info using generic field names
                base_addr = getattr(aw_packet, 'addr', 0)
                size_encoding = getattr(aw_packet, 'size', 2)
                bytes_per_beat = 1 << size_encoding

                # Write data to memory if available
                if self.memory_model:
                    for i, w_packet in enumerate(w_packets):
                        addr = base_addr + (i * bytes_per_beat)

                        # Apply base address offset before accessing memory model
                        # (RTL sends absolute addresses, memory model expects 0-based offsets)
                        memory_offset = addr - self.base_addr

                        data = getattr(w_packet, 'data', 0)
                        strb = getattr(w_packet, 'strb', 0xF)

                        # Convert data to proper bytearray format
                        try:
                            data_bytes = self.memory_model.integer_to_bytearray(data, bytes_per_beat)
                            self.memory_model.write(memory_offset, data_bytes, strb)
                        except Exception as mem_error:
                            if self.log:
                                self.log.warning(f"AXI4SlaveWrite: Memory write failed for txn {transaction_id}: {mem_error}")

                # Add delay for realistic B response timing
                if self.response_delay_cycles > 0:
                    for _ in range(self.response_delay_cycles):
                        await RisingEdge(self.clock)

                # Double-check transaction still exists before sending B response
                if transaction_id not in self.pending_transactions:
                    if self.log:
                        self.log.debug(f"AXI4SlaveWrite: Transaction {transaction_id} was deleted during completion")
                    return

                # Send B response using generic field names
                b_packet = self.b_channel.create_packet(
                    id=transaction_id,
                    resp=0
                )

                await self.b_channel.send(b_packet)

                if self.log:
                    self.log.debug(f"AXI4SlaveWrite: B response sent - id={transaction_id}, "
                                f"addr=0x{base_addr:08X}, beats={len(w_packets)}")

            except Exception as e:
                if self.log:
                    self.log.error(f"AXI4SlaveWrite: Error completing transaction {transaction_id}: {e}")
            finally:
                # Safe cleanup - remove completed transaction from list
                if transaction_id in self.pending_transactions:
                    transaction_list = self.pending_transactions[transaction_id]
                    # Remove the completed transaction from the list
                    if transaction in transaction_list:
                        transaction_list.remove(transaction)
                        if self.log:
                            self.log.debug(f"AXI4SlaveWrite: Transaction {transaction_id} removed from list "
                                        f"({len(transaction_list)} remaining)")

                    # If list is now empty, remove the ID entry
                    if not transaction_list:
                        del self.pending_transactions[transaction_id]
                        if self.log:
                            self.log.debug(f"AXI4SlaveWrite: All transactions for ID {transaction_id} completed")
                else:
                    if self.log:
                        self.log.debug(f"AXI4SlaveWrite: Transaction {transaction_id} was already cleaned up")

    def get_compliance_report(self) -> Optional[Dict[str, Any]]:
        """
        ENHANCEMENT: Get compliance report if compliance checking is enabled.
        
        Returns:
            Compliance report dictionary or None if compliance checking disabled
        """
        if self.compliance_checker:
            return self.compliance_checker.get_compliance_report()
        return None

    def print_compliance_report(self):
        """ENHANCEMENT: Print compliance report if compliance checking is enabled."""
        if self.compliance_checker:
            self.compliance_checker.print_compliance_report()
        elif self.log:
            self.log.debug("AXI4SlaveWrite: Compliance checking is disabled")
