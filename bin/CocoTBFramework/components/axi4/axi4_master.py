"""
AXI4 Master Component for Verification

This module provides the AXI4Master class for AXI4 master interfaces.
"""

import cocotb
from collections import deque
from cocotb.triggers import RisingEdge, FallingEdge, Timer
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


class AXI4Master:
    """
    AXI4 Master component that manages multiple channels for AXI4 transactions.
    
    This class provides:
    - Separate GAXI masters for each AXI4 channel (AW, W, B, AR, R)
    - Coordinated transaction management across channels
    - AXI4 protocol checking
    """
    
    def __init__(self, dut, title, prefix, divider, suffix, clock, channels,
                    id_width=8, addr_width=32, data_width=32, user_width=1,
                    aw_randomizer=None, w_randomizer=None, ar_randomizer=None,
                    check_protocol=True, log=None):
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
            aw_randomizer: Timing randomizer for AW channel
            w_randomizer: Timing randomizer for W channel
            ar_randomizer: Timing randomizer for AR channel
            check_protocol: Enable AXI4 protocol checking (default: True)
            log: Logger instance
        """
        self.title = title
        self.clock = clock
        self.log = log
        self.check_protocol = check_protocol
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
        
        # Create randomizers if not provided
        self.aw_randomizer = aw_randomizer or FlexRandomizer(AXI4_MASTER_DEFAULT_CONSTRAINTS)
        self.w_randomizer = w_randomizer or FlexRandomizer(AXI4_MASTER_DEFAULT_CONSTRAINTS)
        self.ar_randomizer = ar_randomizer or FlexRandomizer(AXI4_MASTER_DEFAULT_CONSTRAINTS)
        
        # Create channel components
        if 'AW' in self.channels:
            self.aw_master = create_gaxi_master(
                dut, f"{title}_AW", "", clock,
                field_config=self.aw_field_config,
                randomizer=self.aw_randomizer,
                multi_sig=True,
                signal_map=aw_signal_map,
                optional_signal_map=aw_optional_signal_map,
                log=log
            )
        else:
            self.aw_master = None
        
        if 'W' in self.channels:
            self.w_master = create_gaxi_master(
                dut, f"{title}_W", "", clock,
                field_config=self.w_field_config,
                randomizer=self.w_randomizer,
                multi_sig=True,
                signal_map=w_signal_map,
                optional_signal_map=w_optional_signal_map,
                log=log
            )
        else:
            self.w_master = None

        if 'B' in self.channels:
            self.b_slave = create_gaxi_slave(
                dut, f"{title}_B", "", clock,
                field_config=self.b_field_config,
                multi_sig=True,
                signal_map=b_signal_map,
                optional_signal_map=b_optional_signal_map,
                log=log
            )
        else:
            self.b_slave = None
            
        if 'AR' in self.channels:
            self.ar_master = create_gaxi_master(
                dut, f"{title}_AR", "", clock,
                field_config=self.ar_field_config,
                randomizer=self.ar_randomizer,
                multi_sig=True,
                signal_map=ar_signal_map,
                optional_signal_map=ar_optional_signal_map,
                log=log
            )
        else:
            self.ar_master = None
            
        if 'R' in self.channels:
            self.r_slave = create_gaxi_slave(
                dut, f"{title}_R", "", clock,
                field_config=self.r_field_config,
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
        if 'B' in self.channels:
            self.b_slave.add_callback(self._handle_b_response)
        if 'R' in self.channels:
            self.r_slave.add_callback(self._handle_r_response)
        
        self.log.info(f"AXI4Master '{title}' initialized")
    
    async def reset_bus(self):
        """Reset all AXI4 channels"""
        if 'AW' in self.channels:
            await self.aw_master.reset_bus()
        if 'W' in self.channels:
            await self.w_master.reset_bus()
        if 'B' in self.channels:
            await self.b_slave.reset_bus()
        if 'AR' in self.channels:
            await self.ar_master.reset_bus()
        if 'R' in self.channels:
            await self.r_slave.reset_bus()
            
            # Clear transaction tracking
        if 'B' in self.channels:
            self.write_responses.clear()
        if 'R' in self.channels:
            self.read_responses.clear()
    
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
    
    async def write(self, addr, data, size=2, burst=1, strobe=None, id=0, length=0, cache=0, prot=0, qos=0, region=0, user=0):
        """
        Execute an AXI4 write transaction (simple helper for single transfers).
        
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
        # Convert data to a list if it's a single value
        if isinstance(data, int):
            data = [data]
        elif isinstance(data, (bytearray, bytes)):
            # Convert bytearray to list of ints
            data = list(data)

        # Ensure data length matches length+1
        if len(data) != length + 1:
            if len(data) < length + 1:
                # Pad with zeros
                data.extend([0] * (length + 1 - len(data)))
            else:
                # Truncate
                data = data[:length + 1]

        # Set default strobe value (all bytes enabled)
        if strobe is None:
            bytes_per_beat = 1 << size
            strobe = (1 << bytes_per_beat) - 1

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

        # Validate AW packet
        if self.check_protocol:
            valid, error_msg = aw_packet.validate_axi4_protocol()
            if not valid:
                self.log.error(f"AXI4 protocol error: {error_msg}")
                raise ValueError(f"AXI4 protocol error: {error_msg}")

        # Create pending transaction entry
        self.write_responses[id] = {
            'aw_packet': aw_packet,
            'w_packets': [],
            'complete': False,
            'start_time': get_sim_time('ns')
        }

        # Send AW packet
        await self.aw_master.send(aw_packet)

        # Send W packets
        for i, beat_data in enumerate(data):
            # Create W packet for this beat
            w_packet = AXI4Packet.create_w_packet(
                wdata=beat_data,
                wstrb=strobe,
                wlast=1 if i == length else 0,
                wuser=user
            )

            # Validate W packet
            if self.check_protocol:
                valid, error_msg = w_packet.validate_axi4_protocol()
                if not valid:
                    self.log.error(f"AXI4 protocol error: {error_msg}")
                    raise ValueError(f"AXI4 protocol error: {error_msg}")

            # Add to tracking
            self.write_responses[id]['w_packets'].append(w_packet)

            # Send W packet
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
        
        # Validate AR packet
        if self.check_protocol:
            valid, error_msg = ar_packet.validate_axi4_protocol()
            if not valid:
                self.log.error(f"AXI4 protocol error: {error_msg}")
                raise ValueError(f"AXI4 protocol error: {error_msg}")
        
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
