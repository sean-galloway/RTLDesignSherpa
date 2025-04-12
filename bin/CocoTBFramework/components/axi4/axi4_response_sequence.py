"""
AXI4 Response Sequence

This module provides specialized sequence generators for AXI4 response channels (B/R).
It focuses on response code generation, ordering, and error injection.
"""

import random
from typing import List, Dict, Any, Optional, Tuple, Union, Set
from collections import deque, defaultdict

from CocoTBFramework.components.field_config import FieldConfig
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.axi4.axi4_packet import AXI4Packet
from CocoTBFramework.components.axi4.axi4_fields_signals import (
    AXI4_B_FIELD_CONFIG,
    AXI4_R_FIELD_CONFIG
)


class AXI4ResponseSequence:
    """
    AXI4 Response Sequence generator with protocol awareness.
    
    This class provides utilities for creating sequences of AXI4 response transactions
    that comply with the AXI4 protocol rules, focusing on response ordering,
    error injection, and ID management.
    """

    # AXI4 response codes
    RESP_OKAY = 0
    RESP_EXOKAY = 1
    RESP_SLVERR = 2
    RESP_DECERR = 3

    def __init__(self, name: str = "axi4_response", 
                 channel: str = "B", 
                 id_width: int = 8, 
                 user_width: int = 1):
        """
        Initialize the AXI4 Response Sequence.

        Args:
            name: Sequence name
            channel: AXI4 channel ('B' or 'R')
            id_width: Width of ID field in bits
            user_width: Width of user field in bits
        """
        self.name = name
        self.channel = channel.upper()
        
        if self.channel not in ['B', 'R']:
            raise ValueError(f"Channel must be either 'B' or 'R', got '{channel}'")
        
        self.id_width = id_width
        self.user_width = user_width
        
        # Select appropriate field config based on channel
        if self.channel == 'B':
            self.field_config = self._adjust_field_config(AXI4_B_FIELD_CONFIG)
        else:  # R
            self.field_config = self._adjust_field_config(AXI4_R_FIELD_CONFIG)
        
        # Initialize sequence data
        self.id_sequence = []
        self.resp_sequence = []
        self.user_sequence = []
        # For R channel only
        self.data_sequence = [] if self.channel == 'R' else None
        self.last_sequence = [] if self.channel == 'R' else None
        
        # Track responses by ID
        self.responses_by_id = defaultdict(list)
        
        # ID order tracking for in-order responses
        self.id_order = []
        
        # Randomization options
        self.randomizer = None
        self.use_random_selection = False
        self.inorder = True  # Default to in-order responses
        self.ooo_strategy = 'random'  # 'random', 'round_robin', 'weighted'
        self.ooo_weights = {}  # For weighted strategy
        
        # Generated packets
        self.packets = deque()
        
        # Iterators for sequences
        self.id_iter = None
        self.resp_iter = None
        self.user_iter = None
        self.data_iter = None
        self.last_iter = None
        
        # Statistics
        self.stats = {
            'total_transactions': 0,
            'okay_responses': 0,
            'exokay_responses': 0,
            'slverr_responses': 0,
            'decerr_responses': 0,
            'out_of_order_count': 0
        }

    def _adjust_field_config(self, field_config: FieldConfig) -> FieldConfig:
        """
        Adjust field configuration for specified widths.
        
        Args:
            field_config: Base field configuration
            
        Returns:
            Adjusted field configuration
        """
        # Create a copy to avoid modifying the original
        adjusted_config = field_config
        
        # Update ID width
        if self.channel == 'B':
            if adjusted_config.has_field('bid'):
                adjusted_config.update_field_width('bid', self.id_width)
            if adjusted_config.has_field('buser'):
                adjusted_config.update_field_width('buser', self.user_width)
        else:  # R
            if adjusted_config.has_field('rid'):
                adjusted_config.update_field_width('rid', self.id_width)
            if adjusted_config.has_field('ruser'):
                adjusted_config.update_field_width('ruser', self.user_width)
        
        return adjusted_config

    def add_transaction(self, 
                        id_value: int, 
                        resp: int = 0, 
                        user: int = 0,
                        data: Optional[int] = None,
                        last: int = 1) -> 'AXI4ResponseSequence':
        """
        Add a response transaction to the sequence.
        
        Args:
            id_value: Transaction ID
            resp: Response code (0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)
            user: User signal
            data: Data value (R channel only)
            last: Last indicator (R channel only)
            
        Returns:
            Self for method chaining
        """
        # Validate response code
        if resp not in [self.RESP_OKAY, self.RESP_EXOKAY, self.RESP_SLVERR, self.RESP_DECERR]:
            raise ValueError(f"Invalid response code: {resp}")
        
        # Add ID
        self.id_sequence.append(id_value)
        
        # Add response code
        self.resp_sequence.append(resp)
        
        # Add user signal
        self.user_sequence.append(user)
        
        # Track by ID
        self.responses_by_id[id_value].append(len(self.id_sequence) - 1)
        
        # Track order for in-order responses
        if id_value not in self.id_order:
            self.id_order.append(id_value)
        
        # For R channel, add data and last
        if self.channel == 'R':
            if data is None:
                data = 0
            self.data_sequence.append(data)
            self.last_sequence.append(last)
        
        # Update statistics
        self.stats['total_transactions'] += 1
        
        if resp == self.RESP_OKAY:
            self.stats['okay_responses'] += 1
        elif resp == self.RESP_EXOKAY:
            self.stats['exokay_responses'] += 1
        elif resp == self.RESP_SLVERR:
            self.stats['slverr_responses'] += 1
        elif resp == self.RESP_DECERR:
            self.stats['decerr_responses'] += 1
        
        return self

    def add_burst_response(self, 
                          id_value: int, 
                          burst_len: int, 
                          data_values: Optional[List[int]] = None,
                          resp: int = 0,
                          user: int = 0) -> 'AXI4ResponseSequence':
        """
        Add a complete burst of responses.
        Only applicable for R channel.
        
        Args:
            id_value: Transaction ID
            burst_len: Burst length (0 = 1 beat, 255 = 256 beats)
            data_values: List of data values for the burst
            resp: Response code (0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)
            user: User signal
            
        Returns:
            Self for method chaining
        """
        if self.channel != 'R':
            raise ValueError("Burst responses are only applicable for R channel")
        
        # Create default data values if not provided
        if data_values is None:
            data_values = [0] * (burst_len + 1)
        
        # Ensure data_values has enough values
        if len(data_values) < (burst_len + 1):
            # Pad with zeros
            data_values = data_values + [0] * ((burst_len + 1) - len(data_values))
        
        # Add each beat in the burst
        for i in range(burst_len + 1):
            is_last = (i == burst_len)
            data = data_values[i] if i < len(data_values) else 0
            
            self.add_transaction(
                id_value=id_value,
                resp=resp,
                user=user,
                data=data,
                last=1 if is_last else 0
            )
        
        return self

    def set_order_mode(self, inorder: bool, ooo_strategy: str = 'random') -> 'AXI4ResponseSequence':
        """
        Set the response ordering mode.
        
        Args:
            inorder: If True, responses will be in order by ID
                    If False, out-of-order responses are allowed
            ooo_strategy: Strategy for out-of-order responses
                          'random': Random selection
                          'round_robin': Round-robin by ID
                          'weighted': Weighted by ID priority
            
        Returns:
            Self for method chaining
        """
        self.inorder = inorder
        
        if not inorder:
            if ooo_strategy not in ['random', 'round_robin', 'weighted']:
                raise ValueError(f"Invalid out-of-order strategy: {ooo_strategy}")
            self.ooo_strategy = ooo_strategy
        
        return self

    def set_ooo_weight(self, id_value: int, weight: float) -> 'AXI4ResponseSequence':
        """
        Set the weight for a specific ID in weighted out-of-order strategy.
        
        Args:
            id_value: Transaction ID
            weight: Weight value (higher values increase selection probability)
            
        Returns:
            Self for method chaining
        """
        self.ooo_weights[id_value] = weight
        return self

    def set_random_selection(self, enable: bool = True) -> 'AXI4ResponseSequence':
        """
        Enable/disable random selection from sequences.

        Args:
            enable: True to enable random selection, False to use sequential
            
        Returns:
            Self for method chaining
        """
        self.use_random_selection = enable
        return self

    def set_randomizer(self, randomizer: FlexRandomizer) -> 'AXI4ResponseSequence':
        """
        Set the randomizer for timing constraints.

        Args:
            randomizer: FlexRandomizer instance
            
        Returns:
            Self for method chaining
        """
        self.randomizer = randomizer
        return self

    def reset_iterators(self):
        """Reset all sequence iterators to the beginning."""
        self.id_iter = iter(self.id_sequence)
        self.resp_iter = iter(self.resp_sequence)
        self.user_iter = iter(self.user_sequence)
        
        if self.channel == 'R':
            self.data_iter = iter(self.data_sequence)
            self.last_iter = iter(self.last_sequence)

    def _next_value(self, sequence: List[Any], iterator: Optional[Any]) -> Any:
        """
        Get the next value from a sequence with proper iterator handling.
        
        Args:
            sequence: List of values
            iterator: Iterator for the sequence
            
        Returns:
            Next value in the sequence
        """
        if not sequence:
            return 0
            
        if self.use_random_selection:
            return random.choice(sequence)
            
        try:
            if iterator is None:
                iterator = iter(sequence)
            return next(iterator)
        except StopIteration:
            # Reset iterator and try again
            iterator = iter(sequence)
            return next(iterator)

    def _select_next_id(self) -> Optional[int]:
        """
        Select the next ID to process based on ordering strategy.
        
        Returns:
            Selected ID or None if no IDs available
        """
        # Get all IDs with pending responses
        pending_ids = [id_value for id_value, indices in self.responses_by_id.items() if indices]
        
        if not pending_ids:
            return None
        
        if self.inorder:
            # In-order: follow the original order of IDs
            for id_value in self.id_order:
                if id_value in pending_ids:
                    return id_value
            
            # If we get here, there are pending IDs but none in the order list
            # Default to first pending ID
            return pending_ids[0]
        else:
            # Out-of-order: select based on strategy
            if self.ooo_strategy == 'random':
                return random.choice(pending_ids)
                
            elif self.ooo_strategy == 'round_robin':
                # Find the first ID in order that has pending responses
                for id_value in self.id_order:
                    if id_value in pending_ids:
                        # Move this ID to the end of the order list
                        self.id_order.remove(id_value)
                        self.id_order.append(id_value)
                        return id_value
                
                # If we get here, there are pending IDs but none in the order list
                # Default to first pending ID
                return pending_ids[0]
                
            elif self.ooo_strategy == 'weighted':
                # Calculate weights for each pending ID
                weights = []
                for id_value in pending_ids:
                    # Default weight is 1.0 if not specified
                    weight = self.ooo_weights.get(id_value, 1.0)
                    weights.append(weight)
                
                # Select based on weights
                return random.choices(pending_ids, weights=weights)[0] if sum(weights) > 0 else pending_ids[0]
        
        # Fallback to first pending ID
        return pending_ids[0]

    def generate_packet(self) -> Optional[AXI4Packet]:
        """
        Generate the next response packet according to ordering strategy.

        Returns:
            AXI4 response packet (B or R) or None if no more responses
        """
        # Select next ID to process
        id_value = self._select_next_id()
        if id_value is None:
            return None
        
        # Get the next response index for this ID
        index = self.responses_by_id[id_value].pop(0)
        
        # Check if this is out of order
        if self.inorder:
            expected_id = None
            for id_value_check in self.id_order:
                if self.responses_by_id.get(id_value_check, []):
                    expected_id = id_value_check
                    break
            
            if expected_id is not None and id_value != expected_id:
                self.stats['out_of_order_count'] += 1
        
        # Get values from sequences at this index
        resp = self.resp_sequence[index]
        user = self.user_sequence[index]
        
        # Create appropriate packet type
        if self.channel == 'B':
            packet = AXI4Packet.create_b_packet(
                bid=id_value,
                bresp=resp,
                buser=user
            )
        else:  # R
            data = self.data_sequence[index]
            last = self.last_sequence[index]
            
            packet = AXI4Packet.create_r_packet(
                rid=id_value,
                rdata=data,
                rresp=resp,
                rlast=last,
                ruser=user
            )
        
        # Remove ID from order list if no more responses for this ID
        if not self.responses_by_id[id_value]:
            if id_value in self.id_order:
                self.id_order.remove(id_value)
        
        return packet

    def generate_packets(self) -> List[AXI4Packet]:
        """
        Generate all response packets according to ordering strategy.

        Returns:
            List of generated packets
        """
        # Clear previous packets
        self.packets.clear()
        
        # Generate packets in proper order
        while True:
            packet = self.generate_packet()
            if packet is None:
                break
            self.packets.append(packet)
        
        return list(self.packets)

    def get_stats(self) -> Dict[str, Any]:
        """
        Get statistics about the sequence generation.
        
        Returns:
            Dictionary with statistics
        """
        return self.stats

    # ========================================================================
    # Factory Methods for Common Response Patterns
    # ========================================================================
    
    @classmethod
    def create_write_responses(cls, 
                             id_values: List[int], 
                             resp_values: Optional[List[int]] = None,
                             id_width: int = 8) -> 'AXI4ResponseSequence':
        """
        Create a sequence of write responses.
        
        Args:
            id_values: List of transaction IDs
            resp_values: List of response codes (0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)
            id_width: Width of ID field in bits
            
        Returns:
            Configured AXI4ResponseSequence
        """
        sequence = cls(name="write_responses", channel='B', id_width=id_width)
        
        # Default to OKAY responses if not provided
        if resp_values is None:
            resp_values = [cls.RESP_OKAY] * len(id_values)
        
        # Ensure resp_values has the same length as id_values
        if len(resp_values) < len(id_values):
            # Pad with OKAY responses
            resp_values = resp_values + [cls.RESP_OKAY] * (len(id_values) - len(resp_values))
        
        # Add responses
        for i, id_value in enumerate(id_values):
            resp = resp_values[i]
            
            sequence.add_transaction(
                id_value=id_value,
                resp=resp
            )
        
        return sequence

    @classmethod
    def create_read_responses(cls, 
                            id_values: List[int], 
                            data_values: List[List[int]],
                            resp_values: Optional[List[int]] = None,
                            id_width: int = 8) -> 'AXI4ResponseSequence':
        """
        Create a sequence of read responses.
        
        Args:
            id_values: List of transaction IDs
            data_values: List of data bursts (each item is a list of values for one burst)
            resp_values: List of response codes (0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)
            id_width: Width of ID field in bits
            
        Returns:
            Configured AXI4ResponseSequence
        """
        sequence = cls(name="read_responses", channel='R', id_width=id_width)
        
        # Default to OKAY responses if not provided
        if resp_values is None:
            resp_values = [cls.RESP_OKAY] * len(id_values)
        
        # Ensure resp_values has the same length as id_values
        if len(resp_values) < len(id_values):
            # Pad with OKAY responses
            resp_values = resp_values + [cls.RESP_OKAY] * (len(id_values) - len(resp_values))
        
        # Add responses
        for i, id_value in enumerate(id_values):
            resp = resp_values[i]
            
            # Get data for this burst
            if i < len(data_values):
                data = data_values[i]
            else:
                data = [0]  # Default if not enough data provided
            
            # Add burst response
            sequence.add_burst_response(
                id_value=id_value,
                burst_len=len(data) - 1,
                data_values=data,
                resp=resp
            )
        
        return sequence

    @classmethod
    def create_error_responses(cls, 
                             id_values: List[int], 
                             error_type: str = 'slverr',
                             channel: str = 'B',
                             id_width: int = 8) -> 'AXI4ResponseSequence':
        """
        Create a sequence of error responses.
        
        Args:
            id_values: List of transaction IDs
            error_type: Type of error ('slverr' or 'decerr')
            channel: AXI4 channel ('B' or 'R')
            id_width: Width of ID field in bits
            
        Returns:
            Configured AXI4ResponseSequence
        """
        sequence = cls(name=f"{error_type}_responses", channel=channel, id_width=id_width)
        
        # Set response code based on error type
        if error_type.lower() == 'slverr':
            resp = cls.RESP_SLVERR
        elif error_type.lower() == 'decerr':
            resp = cls.RESP_DECERR
        else:
            raise ValueError(f"Invalid error type: {error_type}. Must be 'slverr' or 'decerr'")
        
        # Add responses
        for id_value in id_values:
            if channel == 'B':
                # Write response - single beat
                sequence.add_transaction(
                    id_value=id_value,
                    resp=resp
                )
            else:  # 'R'
                # Read response - could be burst, but use single beat for error
                sequence.add_transaction(
                    id_value=id_value,
                    resp=resp,
                    data=0,
                    last=1  # Always last for error
                )
        
        return sequence

    @classmethod
    def create_exclusive_responses(cls, 
                                 id_values: List[int], 
                                 id_width: int = 8) -> 'AXI4ResponseSequence':
        """
        Create a sequence of exclusive access responses.
        
        Args:
            id_values: List of transaction IDs
            id_width: Width of ID field in bits
            
        Returns:
            Configured AXI4ResponseSequence
        """
        sequence = cls(name="exclusive_responses", channel='B', id_width=id_width)
        
        # Add EXOKAY responses
        for id_value in id_values:
            sequence.add_transaction(
                id_value=id_value,
                resp=cls.RESP_EXOKAY
            )
        
        return sequence

    @classmethod
    def create_mixed_responses(cls, 
                             id_width: int = 8) -> 'AXI4ResponseSequence':
        """
        Create a comprehensive test sequence with mixed response types.
        
        Args:
            id_width: Width of ID field in bits
            
        Returns:
            Configured AXI4ResponseSequence
        """
        # Create B channel response sequence
        sequence = cls(name="mixed_responses", channel='B', id_width=id_width)
        
        # Add various response types
        
        # 1. Normal OKAY responses
        for i in range(10):
            sequence.add_transaction(
                id_value=i,
                resp=cls.RESP_OKAY
            )
        
        # 2. Exclusive access responses
        for i in range(10, 15):
            sequence.add_transaction(
                id_value=i,
                resp=cls.RESP_EXOKAY
            )
        
        # 3. Slave error responses
        for i in range(15, 20):
            sequence.add_transaction(
                id_value=i,
                resp=cls.RESP_SLVERR
            )
        
        # 4. Decode error responses
        for i in range(20, 25):
            sequence.add_transaction(
                id_value=i,
                resp=cls.RESP_DECERR
            )
        
        # Set to out-of-order mode with weighted strategy
        sequence.set_order_mode(inorder=False, ooo_strategy='weighted')
        
        # Set weights for different response types
        for i in range(10):  # OKAY responses - normal priority
            sequence.set_ooo_weight(i, 1.0)
            
        for i in range(10, 15):  # EXOKAY responses - high priority
            sequence.set_ooo_weight(i, 2.0)
            
        for i in range(15, 20):  # SLVERR responses - low priority
            sequence.set_ooo_weight(i, 0.5)
            
        for i in range(20, 25):  # DECERR responses - very low priority
            sequence.set_ooo_weight(i, 0.2)
        
        return sequence

    @classmethod
    def create_ordered_vs_unordered(cls, 
                                  id_width: int = 8) -> Tuple['AXI4ResponseSequence', 'AXI4ResponseSequence']:
        """
        Create a pair of in-order and out-of-order response sequences with the same transactions.
        
        Args:
            id_width: Width of ID field in bits
            
        Returns:
            Tuple of (in-order sequence, out-of-order sequence)
        """
        # Create sequences
        inorder_sequence = cls(name="inorder_responses", channel='B', id_width=id_width)
        outoforder_sequence = cls(name="outoforder_responses", channel='B', id_width=id_width)
        
        # Add same transactions to both
        for i in range(4):  # Different IDs
            for j in range(5):  # Multiple responses per ID
                inorder_sequence.add_transaction(
                    id_value=i,
                    resp=cls.RESP_OKAY
                )
                
                outoforder_sequence.add_transaction(
                    id_value=i,
                    resp=cls.RESP_OKAY
                )
        
        # Set ordering modes
        inorder_sequence.set_order_mode(inorder=True)
        outoforder_sequence.set_order_mode(inorder=False, ooo_strategy='random')
        
        return inorder_sequence, outoforder_sequence