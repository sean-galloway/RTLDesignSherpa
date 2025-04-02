"""Enhanced GAXI test sequences for the comprehensive buffer testbench"""
import random
from typing import Dict, List, Any, Callable, Optional

from CocoTBFramework.components.gaxi.gaxi_sequence import GAXISequence
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.field_config import FieldConfig


class GAXITestSequences:
    """Collection of common GAXI test sequences for buffer testing"""

    @staticmethod
    def create_incremental_sequence(name: str, field_config: FieldConfig, count: int = 100,
                                    addr_step: int = 4, data_pattern: Optional[Callable] = None):
        """
        Create a sequence with incrementing addresses and data.

        Args:
            name: Sequence name
            field_config: Field configuration
            count: Number of transactions
            addr_step: Address increment between transactions
            data_pattern: Optional function to generate data from address

        Returns:
            Configured GAXISequence
        """
        sequence = GAXISequence(name, field_config)

        # Use lambda function that increments data with address if not provided
        if data_pattern is None:
            data_pattern = lambda idx: idx & 0xFFFFFFFF

        # Determine if we have multi-field config
        has_multi_fields = len(field_config.field_names()) > 1

        # Generate transactions
        for i in range(count):
            # Calculate values based on counter
            addr = i * addr_step
            data = data_pattern(i)

            # For multi-field configurations, add ctrl field
            if has_multi_fields and 'ctrl' in field_config.field_names():
                ctrl = (i * 2) & 0xFFFFFFFF
                extra_fields = {'ctrl': ctrl}

                # Check for data0/data1 pattern
                if 'data0' in field_config.field_names() and 'data1' in field_config.field_names():
                    # Create data dictionary with separate values for each data field
                    data_dict = {
                        'data0': data & 0xFFFFFFFF,
                        'data1': (data << 8) & 0xFFFFFFFF
                    }
                    sequence.add_write(addr, data_dict, extra_fields)
                else:
                    sequence.add_write(addr, data, extra_fields)
            else:
                # Standard mode - simple data field
                sequence.add_write(addr, data)

            # Add a small delay
            sequence.add_delay(1)

        return sequence

    @staticmethod
    def create_random_sequence(name: str, field_config: FieldConfig, count: int = 100,
                                addr_mask: int = 0xFFF, data_mask: int = 0xFFFFFFFF,
                                varies_valid_ready: bool = True):
        """
        Create a sequence with random values for addresses and data.

        Args:
            name: Sequence name
            field_config: Field configuration
            count: Number of transactions
            addr_mask: Mask for address values (limits range)
            data_mask: Mask for data values (limits range)
            varies_valid_ready: If True, use varying delays for valid/ready

        Returns:
            Configured GAXISequence
        """
        sequence = GAXISequence(name, field_config)

        # Determine if we have multi-field config
        has_multi_fields = len(field_config.field_names()) > 1

        # Generate transactions
        for _ in range(count):
            # Generate random values
            addr = random.randint(0, addr_mask)
            data = random.randint(0, data_mask)

            # For multi-field configurations, add ctrl field
            if has_multi_fields and 'ctrl' in field_config.field_names():
                ctrl = random.randint(0, 0xFF)
                extra_fields = {'ctrl': ctrl}

                # Check for data0/data1 pattern
                if 'data0' in field_config.field_names() and 'data1' in field_config.field_names():
                    # Create data dictionary with separate values for each data field
                    data_dict = {
                        'data0': random.randint(0, data_mask),
                        'data1': random.randint(0, data_mask)
                    }
                    sequence.add_write(addr, data_dict, extra_fields)
                else:
                    sequence.add_write(addr, data, extra_fields)
            else:
                # Standard mode - simple data field
                sequence.add_write(addr, data)

            # Add varying delays if requested
            if varies_valid_ready:
                delay = random.randint(0, 5)
                sequence.add_delay(delay)
            else:
                sequence.add_delay(0)

        return sequence

    @staticmethod
    def create_back_to_back_sequence(name: str, field_config: FieldConfig, count: int = 100,
                                    addr_pattern: str = "incremental", data_pattern: str = "incremental"):
        """
        Create a sequence with back-to-back transactions (no delays between valid assertions).

        Args:
            name: Sequence name
            field_config: Field configuration
            count: Number of transactions
            addr_pattern: Address pattern ("incremental", "random", "constant")
            data_pattern: Data pattern ("incremental", "random", "alternating", "walking_ones")

        Returns:
            Configured GAXISequence
        """
        sequence = GAXISequence(name, field_config)

        # Determine if we have multi-field config
        has_multi_fields = len(field_config.field_names()) > 1

        # Generate transactions
        for i in range(count):
            # Generate address based on pattern
            if addr_pattern == "incremental":
                addr = i * 4  # Assume 4-byte aligned addresses
            elif addr_pattern == "random":
                addr = random.randint(0, 0xFFF) & ~0x3  # Random 4-byte aligned
            else:  # constant
                addr = 0x100

            # Generate data based on pattern
            if data_pattern == "incremental":
                data = i & 0xFFFFFFFF
            elif data_pattern == "random":
                data = random.randint(0, 0xFFFFFFFF)
            elif data_pattern == "alternating":
                data = 0x55555555 if (i % 2 == 0) else 0xAAAAAAAA
            elif data_pattern == "walking_ones":
                data = 1 << (i % 32)
            else:
                data = 0xA5A5A5A5

            # For multi-field configurations, add ctrl field
            if has_multi_fields and 'ctrl' in field_config.field_names():
                ctrl = i & 0xFF if data_pattern == "incremental" else random.randint(0, 0xFF)
                extra_fields = {'ctrl': ctrl}

                # Check for data0/data1 pattern
                if 'data0' in field_config.field_names() and 'data1' in field_config.field_names():
                    # Create data dictionary with separate values for each data field
                    if data_pattern == "incremental":
                        data_dict = {
                            'data0': (i * 3) & 0xFFFFFFFF,
                            'data1': (i * 7) & 0xFFFFFFFF
                        }
                    else:
                        data_dict = {
                            'data0': data & 0xFFFFFFFF,
                            'data1': (data << 8) & 0xFFFFFFFF
                        }
                    sequence.add_write(addr, data_dict, extra_fields)
                else:
                    sequence.add_write(addr, data, extra_fields)
            else:
                # Standard mode - simple data field
                sequence.add_write(addr, data)

            # No delays for back-to-back
            sequence.add_delay(0)

        return sequence

    @staticmethod
    def create_burst_pause_sequence(name: str, field_config: FieldConfig, burst_size: int = 10,
                                    num_bursts: int = 5, pause_length: int = 20,
                                    addr_start: int = 0, data_start: int = 0):
        """
        Create a sequence with bursts of transactions followed by pauses.

        Args:
            name: Sequence name
            field_config: Field configuration
            burst_size: Number of transactions in each burst
            num_bursts: Number of bursts
            pause_length: Delay between bursts
            addr_start: Starting address
            data_start: Starting data value

        Returns:
            Configured GAXISequence
        """
        sequence = GAXISequence(name, field_config)

        # Determine if we have multi-field config
        has_multi_fields = len(field_config.field_names()) > 1

        # Generate bursts
        for burst in range(num_bursts):
            burst_addr_base = addr_start + (burst * burst_size * 4)
            burst_data_base = data_start + (burst * burst_size)

            # Generate transactions for this burst
            for i in range(burst_size):
                addr = burst_addr_base + (i * 4)
                data = (burst_data_base + i) & 0xFFFFFFFF

                # For multi-field configurations, add ctrl field
                if has_multi_fields and 'ctrl' in field_config.field_names():
                    ctrl = (burst * 16 + i) & 0xFF
                    extra_fields = {'ctrl': ctrl}

                    # Check for data0/data1 pattern
                    if 'data0' in field_config.field_names() and 'data1' in field_config.field_names():
                        # Create data dictionary with separate values for each data field
                        data_dict = {
                            'data0': data & 0xFFFFFFFF,
                            'data1': ((data << 8) + i) & 0xFFFFFFFF
                        }
                        sequence.add_write(addr, data_dict, extra_fields)
                    else:
                        sequence.add_write(addr, data, extra_fields)
                else:
                    # Standard mode - simple data field
                    sequence.add_write(addr, data)

                # No delays within burst
                sequence.add_delay(0)

            # Add pause after burst (except last burst)
            if burst < num_bursts - 1:
                sequence.add_delay(pause_length)

        return sequence

    @staticmethod
    def create_full_empty_test_sequence(name: str, field_config: FieldConfig, buffer_depth: int = 16,
                                        addr_start: int = 0, data_start: int = 0,
                                        overflow_factor: float = 1.5):
        """
        Create a sequence designed to test buffer full and empty conditions.

        Args:
            name: Sequence name
            field_config: Field configuration
            buffer_depth: Depth of the buffer to test
            addr_start: Starting address
            data_start: Starting data value
            overflow_factor: Factor to multiply buffer_depth for generating extra transactions

        Returns:
            Configured GAXISequence
        """
        sequence = GAXISequence(name, field_config)

        # Determine if we have multi-field config
        has_multi_fields = len(field_config.field_names()) > 1

        # Calculate number of transactions (more than buffer depth to ensure full condition)
        count = int(buffer_depth * overflow_factor)

        # Generate transactions
        for i in range(count):
            addr = addr_start + (i * 4)
            data = (data_start + i) & 0xFFFFFFFF

            # For multi-field configurations, add ctrl field
            if has_multi_fields and 'ctrl' in field_config.field_names():
                ctrl = i & 0xFF
                extra_fields = {'ctrl': ctrl}

                # Check for data0/data1 pattern
                if 'data0' in field_config.field_names() and 'data1' in field_config.field_names():
                    # Create data dictionary with separate values for each data field
                    data_dict = {
                        'data0': data & 0xFFFFFFFF,
                        'data1': (data << 8) & 0xFFFFFFFF
                    }
                    sequence.add_write(addr, data_dict, extra_fields)
                else:
                    sequence.add_write(addr, data, extra_fields)
            else:
                # Standard mode - simple data field
                sequence.add_write(addr, data)

            # No delays to ensure buffer fills up
            sequence.add_delay(0)

        return sequence

    @staticmethod
    def create_pattern_test_sequence(name: str, field_config: FieldConfig,
                                    addr: int = 0x100, pattern_type: str = "walking"):
        """
        Create a sequence with specific data patterns useful for testing data path integrity.

        Args:
            name: Sequence name
            field_config: Field configuration
            addr: Address to use for all transactions
            pattern_type: Pattern type ("walking", "alternating", "corners", "edges")

        Returns:
            Configured GAXISequence
        """
        sequence = GAXISequence(name, field_config)

        # Determine if we have multi-field config
        has_multi_fields = len(field_config.field_names()) > 1

        # Get the width of the data field
        data_width = 32  # Default
        if 'data' in field_config.field_names():
            field_def = field_config.get_field('data')
            data_width = field_def.bits

        # Define patterns based on type
        patterns = []

        if pattern_type == "walking":
            # Walking ones and zeros
            for i in range(data_width):
                patterns.append(1 << i)  # Walking ones
            for i in range(data_width):
                patterns.append(~(1 << i) & ((1 << data_width) - 1))  # Walking zeros

        elif pattern_type == "alternating":
            # Alternating patterns
            patterns = [
                0x55555555 & ((1 << data_width) - 1),  # 0101...
                0xAAAAAAAA & ((1 << data_width) - 1),  # 1010...
                0x33333333 & ((1 << data_width) - 1),  # 0011...
                0xCCCCCCCC & ((1 << data_width) - 1),  # 1100...
                0x0F0F0F0F & ((1 << data_width) - 1),  # 00001111...
                0xF0F0F0F0 & ((1 << data_width) - 1),  # 11110000...
                0x00FF00FF & ((1 << data_width) - 1),  # 00000000 11111111...
                0xFF00FF00 & ((1 << data_width) - 1),  # 11111111 00000000...
            ]

        elif pattern_type == "corners":
            # Corner cases
            mask = (1 << data_width) - 1
            patterns = [
                0,                   # All zeros
                mask,                # All ones
                0x00000001,          # Just LSB
                1 << (data_width-1), # Just MSB
                0x00000003,          # Two LSBs
                mask & ~0x00000001,  # All except LSB
                mask & ~(1 << (data_width-1)), # All except MSB
            ]

        elif pattern_type == "edges":
            # Edge cases
            patterns = [
                0x00000000,  # All zeros
                0xFFFFFFFF,  # All ones
                0xA5A5A5A5,  # Alternating nibbles
                0x5A5A5A5A,  # Alternating nibbles inverted
                0xDEADBEEF,  # Common test pattern
                0x01234567,  # Incrementing nibbles
                0x76543210,  # Decrementing nibbles
            ]

        else:
            # Default if unknown pattern
            patterns = [0xA5A5A5A5, 0x5A5A5A5A, 0xFFFFFFFF, 0x00000000]

        # Generate a transaction for each pattern
        for data in patterns:
            # Mask to ensure pattern fits in data width
            data = data & ((1 << data_width) - 1)

            # For multi-field configurations, add ctrl field
            if has_multi_fields and 'ctrl' in field_config.field_names():
                ctrl = (data >> 16) & 0xFF  # Use part of the data pattern
                extra_fields = {'ctrl': ctrl}

                # Check for data0/data1 pattern
                if 'data0' in field_config.field_names() and 'data1' in field_config.field_names():
                    # Create data dictionary with separate values for each data field
                    data_dict = {
                        'data0': data & 0xFFFFFFFF,
                        'data1': ~data & 0xFFFFFFFF  # Complement of data0
                    }
                    sequence.add_write(addr, data_dict, extra_fields)
                else:
                    sequence.add_write(addr, data, extra_fields)
            else:
                # Standard mode - simple data field
                sequence.add_write(addr, data)

            # Small delay between patterns
            sequence.add_delay(2)

        return sequence

    @staticmethod
    def create_addr_ctrl_crossing_sequence(name: str, field_config: FieldConfig, count: int = 50):
        """
        Create a sequence specifically to test crossing of addr/ctrl/data signals,
        with different values and patterns in each field.

        Args:
            name: Sequence name
            field_config: Field configuration
            count: Number of transactions

        Returns:
            Configured GAXISequence, or None if not a multi-field config
        """
        # Only applicable for multi-field configurations
        if 'addr' not in field_config.field_names() or 'ctrl' not in field_config.field_names():
            return None

        sequence = GAXISequence(name, field_config)

        # Get field widths
        addr_width = field_config.get_field('addr').bits
        ctrl_width = field_config.get_field('ctrl').bits

        addr_mask = (1 << addr_width) - 1
        ctrl_mask = (1 << ctrl_width) - 1

        # Generate transactions with different patterns for each field
        for i in range(count):
            # Use different prime multipliers to ensure values don't track together
            addr = (i * 7) & addr_mask
            ctrl = (i * 11) & ctrl_mask

            # Data field(s)
            if 'data0' in field_config.field_names() and 'data1' in field_config.field_names():
                # Multi-data configuration
                data_dict = {
                    'data0': (i * 13) & 0xFFFFFFFF,
                    'data1': (i * 17) & 0xFFFFFFFF
                }
                sequence.add_write(addr, data_dict, {'ctrl': ctrl})
            elif 'data' in field_config.field_names():
                # Single data field
                data = (i * 19) & 0xFFFFFFFF
                sequence.add_write(addr, data, {'ctrl': ctrl})
            else:
                # Fallback - should never happen with proper field config
                sequence.add_write(addr, 0, {'ctrl': ctrl})

            # Small delay between transactions
            sequence.add_delay(1)

        return sequence

    @staticmethod
    def create_alternating_field_values_sequence(name: str, field_config: FieldConfig, count: int = 40):
        """
        Create a sequence with alternating bit patterns in different fields.

        Args:
            name: Sequence name
            field_config: Field configuration
            count: Number of transactions

        Returns:
            Configured GAXISequence, or None if not a multi-field config
        """
        # Only applicable for multi-field configurations
        if 'addr' not in field_config.field_names() or 'ctrl' not in field_config.field_names():
            return None

        sequence = GAXISequence(name, field_config)

        # Get field widths
        addr_width = field_config.get_field('addr').bits
        ctrl_width = field_config.get_field('ctrl').bits

        addr_mask = (1 << addr_width) - 1
        ctrl_mask = (1 << ctrl_width) - 1

        # Helper function to generate alternating 1s and 0s
        def alternating_ones(width):
            result = 0
            for i in range(0, width, 2):
                result |= (1 << i)
            return result

        def invert_bits(value, width):
            return (~value) & ((1 << width) - 1)

        # Generate transactions with alternating bit patterns
        for i in range(count):
            pattern_type = i % 4

            if pattern_type == 0:
                # All 1s in addr, alternating in ctrl and data
                addr = addr_mask
                ctrl = alternating_ones(ctrl_width) & ctrl_mask

                if 'data0' in field_config.field_names() and 'data1' in field_config.field_names():
                    # Multi-data configuration
                    data_dict = {
                        'data0': alternating_ones(32) & 0xFFFFFFFF,
                        'data1': invert_bits(alternating_ones(32), 32) & 0xFFFFFFFF
                    }
                    sequence.add_write(addr, data_dict, {'ctrl': ctrl})
                else:
                    # Single data field
                    data = alternating_ones(32) & 0xFFFFFFFF
                    sequence.add_write(addr, data, {'ctrl': ctrl})

            elif pattern_type == 1:
                # All 0s in addr, inverted alternating in ctrl and data
                addr = 0
                ctrl = invert_bits(alternating_ones(ctrl_width), ctrl_width) & ctrl_mask

                if 'data0' in field_config.field_names() and 'data1' in field_config.field_names():
                    # Multi-data configuration
                    data_dict = {
                        'data0': invert_bits(alternating_ones(32), 32) & 0xFFFFFFFF,
                        'data1': alternating_ones(32) & 0xFFFFFFFF
                    }
                    sequence.add_write(addr, data_dict, {'ctrl': ctrl})
                else:
                    # Single data field
                    data = invert_bits(alternating_ones(32), 32) & 0xFFFFFFFF
                    sequence.add_write(addr, data, {'ctrl': ctrl})

            elif pattern_type == 2:
                # Alternating in addr, all 1s in ctrl, all 0s in data
                addr = alternating_ones(addr_width) & addr_mask
                ctrl = ctrl_mask

                if 'data0' in field_config.field_names() and 'data1' in field_config.field_names():
                    # Multi-data configuration
                    data_dict = {
                        'data0': 0,
                        'data1': 0xFFFFFFFF
                    }
                    sequence.add_write(addr, data_dict, {'ctrl': ctrl})
                else:
                    # Single data field
                    data = 0
                    sequence.add_write(addr, data, {'ctrl': ctrl})

            else:  # pattern_type == 3
                # Inverted alternating in addr, all 0s in ctrl, all 1s in data
                addr = invert_bits(alternating_ones(addr_width), addr_width) & addr_mask
                ctrl = 0

                if 'data0' in field_config.field_names() and 'data1' in field_config.field_names():
                    # Multi-data configuration
                    data_dict = {
                        'data0': 0xFFFFFFFF,
                        'data1': 0
                    }
                    sequence.add_write(addr, data_dict, {'ctrl': ctrl})
                else:
                    # Single data field
                    data = 0xFFFFFFFF
                    sequence.add_write(addr, data, {'ctrl': ctrl})

            # Small delay between transactions
            sequence.add_delay(2)

        return sequence

    @staticmethod
    def create_clock_ratio_test_sequence(name: str, field_config: FieldConfig, count: int = 20):
        """
        Create a sequence specifically designed to test async clock domain crossing.

        Args:
            name: Sequence name
            field_config: Field configuration
            count: Number of transactions

        Returns:
            Configured GAXISequence
        """
        sequence = GAXISequence(name, field_config)

        # Determine if we have multi-field config
        has_multi_fields = len(field_config.field_names()) > 1

        # Generate transactions with varying delays (stress CDC logic)
        for i in range(count):
            addr = i * 4
            data = i & 0xFFFFFFFF

            # For multi-field configurations
            if has_multi_fields and 'ctrl' in field_config.field_names():
                ctrl = i & 0xFF

                if 'data0' in field_config.field_names() and 'data1' in field_config.field_names():
                    # Multi-data configuration
                    data_dict = {
                        'data0': data & 0xFFFFFFFF,
                        'data1': (data << 8) & 0xFFFFFFFF
                    }
                    sequence.add_write(addr, data_dict, {'ctrl': ctrl})
                else:
                    sequence.add_write(addr, data, {'ctrl': ctrl})
            else:
                sequence.add_write(addr, data)

            # Add periodic delays to stress CDC logic
            if i % 5 == 0:
                sequence.add_delay(3)
            else:
                sequence.add_delay(1)

        return sequence

    @staticmethod
    def create_custom_sequence(name: str, field_config: FieldConfig, transaction_list: List[Dict[str, Any]]):
        """
        Create a sequence from a list of pre-defined transactions.

        Args:
            name: Sequence name
            field_config: Field configuration
            transaction_list: List of transaction specifications
                Each dict should have: addr, data (or data_dict), ctrl (optional), delay (optional)

        Returns:
            Configured GAXISequence
        """
        sequence = GAXISequence(name, field_config)

        # Process each transaction in the list
        for transaction in transaction_list:
            addr = transaction.get('addr', 0)
            data = transaction.get('data')
            data_dict = transaction.get('data_dict')
            ctrl = transaction.get('ctrl')
            delay = transaction.get('delay', 0)

            # Extra fields if ctrl is specified
            extra_fields = {'ctrl': ctrl} if ctrl is not None else None

            # Add transaction
            if data_dict is not None:
                sequence.add_write(addr, data_dict, extra_fields)
            else:
                sequence.add_write(addr, data, extra_fields)

            # Add delay if specified
            if delay > 0:
                sequence.add_delay(delay)

        return sequence
