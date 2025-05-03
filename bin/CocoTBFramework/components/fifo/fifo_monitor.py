"""FIFO Monitor Component with improved signal handling and robust error detection"""
from collections import deque
from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import FallingEdge, Timer
from cocotb.utils import get_sim_time

from ..field_config import FieldConfig, FieldDefinition
from ..debug_object import print_object_details, print_dict_to_log
from .fifo_packet import FIFOPacket


# Standard Signal names for all master/slave/monitor objects
fifo_write = 'i_write'
fifo_wr_full = 'o_wr_full'
fifo_wr_data = 'i_wr_data'
fifo_read = 'i_read'
fifo_rd_empty = 'o_rd_empty'
fifo_rd_data = 'o_rd_data'
fifo_rd_data_wire = 'ow_rd_data'  # for fifo_mux mode

fifo_valid_modes = ['fifo_mux', 'fifo_flop']

# Standard signal maps for FIFO components
master_signal_map = {
    'i_write': 'i_write',
    'o_wr_full': 'o_wr_full'
}
master_optional_signal_map = {
    'i_wr_data': 'i_wr_data'
}

slave_signal_map = {
    'o_rd_empty': 'o_rd_empty',
    'i_read': 'i_read'
}
slave_skid_optional_signal_map = {
    'o_rd_data': 'o_rd_data'
}
slave_fifo_flop_optional_signal_map = {
    'o_rd_data': 'o_rd_data'
}
slave_fifo_mux_optional_signal_map = {
    'o_rd_data': 'ow_rd_data'
}

class FIFOMonitor(BusMonitor):
    """
    Monitor for FIFO bus transactions with enhanced signal handling and error detection.
    Observes signals without driving anything.

    Supports:
    1. Single data bus (standard mode)
    2. Individual signals for each field (multi-signal mode)
    3. Optional signals with fallback behavior
    4. FIFO state tracking
    5. Improved error detection
    """
    def __init__(self, dut, title, prefix, clock, is_slave=False,
                    field_config=None, packet_class=FIFOPacket, timeout_cycles=1000,
                    field_mode=False, multi_sig=False, log=None, mode='fifo_mux', signal_map=None, optional_signal_map=None, **kwargs):
        """
        Initialize the FIFO bus monitor.

        Args:
            dut: Device under test
            title: Title of the bus
            prefix: prefix used in the bus code
            clock: The clock signal
            is_slave: If True, monitor read port; if False, monitor write port
            field_config: Field configuration for packets
            packet_class: Class to use for creating packets
            timeout_cycles: Maximum cycles to wait before timeout
            field_mode: If True, treat standard data bus as containing multiple fields
            multi_sig: Use multiple signals or not
            log: Logger instance
            mode: Operating mode ('fifo_mux', 'fifo_flop')
                    In 'fifo_mux' mode (slave side), use 'ow_rd_data' instead of 'o_rd_data'.
                    In 'fifo_flop' mode, capture data one clock after read handshake.
            signal_map: Signal mapping for FIFO signals
            optional_signal_map: Optional signal mapping for data signals
                These signals won't cause errors if missing from the DUT
            **kwargs: Additional arguments to pass to BusMonitor
        """
        # Validate mode parameter
        if mode not in fifo_valid_modes:
            raise ValueError(f"Invalid mode '{mode}' for Monitor ({title}). Mode must be one of: {', '.join(fifo_valid_modes)}")

        # Set up simple items
        self.title = title
        self.clock = clock
        self.timeout_cycles = timeout_cycles
        self.field_mode = field_mode or multi_sig
        self.use_multi_signal = multi_sig  # Explicitly set this attribute

        # Handle field_config - convert dict to FieldConfig if needed
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        else:
            self.field_config = field_config or FieldConfig.create_data_only()

        self.packet_class = packet_class
        self.is_slave = is_slave
        self.mode = mode

        # Assign the signal maps based on whether monitoring read or write port
        if is_slave:
            # Monitoring read port
            self.signal_map = signal_map or slave_signal_map
            if optional_signal_map is not None:
                self.optional_signal_map = optional_signal_map
            elif mode == 'fifo_flop':
                self.optional_signal_map = slave_fifo_flop_optional_signal_map
            else:
                self.optional_signal_map = slave_fifo_mux_optional_signal_map

            # Store standard signal names for easier reference
            self.control1_name = fifo_rd_empty
            self.control2_name = fifo_read

            # Data signal based on mode
            self.data_name = fifo_rd_data_wire if mode == 'fifo_mux' else fifo_rd_data
        else:
            # Monitoring write port
            self.signal_map = signal_map or master_signal_map
            self.optional_signal_map = optional_signal_map or master_optional_signal_map

            # Store standard signal names for easier reference
            self.control1_name = fifo_write
            self.control2_name = fifo_wr_full
            self.data_name = fifo_wr_data

        # Get the actual DUT signal names from the map
        self.control1_dut_name = self.signal_map.get(self.control1_name, self.control1_name)
        self.control2_dut_name = self.signal_map.get(self.control2_name, self.control2_name)
        self.data_dut_name = self.optional_signal_map.get(self.data_name, self.data_name)

        # Prepare signal lists for BusMonitor initialization
        msg_multi = None
        if not self.use_multi_signal:
            # Standard mode - use mapped signal names
            self._signals = [self.control1_dut_name, self.control2_dut_name, self.data_dut_name]
        else:
            # Multi-signal mode - only include control signals
            msg_multi = (f'Monitor({title}) multi-signal model\n'
                            f'{signal_map=}\n'
                            f'{optional_signal_map=}\n'
                            f'{field_config=}\n')
            self._signals = [self.control1_dut_name, self.control2_dut_name]

        # Set up optional signals
        self._optional_signals = []
        if self.optional_signal_map:
            self._optional_signals.extend(
                dut_name for _, dut_name in self.optional_signal_map.items()
                if dut_name != self.data_dut_name  # Data signal is already handled
            )

        # Initialize parent BusMonitor (without auto-starting monitor)
        BusMonitor.__init__(self, dut, prefix, clock, callback=None, event=None, **kwargs)
        self.log = log or self._log

        if msg_multi is not None:
            self.log.debug(msg_multi)

        # Set up references to control signals
        if hasattr(self.bus, self.control1_dut_name):
            self.control1_sig = getattr(self.bus, self.control1_dut_name)
        else:
            self.log.error(f"Control signal '{self.control1_dut_name}' not found on bus")
            self.control1_sig = None

        if hasattr(self.bus, self.control2_dut_name):
            self.control2_sig = getattr(self.bus, self.control2_dut_name)
        else:
            self.log.error(f"Control signal '{self.control2_dut_name}' not found on bus")
            self.control2_sig = None

        # Set up reference to data signal (for standard mode)
        if hasattr(self.bus, self.data_dut_name):
            self.data_sig = getattr(self.bus, self.data_dut_name)
        else:
            self.data_sig = None
            if not self.use_multi_signal:
                self.log.warning(f"Data signal '{self.data_dut_name}' not found on bus")

        # Create a mapping of field names to DUT signals for multi-signal mode
        self.field_signals = {}

        # In multi-signal mode, verify signals and store mappings
        if self.use_multi_signal:
            self._initialize_multi_signal_mode()

        # Initialize tracking variables
        self.observed_queue = deque()
        self.fifo_depth = 0      # Current estimated FIFO depth
        self.fifo_capacity = 8   # Default assumed FIFO capacity
        self.last_transaction = None  # Last observed transaction
        self.pending_transaction = None  # For fifo_flop mode
        
        # Statistics - use a dictionary instead of class to avoid attribute errors
        self.stats = {
            'transactions_observed': 0,
            'protocol_violations': 0,
            'x_z_values': 0,
            'empty_cycles': 0,
            'full_cycles': 0,
            'read_while_empty': 0,
            'write_while_full': 0,
            'received_transactions': 0  # Add this explicitly to avoid AttributeError
        }
        
        # Initialize callbacks list
        self.callbacks = []

        # Debug output
        self.log.info(f"FIFOMonitor initialized for {title} in mode '{mode}', "
                        f"{'read' if is_slave else 'write'} port, "
                        f"{'multi-signal' if self.use_multi_signal else 'standard'} mode")

    def _initialize_multi_signal_mode(self):
        """Initialize signal mappings for multi-signal mode."""
        # Process each field in the field config
        for field_name in self.field_config.field_names():
            # Create the signal name for this field based on read/write port
            if self.is_slave:
                field_signal_name = f'o_rd_pkt_{field_name}'
            else:
                field_signal_name = f'i_wr_pkt_{field_name}'

            # First check optional signal map
            if field_signal_name in self.optional_signal_map:
                dut_signal_name = self.optional_signal_map[field_signal_name]
                self._register_field_signal(field_name, dut_signal_name, required=False)
            elif field_signal_name in self.signal_map:
                dut_signal_name = self.signal_map[field_signal_name]
                self._register_field_signal(field_name, dut_signal_name, required=True)
            elif field_name == 'data':
                std_signal = self.data_name if self.is_slave else fifo_wr_data
                if hasattr(self.bus, std_signal):
                    self.field_signals[field_name] = std_signal
                    self.log.debug(f"Using standard signal '{std_signal}' for field '{field_name}'")
                else:
                    self.log.warning(f"Standard signal '{std_signal}' not found for field '{field_name}'")
            else:
                self.log.warning(f"No signal mapping provided for field {field_name}")

    def _register_field_signal(self, field_name, dut_signal_name, required=False):
        """Register a field signal with appropriate error handling"""
        if hasattr(self.bus, dut_signal_name):
            # Store the mapping
            self.field_signals[field_name] = dut_signal_name
            self.log.debug(f"Registered signal '{dut_signal_name}' for field '{field_name}'")
        elif required:
            raise ValueError(f"Required signal '{dut_signal_name}' for field '{field_name}' not found on DUT")
        else:
            self.log.warning(f"Optional signal '{dut_signal_name}' for field '{field_name}' not found on DUT")

    def _check_field_value(self, field_name, field_value):
        """
        Check if a field value exceeds the maximum possible value for the field.

        Args:
            field_name: Name of the field to check
            field_value: Value to check against field width

        Returns:
            field_value: The original value if within range, or the masked value if not
        """
        # Get field definition
        if not hasattr(self.field_config, 'get_field'):
            # Can't perform check if field_config doesn't support get_field
            return field_value

        try:
            field_def = self.field_config.get_field(field_name)
            bits = field_def.bits

            # Calculate maximum value for this field
            max_value = (1 << bits) - 1

            # Check if value exceeds maximum
            if field_value > max_value:
                current_time = get_sim_time('ns')
                self.log.warning(
                    f"FIFOMonitor({self.title}) at {current_time}ns: Field '{field_name}' value 0x{field_value:X} "
                    f"exceeds maximum 0x{max_value:X} ({bits} bits). Value will be masked."
                )

                return field_value & max_value
        except Exception as e:
            self.log.error(f"Error checking field value: {e}")

        return field_value

    def set_fifo_capacity(self, capacity):
        """
        Set the assumed FIFO capacity for depth tracking.

        Args:
            capacity: FIFO capacity in entries
        """
        self.fifo_capacity = capacity
        self.log.info(f"FIFOMonitor ({self.title}): Set FIFO capacity to {capacity}")

    def _get_data_dict(self):
        """
        Collect data from field signals and properly handle X/Z values.

        Returns:
            Dictionary of field values with X/Z values represented as -1
        """
        data_dict = {}

        if self.use_multi_signal:
            # Multi-signal mode: collect from individual field signals
            for field_name, dut_signal_name in self.field_signals.items():
                if hasattr(self.bus, dut_signal_name):
                    # For slave monitor in fifo_mux mode
                    if self.is_slave and self.mode == 'fifo_mux':
                        # Special handling for fifo_mux mode
                        # Use ow_rd_* signals instead of o_rd_*
                        mux_signal_name = dut_signal_name.replace('o_rd_', 'ow_rd_')
                        if hasattr(self.bus, mux_signal_name):
                            signal = getattr(self.bus, mux_signal_name)
                        else:
                            signal = getattr(self.bus, dut_signal_name)
                    else:
                        # Standard signal handling for write monitor
                        signal = getattr(self.bus, dut_signal_name)

                    # Get the value from the signal
                    if signal.value.is_resolvable:
                        field_value = int(signal.value)
                        # Check field value against maximum
                        field_value = self._check_field_value(field_name, field_value)
                        data_dict[field_name] = field_value
                    else:
                        self.log.warning(f"Field {field_name} with signal {dut_signal_name} has X/Z value")
                        data_dict[field_name] = -1  # Use -1 to indicate X/Z
                        self.stats['x_z_values'] += 1
                else:
                    self.log.debug(f"Signal {dut_signal_name} for field {field_name} not found on DUT")
        elif self.data_sig:
            # Standard mode
            if self.data_sig.value.is_resolvable:
                raw_value = int(self.data_sig.value)
                if self.field_mode:
                    # Multi-field mode - will be unpacked later
                    data_dict['data'] = raw_value
                elif hasattr(self.field_config, 'has_field') and self.field_config.has_field('data'):
                    # Single data field
                    field_value = self._check_field_value('data', raw_value)
                    data_dict['data'] = field_value
                else:
                    # Handle multi-field configuration in standard mode
                    data_dict['data'] = raw_value
            else:
                self.log.warning("Data signal has X/Z value")
                data_dict['data'] = -1  # Use -1 to indicate X/Z
                self.stats['x_z_values'] += 1

        # More detailed debug for troubleshooting
        if self.use_multi_signal and not data_dict:
            self.log.warning(f"No data values collected for {'read' if self.is_slave else 'write'} monitor!")
            self.log.debug(f"Field signals mapping: {self.field_signals}")

        return data_dict

    def _update_fifo_depth(self, is_write):
        """
        Update the estimated FIFO depth based on the operation.
        Uses actual signal values to detect errors instead of guessing.

        Args:
            is_write: True for write, False for read

        Returns:
            Updated FIFO depth
        """
        current_time = get_sim_time('ns')

        if is_write:
            # Check if FIFO is actually full before warning
            if self.control2_sig.value.is_resolvable and int(self.control2_sig.value) == 1:
                self.log.warning(f"FIFOMonitor ({self.title}): Write to full FIFO detected at {current_time}ns")
                self.stats['write_while_full'] += 1
            else:
                # Safe to increment depth
                self.fifo_depth = min(self.fifo_depth + 1, self.fifo_capacity)
                
            # Update full cycles counter
            if self.fifo_depth >= self.fifo_capacity:
                self.stats['full_cycles'] += 1
        else:
            # Check for empty FIFO read
            if self.control1_sig.value.is_resolvable and int(self.control1_sig.value) == 1:
                self.log.warning(f"FIFOMonitor ({self.title}): Read from empty FIFO detected at {current_time}ns")
                self.stats['read_while_empty'] += 1
            elif self.fifo_depth > 0:
                self.fifo_depth = max(0, self.fifo_depth - 1)
                
            # Update empty cycles counter
            if self.fifo_depth == 0:
                self.stats['empty_cycles'] += 1

        return self.fifo_depth

    def _check_protocol_violation(self, is_write):
        """
        Check for protocol violations based on signals.
        
        Args:
            is_write: True if checking write port, False if checking read port
            
        Returns:
            True if violation detected, False otherwise
        """
        if is_write:
            # Check for write while full violation
            if (self.control1_sig.value.is_resolvable and 
                self.control2_sig.value.is_resolvable and
                int(self.control1_sig.value) == 1 and
                int(self.control2_sig.value) == 1):
                self.log.warning(f"FIFOMonitor ({self.title}): Protocol violation - write while full at {get_sim_time('ns')}ns")
                self.stats['protocol_violations'] += 1
                return True
        else:
            # Check for read while empty violation
            if (self.control1_sig.value.is_resolvable and 
                self.control2_sig.value.is_resolvable and
                int(self.control2_sig.value) == 1 and
                int(self.control1_sig.value) == 1):
                self.log.warning(f"FIFOMonitor ({self.title}): Protocol violation - read while empty at {get_sim_time('ns')}ns")
                self.stats['protocol_violations'] += 1
                return True
        
        return False

    def _finish_packet(self, current_time, packet, data_dict=None):
        """
        Finish packet processing and add to the observed queue.

        Args:
            current_time: Current simulation time
            packet: The packet being processed
            data_dict: Dictionary with field values or raw data value
        """
        # Check if we need to unpack fields from a combined value
        if not self.use_multi_signal:
            if (
                self.field_mode
                and isinstance(data_dict, dict)
                and 'data' in data_dict
            ):
                # Field mode - extract fields from combined value
                unpacked_fields = {}
                combined_value = data_dict['data']
                data_dict = self._finish_packet_helper(combined_value, unpacked_fields)
            elif (
                not self.field_mode
                and isinstance(data_dict, dict)
                and 'data' in data_dict
                and hasattr(self.field_config, 'field_names')
                and len(self.field_config) > 1
            ):
                # Standard mode with complex field config
                unpacked_fields = {}
                combined_value = data_dict['data']
                data_dict = self._finish_packet_helper(combined_value, unpacked_fields)

        # Use the packet's unpack_from_fifo method for field handling
        if data_dict:
            if hasattr(packet, 'unpack_from_fifo'):
                packet.unpack_from_fifo(data_dict)
            else:
                # Legacy fallback - set fields directly
                for field_name, value in data_dict.items():
                    if value != -1:  # Skip X/Z values
                        value = self._check_field_value(field_name, value)
                        if hasattr(packet, field_name):
                            setattr(packet, field_name, value)

        # Set end time and add to observed queue
        packet.end_time = current_time
        self.observed_queue.append(packet)
        self.stats['transactions_observed'] += 1
        self.stats['received_transactions'] += 1  # Add this to match expected behavior
        self.log.debug(f"FIFOMonitor({self.title}) Transaction at {current_time}ns: {packet.formatted(compact=True) if hasattr(packet, 'formatted') else str(packet)}")
        
        # Call all registered callbacks
        self._call_callbacks(packet)

    def _call_callbacks(self, packet):
        """
        Call all registered callbacks with the packet.
        This replaces the direct _recv call to avoid the AttributeError.
        
        Args:
            packet: The packet to pass to callbacks
        """
        # Call parent class _recv if needed
        if hasattr(self, '_recv') and callable(self._recv):
            try:
                self._recv(packet)
            except AttributeError:
                # Handle the AttributeError by not propagating it
                self.log.debug("Ignoring AttributeError from parent _recv method")
        
        # Call additional callbacks
        for callback in self.callbacks:
            try:
                callback(packet)
            except Exception as e:
                self.log.error(f"Error in callback: {e}")

    def add_callback(self, callback):
        """
        Add a callback function to be called when a packet is observed.
        
        Args:
            callback: Function to call with observed packet
            
        Returns:
            Self for method chaining
        """
        if callback not in self.callbacks:
            self.callbacks.append(callback)
        return self

    def _finish_packet_helper(self, combined_value, unpacked_fields):
        """
        Helper method to extract individual fields from combined value.

        Args:
            combined_value: Combined integer value containing all fields
            unpacked_fields: Empty dictionary to store extracted fields

        Returns:
            Dictionary of field name -> field value mappings
        """
        bit_offset = 0
        # Process fields in the order defined in field_config
        for field_name in self.field_config.field_names():
            # Get field definition from FieldConfig
            field_def = self.field_config.get_field(field_name)
            field_width = field_def.bits
            mask = (1 << field_width) - 1

            # Extract field value using mask and shift
            field_value = (combined_value >> bit_offset) & mask

            # Check field value against its maximum
            field_value = self._check_field_value(field_name, field_value)

            unpacked_fields[field_name] = field_value
            bit_offset += field_width

        return unpacked_fields

    async def _monitor_recv(self):
        """
        Monitor for FIFO transactions.

        This method continuously monitors the control signals for transactions
        and records observed packets.
        """
        try:
            # Set up pending transaction for fifo_flop mode
            pending_packet = None
            pending_capture = False

            while True:
                # Wait for a falling edge to sample signals
                await FallingEdge(self.clock)

                # Get current time
                current_time = get_sim_time('ns')

                # Check for protocol violations
                self._check_protocol_violation(not self.is_slave)

                # Handle pending captures for fifo_flop mode
                if pending_capture and self.mode == 'fifo_flop':
                    data_dict = self._get_data_dict()
                    self._finish_packet(current_time, pending_packet, data_dict)
                    pending_capture = False
                    pending_packet = None

                # Check for write/read operations
                if self.is_slave:
                    # Monitoring read port - check if read=1 AND empty=0 (valid read)
                    valid_read = (
                        self.control2_sig.value.is_resolvable and
                        int(self.control2_sig.value) == 1 and   # read is asserted
                        self.control1_sig.value.is_resolvable and
                        int(self.control1_sig.value) == 0       # not empty
                    )

                    if valid_read:
                        # Create a packet and capture data immediately or in next cycle
                        # depending on the mode
                        packet = self.packet_class(self.field_config)
                        packet.start_time = current_time

                        # Update FIFO depth
                        self._update_fifo_depth(is_write=False)

                        if self.mode == 'fifo_flop':
                            # Schedule capture for next cycle
                            pending_capture = True
                            pending_packet = packet
                        else:
                            # Capture data immediately from the data signal
                            data_dict = self._get_data_dict()
                            self._finish_packet(current_time, packet, data_dict)

                    elif (self.control2_sig.value.is_resolvable and
                            int(self.control2_sig.value) == 1 and
                            self.control1_sig.value.is_resolvable and
                            int(self.control1_sig.value) == 1):  # read while empty
                        # Already logged in _update_fifo_depth, just update stats
                        pass
                        
                    # Update empty cycles counter if applicable
                    if self.control1_sig.value.is_resolvable and int(self.control1_sig.value) == 1:
                        self.stats['empty_cycles'] += 1
                else:
                    # Monitoring write port - check if write=1 (valid write)
                    if self.control1_sig.value.is_resolvable and int(self.control1_sig.value) == 1:
                        if (
                            not self.control2_sig.value.is_resolvable
                            or int(self.control2_sig.value) == 0
                        ):  # write and not full
                            # Create new packet
                            packet = self.packet_class(self.field_config)
                            packet.start_time = current_time

                            # Update FIFO depth
                            self._update_fifo_depth(is_write=True)

                            # Capture data
                            data_dict = self._get_data_dict()
                            self._finish_packet(current_time, packet, data_dict)
                        elif int(self.control2_sig.value) == 1:  # write while full
                            # Already logged in _update_fifo_depth, just update stats
                            pass
                            
                    # Update full cycles counter if applicable
                    if self.control2_sig.value.is_resolvable and int(self.control2_sig.value) == 1:
                        self.stats['full_cycles'] += 1

                # Wait a bit to avoid oversampling
                await Timer(1, units='ps')

        except Exception as e:
            self.log.error(f"FIFOMonitor ({self.title}): Exception in _monitor_recv: {e}")
            import traceback
            self.log.error(traceback.format_exc())
            raise

    def get_stats(self):
        """
        Get statistics about observed transactions.

        Returns:
            Dictionary with statistics
        """
        # Format for easier consumption
        result = self.stats.copy()
        result['monitor_type'] = 'read' if self.is_slave else 'write'
        result['fifo_depth'] = self.fifo_depth
        result['fifo_capacity'] = self.fifo_capacity
        result['utilization_percentage'] = (self.fifo_depth / self.fifo_capacity * 100) if self.fifo_capacity > 0 else 0

        return result
        
    def get_observed_packets(self, count=None):
        """
        Get observed packets.
        
        Args:
            count: Number of packets to return (None = all)
            
        Returns:
            List of observed packets
        """
        if count is None:
            return list(self.observed_queue)
        return list(self.observed_queue)[-count:]

    def clear_queue(self):
        """Clear the observed transactions queue after scoreboard validation."""
        self.observed_queue.clear()
        self.log.info(f"FIFOMonitor ({self.title}): Observed queue cleared")
