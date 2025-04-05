"""FIFO Monitor Component with required and optional signal support"""
import cocotb
from collections import deque
from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time

from ..flex_randomizer import FlexRandomizer
from .fifo_packet import FIFOPacket
from CocoTBFramework.components.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.debug_object import print_object_details, print_dict_to_log


# Standard Signal names for all master/slave/monitor objects
fifo_write = 'i_write'
fifo_wr_full = 'o_wr_full'
fifo_wr_data = 'i_wr_data'
fifo_read = 'i_read'
fifo_rd_empty = 'o_rd_empty'
fifo_rd_data = 'o_rd_data'
fifo_rd_data_wire = 'ow_rd_data'  # for fifo_mux mode

fifo_valid_modes = ['skid', 'fifo_mux', 'fifo_flop']

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
    Monitor for FIFO bus transactions.
    Observes signals without driving anything.

    Supports:
    1. Single data bus (standard mode)
    2. Individual signals for each field (multi-signal mode)
    3. Optional signals with fallback behavior
    """
    def __init__(self, dut, title, prefix, clock, is_slave=False,
                    field_config=None, packet_class=FIFOPacket, timeout_cycles=1000,
                    multi_sig=False, log=None, mode='skid', signal_map=None, optional_signal_map=None, **kwargs):
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
            log: Logger instance
            multi_sig: Use multiple signals or not
            mode: Operating mode ('skid', 'fifo_mux', 'fifo_flop')
                    In 'fifo_mux' mode (slave side), use 'ow_rd_data' instead of 'o_rd_data'.
                    In 'fifo_flop' mode, capture data one clock after read handshake.
            signal_map: Dictionary mapping required FIFO signals to DUT signals
            optional_signal_map: Dictionary mapping optional FIFO signals to DUT signals
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

        # Handle field_config - convert dict to FieldConfig if needed
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        else:
            self.field_config = field_config or FieldConfig.create_data_only()

        self.packet_class = packet_class
        self.is_slave = is_slave
        self.mode = mode

        # Determine if we're using multi-signal mode
        self.use_multi_signal = multi_sig

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
            if mode == 'fifo_mux':
                self.data_name = fifo_rd_data_wire
            else:
                self.data_name = fifo_rd_data
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

        # Debug output
        self.log.info(f"FIFOMonitor initialized for {title} in mode '{mode}', "
                        f"{'read' if is_slave else 'write'} port, "
                        f"{'multi-signal' if self.use_multi_signal else 'standard'} mode")
        print_object_details(self, self.log, f"FIFOMonitor '{self.title}' INIT")

        self.log.info(f"Field config items count: {len(self.field_config)}")
        for field_name in self.field_config.field_names():
            field_def = self.field_config.get_field(field_name)
            self.log.info(f"Field {field_name}: bits={field_def.bits}, default={field_def.default}")

    def _initialize_multi_signal_mode(self):
        """Initialize signal mappings for multi-signal mode."""
        # Process each field in the field config
        for field_name in self.field_config.field_names():
            # Create the signal name for this field based on read/write port
            if self.is_slave:
                field_signal_name = f'o_rd_data_{field_name}'
            else:
                field_signal_name = f'i_wr_data_{field_name}'

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
        Collect data from field signals in multi-signal mode.

        Returns:
            Dictionary of field values
        """
        data_dict = {}

        if self.use_multi_signal:
            # Multi-signal mode: collect from individual field signals
            for field_name, dut_signal_name in self.field_signals.items():
                if hasattr(self.bus, dut_signal_name):
                    signal = getattr(self.bus, dut_signal_name)
                    if signal.value.is_resolvable:
                        field_value = int(signal.value)
                        # Check field value against maximum
                        field_value = self._check_field_value(field_name, field_value)
                        data_dict[field_name] = field_value
                    else:
                        self.log.warning(f"Field {field_name} has X/Z value")
                        data_dict[field_name] = -1  # Indicate X/Z value
                else:
                    self.log.debug(f"Signal {dut_signal_name} not found on DUT")
        elif self.data_sig:
            if self.data_sig.value.is_resolvable:
                # In standard mode with a single 'data' field
                if hasattr(self.field_config, 'has_field') and self.field_config.has_field('data'):
                    field_value = int(self.data_sig.value)
                    # Check value against field's maximum
                    field_value = self._check_field_value('data', field_value)
                    data_dict['data'] = field_value
                else:
                    # Handle multi-field configuration in standard mode
                    data_dict['data'] = int(self.data_sig.value)
            else:
                self.log.warning("Data signal has X/Z value")
                data_dict['data'] = -1  # Indicate X/Z value

        return data_dict

    def _update_fifo_depth(self, is_write):
        """
        Update the estimated FIFO depth based on the operation.

        Args:
            is_write: True for write, False for read

        Returns:
            Updated FIFO depth
        """
        prev_depth = self.fifo_depth

        if is_write:
            # Write operation - increment depth if not full
            if self.fifo_depth < self.fifo_capacity:
                self.fifo_depth += 1
            else:
                self._update_fifo_depth_helper(
                    '): Write to full FIFO detected', 'write_to_full'
                )
        elif self.fifo_depth > 0:
            self.fifo_depth -= 1
        else:
            self._update_fifo_depth_helper(
                '): Read from empty FIFO detected', 'read_from_empty'
            )
        return self.fifo_depth

    def _update_fifo_depth_helper(self, arg0, arg1):
                # FIFO is full - log error
        self.log.warning(f"FIFOMonitor ({self.title}{arg0}")

    def _finish_packet(self, current_time, packet, data_dict=None):
        """
        Finish packet processing and add to the observed queue.
        
        Args:
            current_time: Current simulation time
            packet: The packet being processed
            data_dict: Dictionary with field values or raw data value
        """
            # Extract individual fields from the combined data value
        if isinstance(data_dict, dict) and 'data' in data_dict:
            if not self.use_multi_signal and self.is_slave:
                # Extract fields based on field configuration
                if hasattr(self.field_config, 'field_names'):
                    field_values = {}
                    bit_offset = 0

                    # Process fields in reverse order from how they appear in the output
                    # If the format is [id][data3][data2][data1][data0], we need to extract
                    # from LSB to MSB: data0, data1, data2, data3, id
                    fields = self.field_config.field_names()

                    combined_value = data_dict['data']

                    for field_name in fields:
                        field_def = self.field_config.get_field(field_name)
                        field_width = field_def.bits
                        mask = (1 << field_width) - 1

                        # Extract field value from the combined data
                        field_value = (combined_value >> bit_offset) & mask
                        field_values[field_name] = field_value
                        bit_offset += field_width

                    # Replace data_dict with extracted fields
                    data_dict = field_values

        # The rest of the method remains the same
        if data_dict:
            for field_name, value in data_dict.items():
                if hasattr(packet, field_name):
                    setattr(packet, field_name, value)

        # Set end time and add to observed queue
        packet.end_time = current_time
        self.observed_queue.append(packet)
        self.log.debug(f"FIFOMonitor({self.title}) Transaction at {current_time}ns: {packet.formatted(compact=True) if hasattr(packet, 'formatted') else str(packet)}")
        self._recv(packet)  # Trigger callbacks

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

                        if self.mode == 'fifo_flop':
                            # Schedule capture for next cycle
                            pending_capture = True
                            pending_packet = packet
                        else:
                            # Capture data immediately from the data signal
                            if self.use_multi_signal:
                                data_dict = self._get_data_dict()
                            elif self.data_sig and self.data_sig.value.is_resolvable:
                                data_value = int(self.data_sig.value)
                                # Process the data correctly according to the field configuration
                                # This is where the current implementation might have issues
                                data_dict = {'data': data_value}
                            else:
                                self.log.warning("Data signal has X/Z value")
                                data_dict = {'data': -1}  # Indicate X/Z as -1

                            self._finish_packet(current_time, packet, data_dict)

                    elif (self.control2_sig.value.is_resolvable and
                            int(self.control2_sig.value) == 1 and
                            self.control1_sig.value.is_resolvable and
                            int(self.control1_sig.value) == 1):  # read while empty

                        self.log.warning(f"FIFOMonitor ({self.title}): Read from empty FIFO at {current_time}ns")
                elif self.control1_sig.value.is_resolvable:
                    if int(self.control1_sig.value) == 1:
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

                            self.log.warning(f"FIFOMonitor ({self.title}): Write to full FIFO at {current_time}ns")

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

        return result

    def clear_queue(self):
        """Clear the observed transactions queue after scoreboard validation."""
        self.observed_queue.clear()
        self.log.info(f"FIFOMonitor ({self.title}): Observed queue cleared")
