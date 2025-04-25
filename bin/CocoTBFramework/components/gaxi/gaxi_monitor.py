"""GAXI Monitor Component with required and optional signal support"""
import pprint

from collections import deque
from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import FallingEdge, Timer
from cocotb.utils import get_sim_time

from ..field_config import FieldConfig
from ..debug_object import print_object_details, print_dict_to_log
from .gaxi_packet import GAXIPacket


# Standard Signal names for all master/sllave/monitor objects
gaxi_valid = 'm2s_valid'
gaxi_ready = 's2m_ready'
gaxi_pkt = 'm2s_pkt'
gaxi_valid_modes = ['skid', 'fifo_mux', 'fifo_flop']

# Standard signal maps for GAXI components
master_signal_map = {
            'm2s_valid': 'i_wr_valid',
            's2m_ready': 'o_wr_ready'
}
master_optional_signal_map = {
            'm2s_pkt': 'i_wr_data'
}

slave_signal_map = {
            'm2s_valid': 'o_rd_valid',
            's2m_ready': 'i_rd_ready'
}
slave_skid_optional_signal_map = {
            'm2s_pkt': 'o_rd_data'
}
slave_fifo_flop_optional_signal_map = {
            'm2s_pkt': 'o_rd_data'
}
slave_fifo_mux_optional_signal_map = {
            'm2s_pkt': 'ow_rd_data'
}


class GAXIMonitor(BusMonitor):
    """
    Monitor for GAXI bus transactions.
    Observes valid/ready handshake without driving signals.

    Supports:
    1. Single data bus (standard mode)
    2. Individual signals for each field (multi-signal mode)
    3. Optional signals with fallback behavior
    """
    def __init__(self, dut, title, prefix, clock, is_slave=False,
                    field_config=None, packet_class=GAXIPacket, timeout_cycles=1000,
                    field_mode=False, multi_sig=False, log=None, mode='skid', signal_map=None, optional_signal_map=None, **kwargs):
        # sourcery skip: low-code-quality
        """
        Initialize the GAXI bus monitor.

        Args:
            dut: Device under test
            title: Title of the bus
            prefix: prefix used in the bus code
            clock: The clock signal
            is_slave: If True, use slave signals; if False, use master signals
            field_config: Field configuration for packets
            packet_class: Class to use for creating packets
            timeout_cycles: Maximum cycles to wait before timeout
            log: Logger instance
            multi_sig: Use multiple signals or not
            mode: Operating mode ('skid', 'fifo_mux', 'fifo_flop')
                    In 'fifo_mux' mode (slave side), use 'ow_rd_data' instead of 'm2s_pkt'.
                    In 'fifo_flop' mode, capture data one clock after valid/ready handshake.
            signal_map: Dictionary mapping required GAXI signals to DUT signals
                Format depends on is_slave parameter:
                - Slave: {'m2s_valid': 'dut_valid', 's2m_ready': 'dut_ready', ...}
                - Master: {'m2s_valid': 'dut_valid', 's2m_ready': 'dut_ready', ...}
            optional_signal_map: Dictionary mapping optional GAXI signals to DUT signals
                These signals won't cause errors if missing from the DUT
            **kwargs: Additional arguments to pass to BusMonitor
        """
        # Validate mode parameter
        if mode not in gaxi_valid_modes:
            raise ValueError(f"Invalid mode '{mode}' for Monitor ({title}). Mode must be one of: {', '.join(gaxi_valid_modes)}")

        # Set up simple items
        self.title = title
        self.clock = clock
        self.timeout_cycles = timeout_cycles
        self.field_mode = field_mode or multi_sig

        # Handle field_config - convert dict to FieldConfig if needed
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        else:
            self.field_config = field_config or FieldConfig.create_data_only()
        self.packet_class = packet_class or GAXIPacket
        self.is_slave = is_slave
        self.mode = mode

        # Determine if we're using multi-signal mode
        self.use_multi_signal = multi_sig

        # Assign the signal maps
        if is_slave:
            self.signal_map = signal_map or slave_signal_map
        else:
            self.signal_map = signal_map or master_signal_map

        if optional_signal_map is not None:
            self.optional_signal_map = optional_signal_map
        elif not is_slave:
            self.optional_signal_map = master_optional_signal_map
        elif mode == 'skid':
            self.optional_signal_map = slave_skid_optional_signal_map
        elif mode == 'fifo_flop':
            self.optional_signal_map = slave_fifo_flop_optional_signal_map
        else:
            self.optional_signal_map = slave_fifo_mux_optional_signal_map

        # Store standard signal names for easier reference
        self.valid_name = 'm2s_valid'
        self.ready_name = 's2m_ready'
        self.pkt_name = 'm2s_pkt'

        # Get the actual DUT signal names from the map
        self.valid_dut_name = self.signal_map.get(self.valid_name, self.valid_name)
        self.ready_dut_name = self.signal_map.get(self.ready_name, self.ready_name)
        self.pkt_dut_name = self.optional_signal_map.get(self.pkt_name, self.pkt_name)

        # Prepare signal lists for BusMonitor initialization
        msg_multi = None
        if not self.use_multi_signal:
            # Standard mode - use mapped signal names
            self._signals = [self.valid_dut_name, self.ready_dut_name, self.pkt_dut_name]
        else:
            # Multi-signal mode - only include valid/ready with mapped names
            msg_multi = (f'Slave({title}) multi-signal model\n'
                            f'{signal_map=}\n'
                            f'{optional_signal_map=}\n'
                            f'{field_config=}\n')
            self._signals = [self.valid_dut_name, self.ready_dut_name]

        # Set up optional signals
        self._optional_signals = []
        if self.optional_signal_map:
            self._optional_signals.extend(
                dut_name for _, dut_name in self.optional_signal_map.items()
            )

        # Initialize base BusMonitor (don't auto-start monitoring)
        BusMonitor.__init__(self, dut, prefix, clock, callback=None, event=None, **kwargs)
        self.log = log or self._log
        self.log.debug(f"GAXIMonitor init for '{title}': mode={mode}")
        # if msg_multi is not None:
        #     self.log.debug(msg_multi)

        # Set up references to valid and ready signals
        if hasattr(self.bus, self.valid_dut_name):
            self.valid_sig = getattr(self.bus, self.valid_dut_name)
        else:
            self.log.error(f"Valid signal '{self.valid_dut_name}' not found on bus")
            self.valid_sig = None

        if hasattr(self.bus, self.ready_dut_name):
            self.ready_sig = getattr(self.bus, self.ready_dut_name)
        else:
            self.log.error(f"Ready signal '{self.ready_dut_name}' not found on bus")
            self.ready_sig = None

        # Set up reference to packet signal (for standard mode)
        if hasattr(self.bus, self.pkt_dut_name):
            self.pkt_sig = getattr(self.bus, self.pkt_dut_name)
        else:
            self.pkt_sig = None

        # Initialize queue for observed transactions
        self.observed_queue = deque()

        # Create a mapping of field names to DUT signals for multi-signal mode
        self.field_signals = {}

        if self.use_multi_signal:
            self._initialize_multi_signal_mode()

        # Debug output
        self.log.info(f"GAXIMonitor initialized for {title} in mode '{mode}', {'multi-signal' if self.use_multi_signal else 'standard'}")
        # print_object_details(self, self.log, f"GAXI Monitor '{self.title}' INIT")
        # print_object_details(self.field_config, self.log, f"GAXI Monitor Field Config'{self.title}' INIT")
        # print_object_details(self.field_signals, self.log, f"GAXI Monitor Field Signals'{self.title}' INIT")

    def clear_queue(self):
        """Clear the observed transactions queue after scoreboard validation."""
        self.observed_queue.clear()
        self.log.info(f"GAXIMonitor ({self.title}): Observed queue cleared after scoreboard check.")

    def _initialize_multi_signal_mode(self):
        """Initialize signal mappings for multi-signal mode with fallback to standard signals."""
        # Check field signal mappings
        for field_name in self.field_config.field_names():
            field_signal_name = f'm2s_pkt_{field_name}'

            # Check required signal map first
            if field_signal_name in self.signal_map:
                dut_signal_name = self.signal_map[field_signal_name]
                self._register_field_signal(field_name, dut_signal_name, required=True)

            # Then check optional signal map
            elif field_signal_name in self.optional_signal_map:
                dut_signal_name = self.optional_signal_map[field_signal_name]
                self._register_field_signal(field_name, dut_signal_name, required=False)

            else:
                self.log.warning(f"GAXIMonitor({self.title}): No signal mapping provided for field {field_name}")

    def _register_field_signal(self, field_name, dut_signal_name, required=True):
        """Register a field signal with appropriate error handling"""
        # Verify signal exists on DUT
        if hasattr(self.bus, dut_signal_name):
            # Store the mapping
            self.field_signals[field_name] = dut_signal_name
            # self.log.debug(f"Registered signal '{dut_signal_name}' for field '{field_name}'")
        elif required:
            # Signal is required but not found
            raise ValueError(f"Required signal '{dut_signal_name}' for field '{field_name}' not found on DUT")
        else:
            # Optional signal not found - log warning
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
                    f"GAXIMonitor({self.title}) at {current_time}ns: Field '{field_name}' value 0x{field_value:X} "
                    f"exceeds maximum 0x{max_value:X} ({bits} bits). Value will be masked."
                )

                return field_value & max_value
        except Exception as e:
            self.log.error(f"Error checking field value: {e}")

        return field_value

    def _finish_packet(self, current_time, packet, data_dict=None):
        """
        Finish packet processing and trigger callbacks.

        Args:
            current_time: Current simulation time
            packet: The packet to finish
            data_dict: Dictionary of field data (for multi-signal mode)
                    or single 'data' value (for standard mode)
        """
        # Check if we need to unpack fields from a combined value
        if not self.use_multi_signal:
            if (
                hasattr(self, 'field_mode')
                and self.field_mode
                and isinstance(data_dict, dict)
                and 'data' in data_dict
            ):
                unpacked_fields = {}
                combined_value = data_dict['data']
                data_dict = self._finish_packet_helper(
                    combined_value, unpacked_fields
                )
            elif (
                not hasattr(self, 'field_mode')
                and hasattr(self.field_config, 'field_names')
                and len(self.field_config) > 1
                and isinstance(data_dict, dict)
                and 'data' in data_dict
            ):
                # Legacy mode: Standard mode with complex field config
                combined_value = data_dict['data']
                unpacked_fields = {}
                data_dict = self._finish_packet_helper(
                    combined_value, unpacked_fields
                )
        # Use the packet's unpack_from_fifo method for field handling
        if data_dict:
            if hasattr(packet, 'unpack_from_fifo'):
                packet.unpack_from_fifo(data_dict)
            else:
                # Legacy fallback - set fields directly
                for field_name, value in data_dict.items():
                    # Check field value here too for legacy packets
                    value = self._check_field_value(field_name, value)
                    if hasattr(packet, field_name):
                        setattr(packet, field_name, value)

        # Record completion time and store packet
        packet.end_time = current_time
        self.observed_queue.append(packet)
        # Format packet for logging if it has a formatted method
        packet_str = packet.formatted(compact=True) if hasattr(packet, 'formatted') else str(packet)
        self.log.debug(f"Monitor({self.title}) Transaction received at {packet.end_time}ns: {packet_str}")
        self._recv(packet)  # trigger callbacks

    def _finish_packet_helper(self, combined_value, unpacked_fields):
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
        elif self.pkt_sig:
            if self.pkt_sig.value.is_resolvable:
                # Get raw value
                raw_value = int(self.pkt_sig.value)
                # Store according to field_mode
                if hasattr(self, 'field_mode') and self.field_mode:
                    # Multi-field mode (will be unpacked later)
                    data_dict['data'] = raw_value
                else:
                    # Single data field mode
                    field_value = self._check_field_value('data', raw_value)
                    data_dict['data'] = field_value
            else:
                self.log.warning("Data signal has X/Z value")
                data_dict['data'] = -1  # Indicate X/Z value

        return data_dict
    async def _recv_phase1(self, current_time, last_packet, last_xfer):
        """
        Receive phase 1: Handle pending transactions from previous cycle

        Returns:
            current_time: Updated simulation time
        """
        # Wait a brief moment for signal stability
        await Timer(200, units='ps')

        # Check if last transfer is pending (fifo_flop mode)
        if last_xfer:
            packet = last_packet

            if self.use_multi_signal:
                # Multi-signal mode: collect data from field signals
                data_dict = self._get_data_dict()
                self._finish_packet(current_time, packet, data_dict)
            else:
                # Standard mode - check if data signal is X/Z
                if self.pkt_sig.value.is_resolvable:
                    data_val = int(self.pkt_sig.value)
                else:
                    self.log.warning("Data signal has X/Z value")
                    data_val = -1  # Represent X/Z as -1

                self._finish_packet(current_time, packet, {'data': data_val})

        return current_time

    async def _recv_phase2(self, current_time, last_packet, last_xfer):
        """
        Receive phase 2: Check for valid handshake and process transaction

        Returns:
            tuple: (last_packet, last_xfer) for next cycle
        """
        # Check for a valid handshake on this cycle
        if (not self.valid_sig.value.is_resolvable or
                not self.ready_sig.value.is_resolvable or
                self.valid_sig.value.integer != 1 or
                self.ready_sig.value.integer != 1):
            return last_packet, last_xfer

        # Create a new packet
        packet = self.packet_class(self.field_config)
        packet.start_time = current_time

        if self.mode == 'fifo_flop':
            # 'fifo_flop' mode: note handshake time, defer data capture to next cycle
            last_xfer = True
            last_packet = packet
        else:
            # Capture data for this transaction
            data_dict = self._get_data_dict()
            self._finish_packet(current_time, packet, data_dict)

        return last_packet, last_xfer

    async def _monitor_recv(self):
        """
        Monitor for GAXI transactions following valid/ready handshakes.
        Handles both standard and multi-signal modes.
        """
        try:
            last_packet = None
            last_xfer = False

            while True:
                await FallingEdge(self.clock)
                current_time = get_sim_time('ns')

                # recv phase 1: Handle pending transactions
                current_time = await self._recv_phase1(current_time, last_packet, last_xfer)

                # Always clear the last transfer here
                last_xfer = False

                # recv phase 2: Check for valid handshake and process transaction
                last_packet, last_xfer = await self._recv_phase2(current_time, last_packet, last_xfer)

        except Exception as e:
            self.log.error(f"GAXIMonitor({self.title}): Exception in _monitor_recv: {str(e)}")
            import traceback
            self.log.error(traceback.format_exc())
            raise
