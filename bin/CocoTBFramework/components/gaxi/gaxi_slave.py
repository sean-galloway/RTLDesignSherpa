"""GAXI Slave Component with improved memory integration"""
import cocotb
from collections import deque
from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time

from ..flex_randomizer import FlexRandomizer
from .gaxi_packet import GAXIPacket
from ..field_config import FieldConfig, FieldDefinition
from ..debug_object import print_object_details, print_dict_to_log
from .gaxi_memory_integ import EnhancedMemoryIntegration


# Standard Signal names for all master/sllave/monitor objects
gaxi_valid = 'm2s_valid'
gaxi_ready = 's2m_ready'
gaxi_pkt = 'm2s_pkt'
gaxi_valid_modes = ['skid', 'fifo_mux', 'fifo_flop']

# Standard signal maps and constraints for GAXI Slave components
gaxi_slave_signals = ['m2s_valid', 's2m_ready', 'm2s_pkt']
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
gaxi_slave_default_constraints = {
    'ready_delay': ([[0, 1], [2, 8], [9, 30]], [5, 2, 1])
}

# Basic, default field config
gaxi_basic_field_config = {'data': {'bits': 32, 'default': 0, 'format': 'hex', 'display_width': 8}}

# Default memory Fields
gaxi_memory_fields = {
                'addr': 'addr',
                'data': 'data',
                'strb': 'strb'
}


class GAXISlave(BusMonitor):
    """
    Slave driver for GAXI transactions with enhanced memory integration.
    Controls ready signal and monitors valid signals.
    Supports:
    1. Single data bus (standard mode)
    2. Individual signals for each field (multi-signal mode)
    3. Optional signals with fallback behavior
    """
    def __init__(self, dut, title, prefix, clock,
                field_config=None, packet_class=GAXIPacket, timeout_cycles=1000,
                randomizer=None, memory_model=None, memory_fields=None,
                field_mode=False, multi_sig=False, log=None, mode='skid', signal_map=None, optional_signal_map=None, **kwargs):
        # sourcery skip: low-code-quality
        """
        Initialize the GAXI slave.

        Args:
            dut: Device under test
            title: title of the bus
            prefix: prefix used in the bus code
            clock: The clock signal
            field_config: Field configuration for packets
            packet_class: Class to use for creating packets
            timeout_cycles: Maximum cycles to wait before timeout
            randomizer: FlexRandomizer instance for randomizing timing
            memory_model: Optional MemoryModel instance for reading/writing data
            memory_fields: Dictionary mapping memory fields to packet field names
            log: Logger instance
            multi_sig: Use multiple signals or not
            signal_map: Dictionary mapping required GAXI signals to DUT signals
                Format: {'m2s_valid': 'dut_valid_signal', 's2m_ready': 'dut_ready_signal', ...}
            optional_signal_map: Dictionary mapping optional GAXI signals to DUT signals
                These signals won't cause errors if missing from the DUT
            **kwargs: Additional arguments to pass to BusMonitor
        """
        # Validate mode parameter
        if mode not in gaxi_valid_modes:
            raise ValueError(f"Invalid mode '{mode}' for Slave ({title}). Mode must be one of: {', '.join(gaxi_valid_modes)}")

        # Set up simple items
        self.title = title
        self.clock = clock
        self.tick_delay = 100
        self.tick_units = 'ps'
        self.timeout_cycles = timeout_cycles
        self.field_mode = field_mode or multi_sig

        # Handle field_config - convert dict to FieldConfig if needed
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        else:
            self.field_config = field_config or FieldConfig.create_data_only()
        self.packet_class = packet_class
        self.mode = mode

        # Determine if we're using multi-signal mode
        self.use_multi_signal = multi_sig
        self.signal_map = signal_map or slave_signal_map
        if optional_signal_map is not None:
            self.optional_signal_map = optional_signal_map
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
        if self.use_multi_signal:
            # Multi-signal mode - only include valid/ready in _signals
            msg_multi = (f'Slave({title}) multi-signal model\n'
                            f'{signal_map=}\n'
                            f'{optional_signal_map=}\n'
                            f'{field_config=}\n')

            # Use the mapped signal names for required signals
            self._signals = [self.valid_dut_name, self.ready_dut_name]
        else:
            # Use the mapped signal names for standard mode
            self._signals = [self.valid_dut_name, self.ready_dut_name, self.pkt_dut_name]

        # Set up optional signals
        self._optional_signals = []
        if self.optional_signal_map:
            self._optional_signals.extend(
                dut_name for _, dut_name in self.optional_signal_map.items()
            )

        # Set up randomizer
        if randomizer is None:
            self.randomizer = FlexRandomizer(gaxi_slave_default_constraints)
        else:
            self.randomizer = randomizer
        if not isinstance(self.randomizer, FlexRandomizer):
            raise ValueError(f"Slave ({self.title}) self.randomizer is not properly initialized!")

        # Set up memory model integration
        self.memory_model = memory_model
        self.memory_fields = memory_fields or gaxi_memory_fields
        
        # Initialize parent BusMonitor (without auto-starting monitor)
        BusMonitor.__init__(self, dut, prefix, clock, callback=None, event=None, **kwargs)
        self.log = log or self._log
        self.log.debug(f"GAXISlave init for '{title}': randomizer={randomizer}, mode={mode}")
        
        # Create enhanced memory integration if memory model is provided
        if self.memory_model:
            self.memory_integration = EnhancedMemoryIntegration(
                self.memory_model,
                component_name=f"Slave({self.title})",
                log=self.log,
                memory_fields=self.memory_fields
            )

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

        # Create a mapping of field names to DUT signals for multi-signal mode
        self.field_signals = {}

        # In multi-signal mode, verify signals and store mappings
        if self.use_multi_signal:
            self._initialize_multi_signal_mode()

        # Initialize output signals
        if self.ready_sig:
            self.ready_sig.setimmediatevalue(0)

        # Create received queue
        self.received_queue = deque()

        # Debug output
        if log:
            self.log.info(f"GAXISlave initialized for {self.title} in mode '{self.mode}', {'multi-signal' if self.use_multi_signal else 'standard'}")

    def _initialize_multi_signal_mode(self):
        """Initialize and verify signals in multi-signal mode."""
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
                self.log.warning(f"GAXISlave({self.title}): No signal mapping provided for field {field_name}")

    def _register_field_signal(self, field_name, dut_signal_name, required=True):
        """Register a field signal with appropriate error handling"""
        # Verify signal exists on DUT
        if hasattr(self.bus, dut_signal_name):
            # Store the mapping
            self.field_signals[field_name] = dut_signal_name
        elif required:
            # Signal is required but not found
            raise ValueError(f"Required signal '{dut_signal_name}' for field '{field_name}' not found on DUT")
        else:
            # Optional signal not found - log warning
            self.log.warning(f"Optional signal '{dut_signal_name}' for field '{field_name}' not found on DUT")

    def set_randomizer(self, randomizer):
        """
        Swap the current randomizer with a new one.

        Args:
            randomizer: New FlexRandomizer instance
        """
        self.randomizer = randomizer
        self.log.info(f"Slave({self.title}) Set new randomizer for {self.title}")

    def set_memory_model(self, memory_model, memory_fields=None):
        """
        Set or update the memory model.

        Args:
            memory_model: MemoryModel instance for reading/writing data
            memory_fields: Dictionary mapping memory fields to packet field names
        """
        self.memory_model = memory_model
        if memory_fields:
            self.memory_fields = memory_fields
        elif not self.memory_fields:
            # Set default mapping if not already set
            self.memory_fields = gaxi_memory_fields
            
        # Update or create memory integration
        if self.memory_model:
            self.memory_integration = EnhancedMemoryIntegration(
                self.memory_model,
                component_name=f"Slave({self.title})",
                log=self.log,
                memory_fields=self.memory_fields
            )

    async def reset_bus(self):
        """
        Reset the bus to initial state.
        """
        self.log.debug(f"Slave({self.title}): resetting the bus")

        # Deassert ready signal
        if 's2m_ready' in self.signal_map:
            ready_signal = self.signal_map['s2m_ready']
            if hasattr(self.bus, ready_signal):
                getattr(self.bus, ready_signal).value = 0
        else:
            self.ready_sig.value = 0

        # Clear any queued transactions
        self.received_queue = deque()

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
                    f"GAXISlave({self.title}) at {current_time}ns: Field '{field_name}' value 0x{field_value:X} "
                    f"exceeds maximum 0x{max_value:X} ({bits} bits). Value will be masked."
                )
                
                # Mask the value
                masked_value = field_value & max_value
                return masked_value
        except Exception as e:
            self.log.error(f"Error checking field value: {e}")
            
        return field_value

    def _finish_packet(self, current_time, packet, data_dict=None):
        """
        Finish packet processing and trigger callbacks.
        Also integrates with memory model if available.
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
                    # Check field value here for legacy packets
                    value = self._check_field_value(field_name, value)
                    if hasattr(packet, field_name):
                        setattr(packet, field_name, value)

        # Apply memory model data using enhanced memory integration
        if hasattr(self, 'memory_integration') and self.memory_model:
            success, data, error_msg = self.memory_integration.read(packet, update_transaction=True)
            if not success:
                self.log.warning(f"Slave({self.title}): {error_msg}")

        # Record completion time and store packet
        packet.end_time = current_time
        self.received_queue.append(packet)
        packet_str = packet.formatted(compact=True) if hasattr(packet, 'formatted') else str(packet)
        self.log.debug(f"Slave({self.title}) Transaction received at {packet.end_time}ns: {packet_str}")
        self._recv(packet)  # trigger callbacks

    # TODO Rename this here and in `_finish_packet`
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
        elif self.pkt_sig:
            # Standard mode
            if self.pkt_sig.value.is_resolvable:
                raw_value = int(self.pkt_sig.value)
                if hasattr(self, 'field_mode') and self.field_mode:
                    # Multi-field mode - store raw value to be unpacked later
                    data_dict['data'] = raw_value
                else:
                    # Single field mode
                    field_value = self._check_field_value('data', raw_value)
                    data_dict['data'] = field_value
            else:
                self.log.warning("Data signal has X/Z value")
                data_dict['data'] = -1  # Indicate X/Z value

        return data_dict

    def _get_data_value(self):
        return int(self.pkt_sig.value)

    def _set_rd_ready(self, value):
        # Assert/Deassert ready
        if 's2m_ready' in self.signal_map:
            ready_signal = self.signal_map['s2m_ready']
            if hasattr(self.bus, ready_signal):
                getattr(self.bus, ready_signal).value = value
        else:
            self.ready_sig.value = value

    async def _recv_phase1(self, last_packet, last_xfer):
        """Receive phase 1: Handle pending transactions from previous cycle"""
        # Wait a brief moment for signal stability
        await Timer(200, units='ps')

        current_time = get_sim_time('ns')

        # Check if last transfer is pending (fifo_flop mode)
        if last_xfer:
            packet = last_packet

            if self.use_multi_signal:
                # Multi-signal mode: collect data from field signals
                data_dict = self._get_data_dict()
                self._finish_packet(current_time, packet, data_dict)
            else:
                # Standard mode
                data_val = self._get_data_value()
                self._finish_packet(current_time, packet, {'data': data_val})

        return current_time

    async def _recv_phase2(self):
        """Receive phase 2: Handle ready delays and assert ready"""
        # Determine ready delay for this cycle
        delay_cfg = self.randomizer.next()
        ready_delay = delay_cfg.get('ready_delay', 0)
        if ready_delay > 0:
            # Deassert ready during delay
            self._set_rd_ready(0)
            await self.wait_cycles(ready_delay)

        # Assert ready to accept data
        self._set_rd_ready(1)

        # Wait for a falling edge to sample valid (allow combinatorial settle)
        await FallingEdge(self.clock)

    async def _recv_phase3(self, current_time):
        """Receive phase 3: Check for valid handshake and process transaction"""
        # Check for a valid handshake on this cycle
        if (self.valid_sig.value.is_resolvable and
                self.ready_sig.value.is_resolvable and
                self.valid_sig.value.integer == 1 and
                self.ready_sig.value.integer == 1):

            # Create a new packet
            packet = self.packet_class(self.field_config)
            packet.start_time = current_time

            if self.mode == 'fifo_flop':
                # 'fifo_flop' mode: note handshake time, defer data capture to next cycle
                last_xfer = True
                last_packet = packet
                await RisingEdge(self.clock)
                await Timer(self.tick_delay, units=self.tick_units)
                return last_packet, last_xfer
            else:
                # Capture data for this transaction
                data_dict = self._get_data_dict()
                self._finish_packet(current_time, packet, data_dict)

        # Deassert ready on the rising edge (prepare for next cycle or delay)
        await RisingEdge(self.clock)
        await Timer(self.tick_delay, units=self.tick_units)
        self._set_rd_ready(0)

        # Default return values
        return None, False

    async def _monitor_recv(self):
        """
        Monitor for incoming transactions (read channel).
        Handles both standard and multi-signal modes.
        """
        try:
            last_packet = None
            last_xfer = False

            while True:
                # recv phase 1: Handle pending transactions
                current_time = await self._recv_phase1(last_packet, last_xfer)

                # Always clear the last transfer here
                last_xfer = False

                # recv phase 2: Handle ready delays and assert ready
                await self._recv_phase2()

                # recv phase 3: Check for valid handshake and process transaction
                last_packet, last_xfer = await self._recv_phase3(current_time)

        except Exception as e:
            self.log.error(f"GAXISlave({self.title}) Exception in _monitor_recv: {e}")
            raise

    async def wait_cycles(self, cycles):
        """Wait for a number of clock cycles."""
        for _ in range(cycles):
            await RisingEdge(self.clock)
        await Timer(self.tick_delay, units=self.tick_units)
        
    def get_memory_stats(self):
        """
        Get memory operation statistics.
        
        Returns:
            Dictionary with memory statistics, or None if no memory model available
        """
        if hasattr(self, 'memory_integration'):
            return self.memory_integration.get_stats()
        return None
        
    async def process_request(self, transaction):
        """
        Process a transaction request, usually from a command handler.
        
        This method provides a standardized way for external components like
        command handlers to send transactions directly to the slave without
        going through the bus signals.
        
        Args:
            transaction: Transaction to process
            
        Returns:
            Response packet or None
        """
        # Create a copy of the transaction to avoid modifying the original
        packet = self.packet_class(self.field_config)
        
        # Copy fields from transaction to packet
        for field_name in self.field_config.field_names():
            if hasattr(transaction, field_name):
                setattr(packet, field_name, getattr(transaction, field_name))
                
        # Set timing information
        current_time = get_sim_time('ns')
        packet.start_time = current_time
        
        # Process with memory model if available
        if hasattr(self, 'memory_integration') and self.memory_model:
            success, data, error_msg = self.memory_integration.read(packet, update_transaction=True)
            if not success:
                self.log.warning(f"Slave({self.title}): {error_msg}")
                
        # Complete packet and add to queue
        packet.end_time = get_sim_time('ns')
        self.received_queue.append(packet)
        
        # Trigger callbacks
        self._recv(packet)
        
        # Return processed packet
        return packet
