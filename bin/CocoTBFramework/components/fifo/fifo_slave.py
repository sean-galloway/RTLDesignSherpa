"""FIFO Slave Component with improved memory integration and robust error handling"""
import cocotb
from collections import deque
from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time

from ..flex_randomizer import FlexRandomizer
from ..field_config import FieldConfig
from .fifo_packet import FIFOPacket
from .fifo_memory_integ import FIFOMemoryInteg


# Standard Signal names for all master/slave/monitor objects
fifo_read = 'i_read'
fifo_rd_empty = 'o_rd_empty'
fifo_rd_data = 'o_rd_data'
fifo_rd_data_wire = 'ow_rd_data'  # for fifo_mux mode

fifo_valid_modes = ['fifo_mux', 'fifo_flop']

# Standard signal maps and constraints for FIFO Slave components
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
fifo_slave_default_constraints = {
    'read_delay': ([(0, 1), (2, 8), (9, 30)], [5, 2, 1])
}

# Default memory Fields
fifo_memory_fields = {
    'addr': 'addr',
    'data': 'data',
    'strb': 'strb'
}


class FIFOSlave(BusMonitor):
    """
    Slave driver for FIFO transactions with enhanced memory integration.
    Controls read signal and monitors empty signal.

    Supports:
    1. Single data bus (standard mode)
    2. Individual signals for each field (multi-signal mode)
    3. Optional signals with fallback behavior
    4. Enhanced memory integration with error handling
    5. Transaction dependency tracking
    """
    def __init__(self, dut, title, prefix, clock,
                field_config=None, packet_class=FIFOPacket, timeout_cycles=1000,
                randomizer=None, memory_model=None, memory_fields=None,
                field_mode=False, multi_sig=False, log=None, mode='fifo_mux', signal_map=None, optional_signal_map=None, **kwargs):
        """
        Initialize the FIFO slave.

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
            field_mode: If True, treat standard data bus as containing multiple fields
            multi_sig: Use multiple signals or not
            log: Logger instance
            mode: 'fifo_mux', or 'fifo_flop'
            signal_map: Dictionary mapping required FIFO signals to DUT signals
                Format: {'o_rd_empty': 'dut_empty_signal', 'i_read': 'dut_read_signal', ...}
            optional_signal_map: Dictionary mapping optional FIFO signals to DUT signals
                These signals won't cause errors if missing from the DUT
            **kwargs: Additional arguments to pass to BusMonitor
        """
        # Validate mode parameter
        if mode not in fifo_valid_modes:
            raise ValueError(f"Invalid mode '{mode}' for Slave ({title}). Mode must be one of: {', '.join(fifo_valid_modes)}")

        # Set up simple items
        self.title = title
        self.clock = clock
        self.tick_delay = 100
        self.tick_units = 'ps'
        self.field_mode = field_mode or multi_sig
        self.timeout_cycles = timeout_cycles
        self.use_multi_signal = multi_sig  # Explicitly set this attribute
        self.reset_occurring = False

        # Handle field_config - convert dict to FieldConfig if needed
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        else:
            self.field_config = field_config or FieldConfig.create_data_only()
        self.packet_class = packet_class
        self.mode = mode

        # Determine if we're using multi-signal mode
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
        self.empty_name = fifo_rd_empty
        self.read_name = fifo_read

        # Data signal based on mode
        self.data_name = fifo_rd_data_wire if mode == 'fifo_mux' else fifo_rd_data
        # Get the actual DUT signal names from the map
        self.empty_dut_name = self.signal_map.get(self.empty_name, self.empty_name)
        self.read_dut_name = self.signal_map.get(self.read_name, self.read_name)
        self.data_dut_name = self.optional_signal_map.get(self.data_name, self.data_name)

        # Prepare signal lists for BusMonitor initialization
        msg_multi = None
        if self.use_multi_signal:
            # Multi-signal mode - only include empty/read in _signals
            msg_multi = (f'Slave({title}) multi-signal model\n'
                            f'{signal_map=}\n'
                            f'{optional_signal_map=}\n'
                            f'{field_config=}\n')
            self._signals = [self.empty_dut_name, self.read_dut_name]
        else:
            # Use the mapped signal names for standard mode
            self._signals = [self.empty_dut_name, self.read_dut_name, self.data_dut_name]

        # Set up optional signals
        self._optional_signals = []
        if self.optional_signal_map:
            self._optional_signals.extend(
                dut_name for _, dut_name in self.optional_signal_map.items()
            )

        # Set up randomizer
        if randomizer is None:
            self.randomizer = FlexRandomizer(fifo_slave_default_constraints)
        else:
            self.randomizer = randomizer
        if not isinstance(self.randomizer, FlexRandomizer):
            raise ValueError(f"Slave ({self.title}) self.randomizer is not properly initialized!")

        # Set up memory model integration
        self.memory_model = memory_model
        if memory_model and not memory_fields:
            # Default memory field mapping if not provided
            self.memory_fields = fifo_memory_fields
        else:
            self.memory_fields = memory_fields

        # Initialize parent BusMonitor (without auto-starting monitor)
        BusMonitor.__init__(self, dut, prefix, clock, callback=None, event=None, **kwargs)
        self.log = log or self._log
        self.log.debug(f"FIFOSlave init for '{title}': randomizer={randomizer}, mode={mode}")

        # Create enhanced memory integration if memory model is provided
        if self.memory_model:
            self.memory_integration = FIFOMemoryInteg(
                self.memory_model,
                component_name=f"Slave({self.title})",
                log=self.log,
                memory_fields=self.memory_fields
            )

        # Set up references to empty and read signals
        if hasattr(self.bus, self.empty_dut_name):
            self.empty_sig = getattr(self.bus, self.empty_dut_name)
        else:
            self.log.error(f"Empty signal '{self.empty_dut_name}' not found on bus")
            self.empty_sig = None

        if hasattr(self.bus, self.read_dut_name):
            self.read_sig = getattr(self.bus, self.read_dut_name)
        else:
            self.log.error(f"Read signal '{self.read_dut_name}' not found on bus")
            self.read_sig = None

        # Set up reference to data signal (for standard mode)
        if hasattr(self.bus, self.data_dut_name):
            self.data_sig = getattr(self.bus, self.data_dut_name)
        else:
            self.data_sig = None

        # Create a mapping of field names to DUT signals for multi-signal mode
        self.field_signals = {}

        # In multi-signal mode, verify signals and store mappings
        if self.use_multi_signal:
            self._initialize_multi_signal_mode()

        # Initialize output signals
        if self.read_sig:
            self.read_sig.setimmediatevalue(0)

        # Create received queue
        self.received_queue = deque()

        # Initialize callbacks list
        self.callbacks = []

        # Statistics - use a dictionary instead of class to avoid attribute errors
        self.stats = {
            'transactions_received': 0,
            'empty_cycles': 0,
            'read_while_empty': 0,
            'received_transactions': 0  # Add this explicitly to avoid AttributeError
        }

        # Debug output
        self.log.info(f"FIFOSlave initialized for {self.title} in mode '{self.mode}', {'multi-signal' if self.use_multi_signal else 'standard'}")

    def _initialize_multi_signal_mode(self):
        """Initialize and verify signals in multi-signal mode."""
        # Check field signal mappings
        for field_name in self.field_config.field_names():
            field_signal_name = f'o_rd_pkt_{field_name}'

            # Check required signal map first
            if field_signal_name in self.signal_map:
                dut_signal_name = self.signal_map[field_signal_name]
                self._register_field_signal(field_name, dut_signal_name, required=True)

            # Then check optional signal map
            elif field_signal_name in self.optional_signal_map:
                dut_signal_name = self.optional_signal_map[field_signal_name]
                self._register_field_signal(field_name, dut_signal_name, required=False)

            else:
                self.log.warning(f"FIFOSlave({self.title}): No signal mapping provided for field {field_name}")

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
                    f"FIFOSlave({self.title}) at {current_time}ns: Field '{field_name}' value 0x{field_value:X} "
                    f"exceeds maximum 0x{max_value:X} ({bits} bits). Value will be masked."
                )

                return field_value & max_value
        except Exception as e:
            self.log.error(f"Error checking field value: {e}")

        return field_value

    def set_randomizer(self, randomizer):
        """
        Swap the current randomizer with a new one.

        Args:
            randomizer: New FlexRandomizer instance
        """
        self.randomizer = randomizer
        self.log.info(f"Slave({self.title}) Set new randomizer for {self.title}")

    def get_randomizer(self):
        """
        Get the current randomizer.

        Returns:
            Current FlexRandomizer instance
        """
        return self.randomizer

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
            self.memory_fields = fifo_memory_fields

        # Update or create memory integration
        if self.memory_model:
            self.memory_integration = FIFOMemoryInteg(
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
        self.reset_occurring = True
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        self.reset_occurring = False

        # Deassert read signal
        if fifo_read in self.signal_map:
            read_signal = self.signal_map[fifo_read]
            if hasattr(self.bus, read_signal):
                getattr(self.bus, read_signal).value = 0
        else:
            self.read_sig.value = 0

        # Clear any queued transactions
        self.received_queue = deque()

    def _finish_packet(self, current_time, packet, data_dict=None):
        """
        Finish packet processing and trigger callbacks.
        Also integrates with memory model if available.
        """
        # Check if we need to unpack fields from a combined value
        if not self.use_multi_signal:
            if (
                self.field_mode
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

        # Update stats
        self.stats['transactions_received'] += 1
        self.stats['received_transactions'] += 1  # Add this to match expected behavior

        # Log packet
        packet_str = packet.formatted(compact=True) if hasattr(packet, 'formatted') else str(packet)
        self.log.debug(f"Slave({self.title}) Transaction received at {packet.end_time}ns: {packet_str}")

        # Call all registered callbacks with the packet
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
                self.log.debug(f"Slave({self.title}) Ignoring AttributeError from parent _recv method")

        # Call additional callbacks
        for callback in self.callbacks:
            try:
                callback(packet)
            except Exception as e:
                self.log.error(f"Error in callback: {e}")

    def add_callback(self, callback):
        """
        Add a callback function to be called when a packet is received.

        Args:
            callback: Function to call with received packet

        Returns:
            Self for method chaining
        """
        if callback not in self.callbacks:
            self.callbacks.append(callback)
        return self

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
        elif self.data_sig:
            # Standard mode
            if self.data_sig.value.is_resolvable:
                raw_value = int(self.data_sig.value)
                if hasattr(self, 'field_mode') and self.field_mode:
                    # Multi-field mode - will be unpacked later
                    data_dict['data'] = raw_value
                else:
                    # Single data field mode
                    field_value = self._check_field_value('data', raw_value)
                    data_dict['data'] = field_value
            else:
                self.log.warning("Data signal has X/Z value")
                data_dict['data'] = -1  # Indicate X/Z value

        return data_dict

    def _set_rd_ready(self, value):
        # Assert/Deassert read
        if fifo_read in self.signal_map:
            read_signal = self.signal_map[fifo_read]
            if hasattr(self.bus, read_signal):
                getattr(self.bus, read_signal).value = value
        else:
            self.read_sig.value = value

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
                # Standard mode - check if data signal is X/Z
                if self.data_sig.value.is_resolvable:
                    data_val = int(self.data_sig.value)
                    self._finish_packet(current_time, packet, {'data': data_val})
                else:
                    self.log.warning("Data signal has X/Z value")
                    self._finish_packet(current_time, packet, {'data': -1})  # Use -1 to indicate X/Z

        return current_time

    async def _recv_phase2(self):
        """Receive phase 2: Handle read delays and assert read if not empty"""
        # Check if FIFO is empty
        if self.empty_sig.value:
            # FIFO is empty, keep read deasserted and update stats
            self._set_rd_ready(0)
            self.stats['empty_cycles'] += 1
            return

        # Check if valid on this cycle, if so we can't drop read
        if not (not self.empty_sig.value.is_resolvable or
                not self.read_sig.value.is_resolvable or
                self.empty_sig.value.integer != 0 or
                self.read_sig.value.integer != 1):
            # Previous read in progress, no delay
            return

        # Determine read delay for this cycle
        delay_cfg = self.randomizer.next()
        read_delay = delay_cfg.get('read_delay', 0)
        if read_delay > 0:
            # Deassert read during delay
            self._set_rd_ready(0)
            await self.wait_cycles(read_delay)

        # FIFO is not empty, assert read
        self._set_rd_ready(1)

        # Wait for a falling edge to sample signals
        await FallingEdge(self.clock)

    async def _recv_phase3(self, current_time):
        """Receive phase 3: Check for valid read and process transaction"""
        # Check if reading and FIFO is not empty (valid read)
        if (self.read_sig.value.is_resolvable and
                self.empty_sig.value.is_resolvable and
                self.read_sig.value.integer == 1 and
                self.empty_sig.value.integer == 0):

            # Create a new packet
            packet = self.packet_class(self.field_config)
            packet.start_time = current_time

            if self.mode == 'fifo_flop':
                # 'fifo_flop' mode: note read time, defer data capture to next cycle
                last_xfer = True
                last_packet = packet
                await RisingEdge(self.clock)
                await Timer(self.tick_delay, units=self.tick_units)
                return last_packet, last_xfer
            else:
                # In fifo_mux mode, capture data in the same cycle
                data_dict = self._get_data_dict()
                self._finish_packet(current_time, packet, data_dict)
        elif (self.read_sig.value.is_resolvable and
                self.empty_sig.value.is_resolvable and
                self.read_sig.value.integer == 1 and
                self.empty_sig.value.integer == 1):
            # Attempting to read while empty
            self.stats['read_while_empty'] += 1
            self.log.warning(f"FIFOSlave({self.title}) Read while empty detected at {current_time}ns")

        # Deassert read on the rising edge (prepare for next cycle or delay)
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

                # recv phase 2: Handle read delays and assert read if not empty
                await self._recv_phase2()

                # recv phase 3: Check for valid read and process transaction
                last_packet, last_xfer = await self._recv_phase3(current_time)

        except Exception as e:
            self.log.error(f"FIFOSlave({self.title}) Exception in _monitor_recv: {e}")
            import traceback
            self.log.error(traceback.format_exc())
            raise

    async def wait_cycles(self, cycles):
        """Wait for a number of clock cycles."""
        for _ in range(cycles):
            await RisingEdge(self.clock)
            if self.reset_occurring:
                break

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

    def get_stats(self):
        """
        Get transaction statistics.

        Returns:
            Dictionary with transaction statistics
        """
        return self.stats.copy()

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

        # Update stats
        self.stats['transactions_received'] += 1
        self.stats['received_transactions'] += 1

        # Call callbacks
        self._call_callbacks(packet)

        # Return processed packet
        return packet
