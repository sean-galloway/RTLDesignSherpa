"""GAXI Master Component with improved memory integration"""
import pprint

import cocotb
from collections import deque
from cocotb_bus.drivers import BusDriver
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from ..flex_randomizer import FlexRandomizer
from ..field_config import FieldConfig
from ..debug_object import print_object_details, print_dict_to_log
from .gaxi_packet import GAXIPacket
from .gaxi_memory_integ import EnhancedMemoryIntegration


# Standard Signal names for all master/sllave/monitor objects
gaxi_valid = 'm2s_valid'
gaxi_ready = 's2m_ready'
gaxi_pkt = 'm2s_pkt'
gaxi_ctrl_signals = [gaxi_valid, gaxi_ready]
gaxi_signals = [gaxi_valid, gaxi_ready, gaxi_pkt]
gaxi_valid_modes = ['skid', 'fifo_mux', 'fifo_flop']

# Standard signal maps and constraints for GAXI Master components
master_signal_map = {
            'm2s_valid': 'i_wr_valid',
            's2m_ready': 'o_wr_ready'
}
master_optional_signal_map = {
            'm2s_pkt': 'i_wr_data'
}
gaxi_master_default_constraints = {
    'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 2, 1])
}

# Basic, defauult field  config
gaxi_basic_field_config = {'data': {'bits': 32, 'default': 0, 'format': 'hex', 'display_width': 8}}

# Default memory Fields
gaxi_memory_fields = {
                'addr': 'addr',
                'data': 'data',
                'strb': 'strb'
}


class GAXIMaster(BusDriver):
    """
    Master driver for GAXI transactions with enhanced memory integration.
    Controls valid signal and waits for ready.
    """
    def __init__(self, dut, title, prefix, clock,
                    field_config=None, packet_class=GAXIPacket, timeout_cycles=1000,
                    randomizer=None, memory_model=None, memory_fields=None, log=None,
                    field_mode=False, multi_sig=False, signal_map=None, optional_signal_map=None, **kwargs):
        """
        Initialize the GAXI master.

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
            signal_map: Dictionary mapping GAXI signals to DUT signals
                Format: {'m2s_valid': 'dut_valid_signal', 's2m_ready': 'dut_ready_signal', ...}
            optional_signal_map: Dictionary mapping optional GAXI signals to DUT signals
                These signals won't cause errors if missing from the DUT
            **kwargs: Additional arguments to pass to BusDriver
        """
        # Set up simple items
        self.title = title
        self.clock = clock
        self.tick_delay = 100
        self.tick_units = 'ps'
        self.timeout_cycles = timeout_cycles
        self.field_mode = field_mode or multi_sig
        self.reset_occurring = False

        # Handle field_config - convert dict to FieldConfig if needed
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        else:
            self.field_config = field_config or FieldConfig.create_data_only()
        self.packet_class = packet_class or GAXIPacket

        # Determine if we're using multi-signal mode (individual signals for each field)
        self.use_multi_signal = multi_sig
        self.signal_map = signal_map or master_signal_map
        self.optional_signal_map = optional_signal_map or master_optional_signal_map

        # Store standard signal names for easier reference
        self.valid_name = 'm2s_valid'
        self.ready_name = 's2m_ready'
        self.pkt_name = 'm2s_pkt'

        # Get the actual DUT signal names from the map
        self.valid_dut_name = self.signal_map.get(self.valid_name, self.valid_name)
        self.ready_dut_name = self.signal_map.get(self.ready_name, self.ready_name)
        self.pkt_dut_name = self.optional_signal_map.get(self.pkt_name, self.pkt_name)

        msg_multi = None
        # Use standard signals if in standard mode and no signals provided
        if not self.use_multi_signal:
            # Use the mapping to translate standardized names to DUT signal names
            self._signals = [self.valid_dut_name, self.ready_dut_name, self.pkt_dut_name]
        else:
            # In multi-signal mode, we need at least valid/ready in the base _signals
            msg_multi = (f'Master({title}) multi-signal model\n'
                            f'{signal_map=}\n'
                            f'{optional_signal_map=}\n'
                            f'{field_config=}\n')

            self._signals = [self.valid_dut_name, self.ready_dut_name]

        self._optional_signals = []
        # Add any optional signals to the optional_signals list
        if self.optional_signal_map:
            self._optional_signals.extend(
                dut_name for _, dut_name in self.optional_signal_map.items()
            )

        # Set up randomizer
        if randomizer is None:
            self.randomizer = FlexRandomizer(gaxi_master_default_constraints)
        else:
            self.randomizer = randomizer

        if not isinstance(self.randomizer, FlexRandomizer):
            raise ValueError(f"Master ({self.title}) self.randomizer is not properly initialized!")

        # Set up enhanced memory model integration
        self.memory_model = memory_model
        self.memory_fields = memory_fields or gaxi_memory_fields
        
        # Initialize parent class
        BusDriver.__init__(self, dut, prefix, clock, **kwargs)
        self.log = log or self._log
        
        # Create enhanced memory integration if memory model is provided
        if self.memory_model:
            self.memory_integration = EnhancedMemoryIntegration(
                self.memory_model,
                component_name=f"Master({self.title})",
                log=self.log,
                memory_fields=self.memory_fields
            )

        # Initialize queues
        self.transmit_queue = deque()
        self.sent_queue = deque()
        self.transmit_coroutine = None
        self.transfer_busy = False
        self.packet_generator = None

        # Create a mapping of field names to DUT signals for multi-signal mode
        self.field_signals = {}

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
        if not self.use_multi_signal and hasattr(self.bus, self.pkt_dut_name):
            self.pkt_sig = getattr(self.bus, self.pkt_dut_name)
        else:
            self.pkt_sig = None

        # In multi-signal mode, verify signals and store mappings
        if self.use_multi_signal:
            self.log.debug(msg_multi)
            self._initialize_multi_signal_mode()
        else:
            # Standard mode - initialize the single data bus
            if self.valid_sig:
                self.valid_sig.setimmediatevalue(0)
            if self.pkt_sig:
                self.pkt_sig.setimmediatevalue(0)

        # Debug output
        self.log.info(f"GAXIMaster initialized for {title} in {'multi-signal' if self.use_multi_signal else 'standard'} mode")

    def _initialize_multi_signal_mode(self):
        """Initialize signals in multi-signal mode with fallback to defaults for optional signals."""
        # Initialize valid signal - this is always required
        if 'm2s_valid' in self.signal_map:
            valid_signal = self.signal_map['m2s_valid']
            if hasattr(self.bus, valid_signal):
                getattr(self.bus, valid_signal).setimmediatevalue(0)
            else:
                raise ValueError(f"Required signal '{valid_signal}' not found on DUT")
        else:
            self.valid_sig.setimmediatevalue(0)

        # Process each field in the field config
        for field_name in self.field_config.field_names():
            # Create the signal name for this field in the signal map
            field_signal_name = f'm2s_pkt_{field_name}'

            # Check required signal map first
            if field_signal_name in self.signal_map:
                dut_signal_name = self.signal_map[field_signal_name]
                self._register_field_signal(field_name, dut_signal_name, required=True)

            # Then check optional signal map
            elif field_signal_name in self.optional_signal_map:
                dut_signal_name = self.optional_signal_map[field_signal_name]
                self._register_field_signal(field_name, dut_signal_name, required=False)

            # If no mapping exists and we have a 'data' field, use standard data signal
            elif field_name == 'data' and hasattr(self.bus, 'm2s_pkt'):
                self.field_signals[field_name] = 'm2s_pkt'
                self.pkt_sig.setimmediatevalue(0)

            # No mapping and no standard data signal
            else:
                self.log.warning(f"GAXIMaster({self.title}): No signal mapping provided for field {field_name}")

    def _register_field_signal(self, field_name, dut_signal_name, required=True):
        """Register a field signal with appropriate error handling"""
        # Verify signal exists on DUT
        if hasattr(self.bus, dut_signal_name):
            # Store the mapping
            self.field_signals[field_name] = dut_signal_name

            # Initialize with default value from field config
            # Access default value directly from FieldDefinition object
            if hasattr(self.field_config, 'get_field'):
                field_def = self.field_config.get_field(field_name)
                default_value = field_def.default
            else:
                # Fallback for dictionary-based field config
                default_value = self.field_config[field_name].get('default', 0)
                
            getattr(self.bus, dut_signal_name).setimmediatevalue(default_value)
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
        self.log.info(f"Set new randomizer for Master({self.title})")

    def get_randomizer(self):
        """
        Get the current randomizer with a new one.

        Args:
            randomizer: New FlexRandomizer instance
        """
        return self.randomizer

    def set_packet_generator(self, generator_func):
        """
        Set a function that generates packets on demand.

        Args:
            generator_func: Function that returns a new packet when called
        """
        self.packet_generator = generator_func

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
                component_name=f"Master({self.title})",
                log=self.log,
                memory_fields=self.memory_fields
            )

    async def reset_bus(self):
        """
        Reset the bus to initial state.
        """
        self.log.debug(f"Master({self.title}): resetting the bus")

        # Reset valid signal
        self._assign_valid_value(value=0)
        self.reset_occurring = True
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        self.reset_occurring = False

        # Reset field signals
        self._clear_data_bus()

        # Clear queues
        self.transmit_queue = deque()
        self.sent_queue = deque()
        self.transmit_coroutine = None
        self.transfer_busy = False

    async def send_packets(self, count=1):
        """
        Send multiple packets using the configured generator.

        Args:
            count: Number of packets to send

        Returns:
            List of sent packets
        """
        if not self.packet_generator:
            raise ValueError("Master({self.title}): Packet generator not set. Use set_packet_generator first.")

        sent_packets = []
        for _ in range(count):
            packet = self.packet_generator()
            await self.send(packet)
            sent_packets.append(packet)

        return sent_packets

    async def busy_send(self, transaction):
        """
        Send a transaction and wait for completion.

        Args:
            transaction: The transaction to send
        """
        await self.send(transaction)
        while self.transfer_busy:
            await RisingEdge(self.clock)
        await Timer(self.tick_delay, units=self.tick_units)

    async def _driver_send(self, transaction, sync=True, hold=False, **kwargs):
        """
        Send a transaction on the bus.

        Args:
            transaction: The transaction to send
            sync: Whether to synchronize with the clock
            hold: Whether to hold off starting a new transmit pipeline
            **kwargs: Additional arguments
        """
        # If using memory model, write to memory using enhanced integration
        if self.memory_model and 'write' in kwargs and kwargs['write']:
            success, error_msg = self.memory_integration.write(transaction)
            if not success:
                self.log.error(f"Master({self.title}): {error_msg}")

        # Add transaction to queue
        self.transmit_queue.append(transaction)

        # Start transmission pipeline if not already running
        if not hold and not self.transmit_coroutine:
            self.log.debug(f'Master({self.title}): Starting new transmit pipeline, queue length: {len(self.transmit_queue)}')
            self.transmit_coroutine = cocotb.start_soon(self._transmit_pipeline())

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
                    f"GAXIMaster({self.title}) at {current_time}ns: Field '{field_name}' value 0x{field_value:X} "
                    f"exceeds maximum 0x{max_value:X} ({bits} bits). Value will be masked."
                )

                return field_value & max_value
        except Exception as e:
            self.log.error(f"Error checking field value: {e}")

        return field_value

    def _drive_signals(self, transaction):
        """
        Drive transaction data onto the bus signals.

        Args:
            transaction: The transaction to drive

        Returns:
            True if successful, False if any signals couldn't be driven
        """
        try:
            # Get FIFO-adjusted values for all fields using the Packet method
            fifo_data = transaction.pack_for_fifo()

            if self.use_multi_signal:
                # Multi-signal mode: drive individual field signals
                for field_name, field_value in fifo_data.items():
                    # Check if value exceeds field capacity and mask if needed
                    field_value = self._check_field_value(field_name, field_value)

                    # For each field, look up the corresponding signal name
                    signal_name = f'm2s_pkt_{field_name}'

                    if signal_name in self.optional_signal_map:
                        dut_signal_name = self.optional_signal_map[signal_name]
                        if hasattr(self.bus, dut_signal_name):
                            getattr(self.bus, dut_signal_name).value = field_value
                    elif field_name in self.field_signals:
                        # Use already registered field signals
                        dut_signal_name = self.field_signals[field_name]
                        if hasattr(self.bus, dut_signal_name):
                            getattr(self.bus, dut_signal_name).value = field_value
            elif self.pkt_sig:
                # Standard mode
                if hasattr(self, 'field_mode') and self.field_mode:
                    self._drive_signals_helper(fifo_data)
                elif 'data' in fifo_data:
                    field_value = self._check_field_value('data', fifo_data['data'])
                    self.pkt_sig.value = field_value
                elif fifo_data:
                    first_field = next(iter(fifo_data))
                    field_value = self._check_field_value(first_field, fifo_data[first_field])
                    self.pkt_sig.value = field_value
            return True
        except Exception as e:
            self.log.error(f"Error driving signals: {e}")
            return False

    def _drive_signals_helper(self, fifo_data):
        # Multiple fields packed into single signal
        combined_value = 0
        bit_offset = 0
        for field_name in self.field_config.field_names():
            if field_name in fifo_data:
                field_def = self.field_config.get_field(field_name)
                field_width = field_def.bits
                field_value = self._check_field_value(field_name, fifo_data[field_name])
                combined_value |= (field_value << bit_offset)
                bit_offset += field_width
        self.pkt_sig.value = combined_value

    def _assign_valid_value(self, value):
        # Assert/Deassert valid
        if 'm2s_valid' in self.signal_map:
            valid_signal = self.signal_map['m2s_valid']
            if hasattr(self.bus, valid_signal):
                getattr(self.bus, valid_signal).value = value
        else:
            self.valid_sig.value = value

    def _clear_data_bus(self):
        # Clear data signals during delay
        if self.use_multi_signal:
            # Reset individual field signals
            for _, dut_signal_name in self.field_signals.items():
                if hasattr(self.bus, dut_signal_name):
                    getattr(self.bus, dut_signal_name).value = 0
        else:
            # Standard mode - reset aggregate data signal
            self.pkt_sig.value = 0

    async def _xmit_phase1(self):
        """First phase of transmission - delay and prepare signals"""
        # Apply any configured delay before asserting valid
        delay_dict = self.randomizer.next()
        valid_delay = delay_dict.get('valid_delay', 0)
        if valid_delay > 0:
            # Deassert wr_valid
            self._assign_valid_value(value=0)

            # Clear the data bus
            self._clear_data_bus()

            # valid delay
            await self.wait_cycles(valid_delay)

    async def _xmit_phase2(self, transaction):
        """Second phase - drive signals and wait for handshake"""
        # Drive signals for this transaction
        if not self._drive_signals(transaction):
            self.log.error(f"Failed to drive signals for transaction: {transaction.formatted()}")
            self.transfer_busy = False
            return False

        # Assert valid for this transaction
        self._assign_valid_value(value=1)
        # wait a bit to keep from catching the last ready assertion
        await Timer(100, units='ps')

        # Wait for the DUT to assert ready (handshake completion)
        timeout_counter = 0
        ready_signal = self.signal_map.get('s2m_ready', 's2m_ready')

        while not getattr(self.bus, ready_signal).value:
            await RisingEdge(self.clock)
            await Timer(self.tick_delay, units=self.tick_units)
            timeout_counter += 1
            if timeout_counter >= self.timeout_cycles:
                self.log.error(f"Master({self.title}) TIMEOUT waiting for ready after {self.timeout_cycles} cycles")

                # Stop driving if timeout (prevent hang)
                self._assign_valid_value(value=0)

                # Clear the data bus
                self._clear_data_bus()

                self.transfer_busy = False
                return False

        return True

    async def _xmit_phase3(self, transaction):
        """Third phase - capture handshake and prepare for next transaction"""
        # Handshake occurred – capture completion time
        await RisingEdge(self.clock)
        await Timer(self.tick_delay, units=self.tick_units)
        current_time_ns = get_sim_time('ns')
        self.log.debug(f"Master({self.title}) Transaction completed at {current_time_ns}ns: "
                        f"{transaction.formatted(compact=True)}")
        transaction.end_time = current_time_ns
        self.sent_queue.append(transaction)
        # clear wr valid
        self._assign_valid_value(value=0)
        # Clear the data bus
        self._clear_data_bus()

    async def _transmit_pipeline(self):
        """
        Pipeline for transmitting transactions with support for multi-signal mode.
        """
        self.log.debug(f'Master({self.title}): Transmit pipeline started, queue length: {len(self.transmit_queue)}')
        self.transfer_busy = True
        await RisingEdge(self.clock)
        await Timer(self.tick_delay, units=self.tick_units)

        while len(self.transmit_queue):
            # Get next transaction from the queue
            transaction = self.transmit_queue.popleft()
            transaction.start_time = get_sim_time('ns')

            # xmit phase 1 - apply delay
            await self._xmit_phase1()

            # xmit phase 2 - drive signals and wait for handshake
            if not await self._xmit_phase2(transaction):
                # Error occurred in phase 2
                continue

            # xmit phase 3 - handle handshake completion
            await self._xmit_phase3(transaction)

        self.log.debug(f"Master({self.title}) Transmit pipeline completed")
        self.transfer_busy = False
        self.transmit_coroutine = None

        # Ensure signals are deasserted at the end
        if 'm2s_valid' in self.signal_map:
            valid_signal = self.signal_map['m2s_valid']
            if hasattr(self.bus, valid_signal):
                getattr(self.bus, valid_signal).value = 0
        else:
            self.valid_sig.value = 0

        # Clear data signals
        if self.use_multi_signal:
            # Reset field signals
            for _, dut_signal_name in self.field_signals.items():
                if hasattr(self.bus, dut_signal_name):
                    getattr(self.bus, dut_signal_name).value = 0
        else:
            # Standard mode - reset aggregate data signal
            self.pkt_sig.value = 0

    async def wait_cycles(self, cycles):
        """
        Wait for a specified number of clock cycles.

        Args:
            cycles: Number of cycles to wait
        """
        self.log.debug(f"Master({self.title}) waiting cycles {cycles}")
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
