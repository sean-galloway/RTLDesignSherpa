"""FIFO Master Component with required and optional signal support"""
import cocotb
from collections import deque
from cocotb_bus.drivers import BusDriver
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from ..flex_randomizer import FlexRandomizer
from .fifo_packet import FIFOPacket
from CocoTBFramework.components.field_config import FieldConfig, FieldDefinition

# Standard Signal names for all master/slave/monitor objects
fifo_write = 'i_write'
fifo_wr_full = 'o_wr_full'
fifo_wr_data = 'i_wr_data'

# Standard signal maps and constraints for FIFO Master components
master_signal_map = {
    'i_write': 'i_write',
    'o_wr_full': 'o_wr_full'
}
master_optional_signal_map = {
    'i_wr_data': 'i_wr_data'
}
fifo_master_default_constraints = {
    'write_delay': ([[0, 0], [1, 8], [9, 20]], [5, 2, 1])
}

# Default memory Fields
fifo_memory_fields = {
    'addr': 'addr',
    'data': 'data',
    'strb': 'strb'
}

class FIFOMaster(BusDriver):
    """
    Master driver for FIFO transactions.
    Controls i_write signal and monitors o_wr_full.
    Can optionally use a memory model for data.

    Supports:
    1. Single data bus (standard mode)
    2. Individual signals for each field (multi-signal mode)
    3. Optional signals with fallback behavior
    """
    def __init__(self, dut, title, prefix, clock,
                field_config=None, packet_class=FIFOPacket, timeout_cycles=1000,
                randomizer=None, memory_model=None, memory_fields=None, log=None,
                multi_sig=False, signal_map=None, optional_signal_map=None, **kwargs):
        """
        Initialize the FIFO master.

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
            signal_map: Dictionary mapping FIFO signals to DUT signals
                Format: {'i_write': 'dut_write_signal', 'o_wr_full': 'dut_full_signal', ...}
            optional_signal_map: Dictionary mapping optional FIFO signals to DUT signals
                These signals won't cause errors if missing from the DUT
            **kwargs: Additional arguments to pass to BusDriver
        """
        # Set up simple items
        self.title = title
        self.clock = clock
        self.timeout_cycles = timeout_cycles
        self.tick_delay = 100
        self.tick_units = 'ps'

        # Handle field_config - convert dict to FieldConfig if needed
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        else:
            self.field_config = field_config or FieldConfig.create_data_only()

        self.packet_class = packet_class

        # Determine if we're using multi-signal mode (individual signals for each field)
        self.use_multi_signal = multi_sig
        self.signal_map = signal_map or master_signal_map
        self.optional_signal_map = optional_signal_map or master_optional_signal_map

        # Store standard signal names for easier reference
        self.write_name = fifo_write
        self.full_name = fifo_wr_full
        self.data_name = fifo_wr_data

        # Get the actual DUT signal names from the map
        self.write_dut_name = self.signal_map.get(self.write_name, self.write_name)
        self.full_dut_name = self.signal_map.get(self.full_name, self.full_name)
        self.data_dut_name = self.optional_signal_map.get(self.data_name, self.data_name)

        msg_multi = None
        # Use standard signals if in standard mode and no signals provided
        if not self.use_multi_signal:
            # Use the mapping to translate standardized names to DUT signal names
            self._signals = [self.write_dut_name, self.full_dut_name, self.data_dut_name]
        else:
            # In multi-signal mode, we need at least write/full in the base _signals
            msg_multi = (f'Master({title}) multi-signal model\n'
                            f'{signal_map=}\n'
                            f'{optional_signal_map=}\n'
                            f'{field_config=}\n')
            self._signals = [self.write_dut_name, self.full_dut_name]

        self._optional_signals = []
        # Add any optional signals to the optional_signals list
        if self.optional_signal_map:
            self._optional_signals.extend(
                dut_name for _, dut_name in self.optional_signal_map.items()
            )

        # Set up randomizer
        if randomizer is None:
            self.randomizer = FlexRandomizer(fifo_master_default_constraints)
        else:
            self.randomizer = randomizer

        if not isinstance(self.randomizer, FlexRandomizer):
            raise ValueError(f"Master ({self.title}) self.randomizer is not properly initialized!")

        # Set up memory model integration
        self.memory_model = memory_model
        if memory_model and not memory_fields:
            # Default memory field mapping if not provided
            self.memory_fields = fifo_memory_fields
        else:
            self.memory_fields = memory_fields

        # Initialize parent class
        BusDriver.__init__(self, dut, prefix, clock, **kwargs)
        self.log = log or self._log
        # if msg_multi is not None:
        #     self.log.debug(msg_multi)

        # Initialize queues
        self.transmit_queue = deque()
        self.sent_queue = deque()
        self.transmit_coroutine = None
        self.transfer_busy = False
        self.packet_generator = None

        # Create a mapping of field names to DUT signals for multi-signal mode
        self.field_signals = {}

        # Set up references to write and full signals
        if hasattr(self.bus, self.write_dut_name):
            self.write_sig = getattr(self.bus, self.write_dut_name)
        else:
            self.log.error(f"Write signal '{self.write_dut_name}' not found on bus")
            self.write_sig = None

        if hasattr(self.bus, self.full_dut_name):
            self.full_sig = getattr(self.bus, self.full_dut_name)
        else:
            self.log.error(f"Full signal '{self.full_dut_name}' not found on bus")
            self.full_sig = None

        # Set up reference to data signal (for standard mode)
        if not self.use_multi_signal and hasattr(self.bus, self.data_dut_name):
            self.data_sig = getattr(self.bus, self.data_dut_name)
        else:
            self.data_sig = None

        # In multi-signal mode, verify signals and store mappings
        if self.use_multi_signal:
            self._initialize_multi_signal_mode()
        else:
            # Standard mode - initialize the single data bus
            if self.write_sig:
                self.write_sig.setimmediatevalue(0)
            if self.data_sig:
                self.data_sig.setimmediatevalue(0)

        # Debug output
        self.log.info(f"FIFOMaster initialized for {title} in {'multi-signal' if self.use_multi_signal else 'standard'} mode")

    def _initialize_multi_signal_mode(self):
        """Initialize signals in multi-signal mode with fallback to defaults for optional signals."""
        # Initialize write signal - this is always required
        if fifo_write in self.signal_map:
            write_signal = self.signal_map[fifo_write]
            if hasattr(self.bus, write_signal):
                getattr(self.bus, write_signal).setimmediatevalue(0)
            else:
                raise ValueError(f"Required signal '{write_signal}' not found on DUT")
        else:
            self.write_sig.setimmediatevalue(0)

        # Process each field in the field config
        # Use field_names() method instead of keys() for FieldConfig objects
        for field_name in self.field_config.field_names():
            # Create the signal name for this field in the signal map
            field_signal_name = f'i_wr_data_{field_name}'

            # Check required signal map first
            if field_signal_name in self.signal_map:
                dut_signal_name = self.signal_map[field_signal_name]
                self._register_field_signal(field_name, dut_signal_name, required=True)

            # Then check optional signal map
            elif field_signal_name in self.optional_signal_map:
                dut_signal_name = self.optional_signal_map[field_signal_name]
                self._register_field_signal(field_name, dut_signal_name, required=False)

            # If no mapping exists and we have a 'data' field, use standard data signal
            elif field_name == 'data' and hasattr(self.bus, fifo_wr_data):
                # self.log.debug(f"Using standard data signal for field '{field_name}'")
                self.field_signals[field_name] = fifo_wr_data
                getattr(self.bus, fifo_wr_data).setimmediatevalue(0)

            # No mapping and no standard data signal
            else:
                self.log.warning(f"FIFOMaster({self.title}): No signal mapping provided for field {field_name}")

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
                    f"FIFOMaster({self.title}) at {current_time}ns: Field '{field_name}' value 0x{field_value:X} "
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
        self.log.info(f"Set new randomizer for Master({self.title})")

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
            self.memory_fields = fifo_memory_fields

    async def reset_bus(self):
        """
        Reset the bus to initial state.
        """
        self.log.debug(f"Master({self.title}): resetting the bus")

        # Reset write signal
        self._assign_write_value(value=0)

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
        # If using memory model, write to memory
        if self.memory_model and 'write' in kwargs and kwargs['write']:
            self._write_to_memory(transaction)

        # Add transaction to queue
        self.transmit_queue.append(transaction)
        # self.log.debug(f'Master({self.title}): Adding to transmit queue: {transaction.formatted(compact=True)}')

        # Start transmission pipeline if not already running
        if not hold and not self.transmit_coroutine:
            self.log.debug(f'Master({self.title}): Starting new transmit pipeline, queue length: {len(self.transmit_queue)}')
            self.transmit_coroutine = cocotb.start_soon(self._transmit_pipeline())

    def _write_to_memory(self, transaction):
        """
        Write transaction data to memory model.

        Args:
            transaction: The transaction to write to memory
        """
        if not self.memory_model or not self.memory_fields:
            return

        try:
            # Get field values
            addr_field = self.memory_fields.get('addr', 'addr')
            data_field = self.memory_fields.get('data', 'data')
            strb_field = self.memory_fields.get('strb', 'strb')

            if hasattr(transaction, addr_field) and hasattr(transaction, data_field):
                self._write_to_memory_helper(
                    transaction, addr_field, data_field, strb_field
                )
        except Exception as e:
            self.log.error(f"Master({self.title}): Error writing to memory: {e}")

    def _write_to_memory_helper(self, transaction, addr_field, data_field, strb_field):
        addr = getattr(transaction, addr_field)
        data = getattr(transaction, data_field)
        strb = getattr(transaction, strb_field) if hasattr(transaction, strb_field) else 0xFF

        # Convert data to bytearray
        data_bytes = self.memory_model.integer_to_bytearray(data, self.memory_model.bytes_per_line)

        # Write to memory
        self.memory_model.write(addr, data_bytes, strb)
        self.log.debug(f"Master({self.title}): Wrote to memory: addr=0x{addr:X}, data=0x{data:X}, strb=0x{strb:X}")

    def _drive_signals(self, transaction):
        """
        Drive transaction data onto the bus signals.

        Args:
            transaction: The transaction to drive

        Returns:
            True if successful, False if any signals couldn't be driven
        """
        try:
            # Get FIFO-adjusted values for all fields using the new Packet method
            fifo_data = transaction.pack_for_fifo()

            if self.use_multi_signal:
                # Multi-signal mode: drive individual field signals
                for field_name, field_value in fifo_data.items():
                    # Check if value exceeds field capacity and mask if needed
                    field_value = self._check_field_value(field_name, field_value)

                    # For each field, look up the corresponding signal name
                    signal_name = f'i_wr_data_{field_name}'

                    if signal_name in self.optional_signal_map:
                        dut_signal_name = self.optional_signal_map[signal_name]
                        if hasattr(self.bus, dut_signal_name):
                            getattr(self.bus, dut_signal_name).value = field_value
                        else:
                            self.log.warning(f"Signal {dut_signal_name} mapped but not found on DUT")
                    elif field_name in self.field_signals:
                        # Use already registered field signals
                        dut_signal_name = self.field_signals[field_name]
                        if hasattr(self.bus, dut_signal_name):
                            getattr(self.bus, dut_signal_name).value = field_value
                        else:
                            self.log.warning(f"Signal {dut_signal_name} registered but not found on DUT")
                    else:
                        self.log.debug(f"FIFOMaster({self.title}): No signal mapping for field {field_name}")
            elif len(fifo_data) == 1 and 'data' in fifo_data:
                # Simple case: only a data field
                field_value = self._check_field_value('data', fifo_data['data'])
                if self.data_sig:
                    self.data_sig.value = field_value
            elif self.data_sig:
                combined_value = 0
                bit_offset = 0

                # Process fields in the order defined in field_config
                field_names = self.field_config.field_names()

                for field_name in field_names:
                    if field_name in fifo_data:
                        # Get field definition from FieldConfig
                        field_def = self.field_config.get_field(field_name)
                        field_width = field_def.bits

                        # Check field value against its max value
                        field_value = self._check_field_value(field_name, fifo_data[field_name])

                        # Shift and combine
                        combined_value |= (field_value << bit_offset)
                        bit_offset += field_width

                self.data_sig.value = combined_value

            return True
        except Exception as e:
            self.log.error(f"Error driving signals: {e}")
            return False

    def _assign_write_value(self, value):
        # Assert/Deassert write
        if fifo_write in self.signal_map:
            write_signal = self.signal_map[fifo_write]
            if hasattr(self.bus, write_signal):
                getattr(self.bus, write_signal).value = value
        else:
            self.write_sig.value = value

    def _clear_data_bus(self):
        # Clear data signals during delay
        if self.use_multi_signal:
            # Reset individual field signals
            for _, dut_signal_name in self.field_signals.items():
                if hasattr(self.bus, dut_signal_name):
                    getattr(self.bus, dut_signal_name).value = 0
        elif self.data_sig:
            self.data_sig.value = 0

    async def _xmit_phase1(self):
        """First phase of transmission - delay and prepare signals"""
        # Apply any configured delay before asserting write
        delay_dict = self.randomizer.next()
        write_delay = delay_dict.get('write_delay', 0)
        if write_delay > 0:
            # self.log.debug(f"Master({self.title}) Delaying write assertion for {write_delay} cycles")

            # Deassert write
            self._assign_write_value(value=0)

            # Clear the data bus
            self._clear_data_bus()

            # write delay
            await self.wait_cycles(write_delay)

    async def _xmit_phase2(self, transaction):
        """Second phase - drive signals and check if FIFO is full"""
        # Drive signals for this transaction
        if not self._drive_signals(transaction):
            self.log.error(f"Failed to drive signals for transaction: {transaction.formatted()}")
            self.transfer_busy = False
            return False

        # Wait for FIFO to not be full
        timeout_counter = 0

        # Check if full signal is high
        while self.full_sig.value:
            await RisingEdge(self.clock)
            await Timer(self.tick_delay, units=self.tick_units)

            # Keep write deasserted while full
            self._assign_write_value(value=0)

            timeout_counter += 1
            if timeout_counter >= self.timeout_cycles:
                self.log.error(f"Master({self.title}) TIMEOUT waiting for FIFO not full after {self.timeout_cycles} cycles")

                # Stop driving if timeout (prevent hang)
                self._assign_write_value(value=0)

                # Clear the data bus
                self._clear_data_bus()

                self.transfer_busy = False
                return False

        # Assert write for this transaction since FIFO is not full
        self._assign_write_value(value=1)

        # Wait a cycle for the write to take effect
        await RisingEdge(self.clock)
        await Timer(self.tick_delay, units=self.tick_units)

        # Check for write while full error
        if self.full_sig.value and self.write_sig.value:
            self.log.error(f"Error: {self.title} write while fifo full")

        return True

    async def _xmit_phase3(self, transaction):
        """Third phase - complete the transfer and prepare for next transaction"""
        # Write has been completed – capture completion time
        current_time_ns = get_sim_time('ns')
        self.log.debug(f"Master({self.title}) Transaction completed at {current_time_ns}ns: "
                        f"{transaction.formatted(compact=True)}")
        transaction.end_time = current_time_ns
        self.sent_queue.append(transaction)

        # Deassert write
        self._assign_write_value(value=0)

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
            # self.log.debug(f"Master({self.title}) Processing transaction, remaining: "
            #                 f"{len(self.transmit_queue)} at {transaction.start_time}ns "
            #                 f"transaction={transaction.formatted(compact=True)}")

            # xmit phase 1 - apply delay
            await self._xmit_phase1()

            # xmit phase 2 - drive signals and check if FIFO is full
            if not await self._xmit_phase2(transaction):
                # Error occurred in phase 2
                continue

            # xmit phase 3 - handle transfer completion
            await self._xmit_phase3(transaction)

        self.log.debug(f"Master({self.title}) Transmit pipeline completed")
        self.transfer_busy = False
        self.transmit_coroutine = None

        # Ensure signals are deasserted at the end
        if fifo_write in self.signal_map:
            write_signal = self.signal_map[fifo_write]
            if hasattr(self.bus, write_signal):
                getattr(self.bus, write_signal).value = 0
        else:
            self.write_sig.value = 0

        # Clear data signals
        if self.use_multi_signal:
            # Reset field signals
            for _, dut_signal_name in self.field_signals.items():
                if hasattr(self.bus, dut_signal_name):
                    getattr(self.bus, dut_signal_name).value = 0
        elif self.data_sig:
            self.data_sig.value = 0

    async def wait_cycles(self, cycles):
        """
        Wait for a specified number of clock cycles.

        Args:
            cycles: Number of cycles to wait
        """
        for _ in range(cycles):
            await RisingEdge(self.clock)
            await Timer(self.tick_delay, units=self.tick_units)
