"""FIFO Master/Slave/Monitor Components with required and optional signal support"""
import cocotb
from collections import deque
from cocotb_bus.drivers import BusDriver
from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time

from ..flex_randomizer import FlexRandomizer
from .fifo_packet import FIFOPacket

# Standard Signal names for all master/slave/monitor objects
fifo_write = 'i_write'
fifo_wr_full = 'o_wr_full'
fifo_wr_data = 'i_wr_data'
fifo_read = 'i_read'
fifo_rd_empty = 'o_rd_empty'
fifo_rd_data = 'o_rd_data'
fifo_rd_data_wire = 'ow_rd_data'  # for fifo_mux mode

fifo_valid_modes = ['skid', 'fifo_mux', 'fifo_flop']

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
    'read_delay': ([[0, 1], [2, 8], [9, 30]], [5, 2, 1])
}

# Basic, default field config
fifo_basic_field_config = {'data': {'bits': 32, 'default': 0, 'format': 'hex', 'display_width': 8}}

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
        self.field_config = field_config or fifo_basic_field_config
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

        # Use standard signals if in standard mode and no signals provided
        if not self.use_multi_signal:
            # Use the mapping to translate standardized names to DUT signal names
            self._signals = [self.write_dut_name, self.full_dut_name, self.data_dut_name]
        else:
            # In multi-signal mode, we need at least write/full in the base _signals
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
        for field_name in self.field_config.keys():
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
            # Get FIFO-adjusted values for all fields
            fifo_data = transaction.pack_for_fifo()
            
            if self.use_multi_signal:
                # Multi-signal mode: drive individual field signals
                for field_name, field_value in fifo_data.items():
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
            else:
                # Standard mode: Use single data signal
                # Check if there's only one field (typically 'data')
                if len(fifo_data) == 1 and 'data' in fifo_data:
                    # Simple case: only a data field
                    if self.data_sig:
                        self.data_sig.value = fifo_data['data']
                else:
                    # Multiple fields need to be packed into a single value
                    if self.data_sig:
                        combined_value = 0
                        bit_offset = 0
                        
                        # Process fields in the order defined in field_config
                        for field_name, config in transaction.field_config.items():
                            if field_name in fifo_data:
                                field_width = config.get('bits', 0)
                                field_value = fifo_data[field_name]
                                
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
        else:
            # Standard mode - reset aggregate data signal
            if self.data_sig:
                self.data_sig.value = 0

    async def _xmit_phase1(self):
        """First phase of transmission - delay and prepare signals"""
        # Apply any configured delay before asserting write
        delay_dict = self.randomizer.next()
        write_delay = delay_dict.get('write_delay', 0)
        if write_delay > 0:
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
            await FallingEdge(self.clock)
            
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

        while len(self.transmit_queue):
            # Get next transaction from the queue
            transaction = self.transmit_queue.popleft()
            transaction.start_time = get_sim_time('ns')

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
        else:
            # Standard mode - reset aggregate data signal
            if self.data_sig:
                self.data_sig.value = 0

    async def wait_cycles(self, cycles):
        """
        Wait for a specified number of clock cycles.

        Args:
            cycles: Number of cycles to wait
        """
        for _ in range(cycles):
            await RisingEdge(self.clock)


class FIFOSlave(BusMonitor):
    """
    Slave driver for FIFO transactions.
    Controls i_read signal and monitors o_rd_empty.
    Can optionally use a memory model for data.

    Supports:
    1. Single data bus (standard mode)
    2. Individual signals for each field (multi-signal mode)
    3. Optional signals with fallback behavior
    """
    def __init__(self, dut, title, prefix, clock,
                field_config=None, packet_class=FIFOPacket, timeout_cycles=1000,
                randomizer=None, memory_model=None, memory_fields=None,
                multi_sig=False, log=None, mode='skid', signal_map=None, optional_signal_map=None, **kwargs):
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
            log: Logger instance
            multi_sig: Use multiple signals or not
            mode: 'skid', 'fifo_mux', or 'fifo_flop'
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
        self.timeout_cycles = timeout_cycles
        self.field_config = field_config or fifo_basic_field_config
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
        self.empty_name = fifo_rd_empty
        self.read_name = fifo_read
        
        # Data signal based on mode
        if mode == 'fifo_mux':
            self.data_name = fifo_rd_data_wire
        else:
            self.data_name = fifo_rd_data

        # Get the actual DUT signal names from the map
        self.empty_dut_name = self.signal_map.get(self.empty_name, self.empty_name)
        self.read_dut_name = self.signal_map.get(self.read_name, self.read_name)
        self.data_dut_name = self.optional_signal_map.get(self.data_name, self.data_name)

        # Prepare signal lists for BusMonitor initialization
        if self.use_multi_signal:
            # Multi-signal mode - only include empty/read in _signals
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
        self.log.debug(f"FIFOSlave init for '{title}': _signals={self._signals}")

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

        # Debug output
        if log:
            self.log.info(f"FIFOSlave initialized for {self.title} in mode '{self.mode}', {'multi-signal' if self.use_multi_signal else 'standard'}")

    def _initialize_multi_signal_mode(self):
        """Initialize and verify signals in multi-signal mode."""
        # Check field signal mappings
        for field_name in self.field_config.keys():
            field_signal_name = f'o_rd_data_{field_name}'

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
            self.memory_fields = fifo_memory_fields

    async def reset_bus(self):
        """
        Reset the bus to initial state.
        """
        self.log.debug(f"Slave({self.title}): resetting the bus")

        # Deassert read signal
        if fifo_read in self.signal_map:
            read_signal = self.signal_map[fifo_read]
            if hasattr(self.bus, read_signal):
                getattr(self.bus, read_signal).value = 0
        else:
            self.read_sig.value = 0

        # Clear any queued transactions
        self.received_queue = deque()

    def _read_from_memory(self, transaction):
        """
        Read data from memory model based on transaction address.

        Args:
            transaction: The transaction containing the address to read from

        Returns:
            Data read from memory, or None if memory model not used or read failed
        """
        if not self.memory_model or not self.memory_fields:
            return None
        try:
            addr_field = self.memory_fields.get('addr', 'addr')
            if hasattr(transaction, addr_field):
                addr = getattr(transaction, addr_field)
                data_bytes = self.memory_model.read(addr, self.memory_model.bytes_per_line)
                data = self.memory_model.bytearray_to_integer(data_bytes)
                self.log.debug(f"Slave({self.title}) Read from memory: addr=0x{addr:X}, data=0x{data:X}")
                return data
        except Exception as e:
            self.log.error(f"Slave({self.title}) Error reading from memory: {e}")
        return None

    def _finish_packet(self, current_time, packet, data_dict=None):
        """
        Finish packet processing and trigger callbacks.
        """
        # Standard mode with complex field config (special case for data_collect)
        if not self.use_multi_signal and len(packet.field_config) > 1 and isinstance(data_dict, dict) and 'data' in data_dict:
            # We have a single data value but multiple fields in the config
            combined_value = data_dict['data']
            unpacked_fields = {}
            bit_offset = 0
            
            # Process fields in the order defined in field_config
            fields = list(packet.field_config.keys())
            
            for field_name in fields:
                config = packet.field_config[field_name]
                field_width = config.get('bits', 0)
                mask = (1 << field_width) - 1
                
                # Extract field value using mask and shift
                field_value = (combined_value >> bit_offset) & mask
                unpacked_fields[field_name] = field_value
                
                bit_offset += field_width

            # Replace data_dict with unpacked fields
            data_dict = unpacked_fields
        
        # Standard unpacking
        if data_dict:
            packet.unpack_from_fifo(data_dict)
            
        # Apply memory model data, if applicable
        if self.memory_model and self.memory_fields:
            data_field = self.memory_fields.get('data', 'data')
            mem_val = self._read_from_memory(packet)
            if mem_val is not None:
                setattr(packet, data_field, mem_val)

        # Record completion time and store packet
        packet.end_time = current_time
        self.received_queue.append(packet)
        self.log.debug(f"Slave({self.title}) Transaction received at {packet.end_time}ns: {packet.formatted(compact=True)}")
        self._recv(packet)  # trigger callbacks

    def _get_data_dict(self):
        """
        Collect data from field signals.

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
                        data_dict[field_name] = int(signal.value)
                    else:
                        self.log.warning(f"Field {field_name} has X/Z value")
                        data_dict[field_name] = -1  # Indicate X/Z value
                else:
                    self.log.debug(f"Signal {dut_signal_name} not found on DUT")
        else:
            # Standard mode: get from the aggregated data signal
            if self.data_sig and self.data_sig.value.is_resolvable:
                # In standard mode with a single 'data' field
                if 'data' in self.field_config:
                    data_dict['data'] = int(self.data_sig.value)
                else:
                    # Handle multi-field configuration in standard mode
                    data_dict['data'] = int(self.data_sig.value)
            elif self.data_sig:
                self.log.warning("Data signal has X/Z value")
                data_dict['data'] = -1  # Indicate X/Z value
                
        return data_dict

    def _set_read_value(self, value):
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

            # Get data from FIFO for flop mode
            data_dict = self._get_data_dict()
            self._finish_packet(current_time, packet, data_dict)

        return current_time

    async def _recv_phase2(self):
        """Receive phase 2: Handle read delays and assert read if not empty"""
        # Determine read delay for this cycle
        delay_cfg = self.randomizer.next()
        read_delay = delay_cfg.get('read_delay', 0)
        if read_delay > 0:
            # Deassert read during delay
            self._set_read_value(0)
            await self.wait_cycles(read_delay)

        # Check if FIFO is empty
        if not self.empty_sig.value:
            # FIFO is not empty, we can read
            self._set_read_value(1)
        else:
            # FIFO is empty, keep read deasserted
            self._set_read_value(0)

        # Wait for a falling edge to sample signals
        await FallingEdge(self.clock)

    async def _recv_phase3(self, current_time):
        """Receive phase 3: Check for valid read and process transaction"""
        # Check if we're reading and FIFO is not empty
        if (self.read_sig.value.is_resolvable and 
            self.empty_sig.value.is_resolvable and
            self.read_sig.value.integer == 1 and
            self.empty_sig.value.integer == 0):
            
            # Create a new packet
            packet = self.packet_class(self.field_config)
            packet.start_time = current_time

            # Check for read while empty error
            if self.empty_sig.value and self.read_sig.value:
                self.log.error(f"Error: {self.title} read while fifo empty")

            if self.mode == 'fifo_flop':
                # 'fifo_flop' mode: note read time, defer data capture to next cycle
                last_xfer = True
                last_packet = packet
                await RisingEdge(self.clock)
                return last_packet, last_xfer
            else:
                # For fifo_mux mode, capture data in the same cycle
                data_dict = self._get_data_dict()
                self._finish_packet(current_time, packet, data_dict)

        # Deassert read on the rising edge (prepare for next cycle or delay)
        await RisingEdge(self.clock)
        self._set_read_value(0)

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
            raise

    async def wait_cycles(self, cycles):
        """Wait for a number of clock cycles."""
        for _ in range(cycles):
            await RisingEdge(self.clock)


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
        self.field_config = field_config or fifo_basic_field_config
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
            elif mode == 'skid':
                self.optional_signal_map = slave_skid_optional_signal_map
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
        if not self.use_multi_signal:
            # Standard mode - use mapped signal names
            self._signals = [self.control1_dut_name, self.control2_dut_name, self.data_dut_name]
        else:
            # Multi-signal mode - only include control signals
            self._signals = [self.control1_dut_name, self.control2_dut_name]

        # Set up optional signals
        self._optional_signals = []
        if self.optional_signal_map:
            self._optional_signals.extend(
                dut_name for _, dut_name in self.optional_signal_map.items()
            )

        # Initialize base BusMonitor (don't auto-start monitoring)
        BusMonitor.__init__(self, dut, prefix, clock, callback=None, event=None, **kwargs)
        self.log = log or self._log
        self.log.debug(f"FIFOMonitor init for '{title}': mode={mode}")

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

        # Initialize queue for observed transactions
        self.observed_queue = deque()

        # Create a mapping of field names to DUT signals for multi-signal mode
        self.field_signals = {}

        if self.use_multi_signal:
            self._initialize_multi_signal_mode()

        # Debug output
        port_type = "read" if is_slave else "write"
        self.log.info(f"FIFOMonitor initialized for {title} {port_type} port in mode '{mode}', "
                      f"{'multi-signal' if self.use_multi_signal else 'standard'}")

    def clear_queue(self):
        """Clear the observed transactions queue after scoreboard validation."""
        self.observed_queue.clear()
        self.log.info(f"FIFOMonitor ({self.title}): Observed queue cleared after scoreboard check.")

    def _initialize_multi_signal_mode(self):
        """Initialize signal mappings for multi-signal mode with fallback to standard signals."""
        # Check field signal mappings
        for field_name in self.field_config.keys():
            if self.is_slave:
                # Read port - use output data signals
                field_signal_name = f'o_rd_data_{field_name}'
            else:
                # Write port - use input data signals
                field_signal_name = f'i_wr_data_{field_name}'

            # Check required signal map first
            if field_signal_name in self.signal_map:
                dut_signal_name = self.signal_map[field_signal_name]
                self._register_field_signal(field_name, dut_signal_name, required=True)

            # Then check optional signal map
            elif field_signal_name in self.optional_signal_map:
                dut_signal_name = self.optional_signal_map[field_signal_name]
                self._register_field_signal(field_name, dut_signal_name, required=False)

            else:
                self.log.warning(f"FIFOMonitor({self.title}): No signal mapping provided for field {field_name}")

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

    def _finish_packet(self, current_time, packet, data_dict=None):
        """
        Finish packet processing and trigger callbacks.
        
        Args:
            current_time: Current simulation time
            packet: The packet to finish
            data_dict: Dictionary of field data (for multi-signal mode)
                    or single 'data' value (for standard mode)
        """
        # Standard mode with complex field config (special case for data_collect)
        if not self.use_multi_signal and len(packet.field_config) > 1 and isinstance(data_dict, dict) and 'data' in data_dict:
            # We have a single data value but multiple fields in the config
            combined_value = data_dict['data']
            unpacked_fields = {}
            bit_offset = 0
            
            # Process fields in the order defined in field_config
            fields = list(packet.field_config.keys())
            
            for field_name in fields:
                config = packet.field_config[field_name]
                field_width = config.get('bits', 0)
                mask = (1 << field_width) - 1
                
                # Extract field value using mask and shift
                field_value = (combined_value >> bit_offset) & mask
                unpacked_fields[field_name] = field_value
                
                bit_offset += field_width

            # Replace data_dict with unpacked fields
            data_dict = unpacked_fields
        
        # Use the packet's unpack_from_fifo method for field handling
        if data_dict:
            packet.unpack_from_fifo(data_dict)

        # Record completion time and store packet
        packet.end_time = current_time
        self.observed_queue.append(packet)
        self.log.debug(f"Monitor({self.title}) Transaction observed at {packet.end_time}ns: {packet.formatted(compact=True)}")
        self._recv(packet)  # trigger callbacks

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
                        data_dict[field_name] = int(signal.value)
                    else:
                        self.log.warning(f"Field {field_name} has X/Z value")
                        data_dict[field_name] = -1  # Indicate X/Z value
                else:
                    self.log.debug(f"Signal {dut_signal_name} not found on DUT")
        else:
            # Standard mode: get from the aggregated data signal
            if self.data_sig and self.data_sig.value.is_resolvable:
                # In standard mode with a single 'data' field
                if len(self.field_config) == 1 and 'data' in self.field_config:
                    data_dict['data'] = int(self.data_sig.value)
                else:
                    # Handle multi-field configuration in standard mode
                    # For now, just store the raw value in 'data'
                    data_dict['data'] = int(self.data_sig.value)
            elif self.data_sig:
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

            # Get data from FIFO for flop mode
            data_dict = self._get_data_dict()
            self._finish_packet(current_time, packet, data_dict)

        return current_time

    async def _recv_phase2(self, current_time, last_packet, last_xfer):
        """
        Receive phase 2: Check for valid transaction and process it

        Returns:
            tuple: (last_packet, last_xfer) for next cycle
        """
        # For read port monitoring
        if self.is_slave:
            # Check if reading and not empty
            if (self.control1_sig.value.is_resolvable and
                self.control2_sig.value.is_resolvable and
                self.control1_sig.value.integer == 0 and  # not empty
                self.control2_sig.value.integer == 1):     # read
                
                # Create a new packet
                packet = self.packet_class(self.field_config)
                packet.start_time = current_time

                # Check for read while empty error
                if self.control1_sig.value.integer and self.control2_sig.value.integer:
                    self.log.error(f"Error: {self.title} read while fifo empty observed")

                if self.mode == 'fifo_flop':
                    # 'fifo_flop' mode: defer data capture to next cycle
                    last_xfer = True
                    last_packet = packet
                else:
                    # Capture data for this transaction
                    data_dict = self._get_data_dict()
                    self._finish_packet(current_time, packet, data_dict)
        else:
            # For write port monitoring
            # Check if writing and not full
            if (self.control1_sig.value.is_resolvable and
                self.control2_sig.value.is_resolvable and
                self.control1_sig.value.integer == 1 and  # write
                self.control2_sig.value.integer == 0):     # not full
                
                # Create a new packet
                packet = self.packet_class(self.field_config)
                packet.start_time = current_time

                # Check for write while full error
                if self.control1_sig.value.integer and self.control2_sig.value.integer:
                    self.log.error(f"Error: {self.title} write while fifo full observed")

                # Capture data for this transaction
                data_dict = self._get_data_dict()
                self._finish_packet(current_time, packet, data_dict)

        return last_packet, last_xfer

    async def _monitor_recv(self):
        """
        Monitor for FIFO transactions.
        Handles both read and write port monitoring.
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

                # recv phase 2: Check for valid transaction and process it
                last_packet, last_xfer = await self._recv_phase2(current_time, last_packet, last_xfer)

        except Exception as e:
            self.log.error(f"FIFOMonitor({self.title}): Exception in _monitor_recv: {str(e)}")
            import traceback
            self.log.error(traceback.format_exc())
            raise
