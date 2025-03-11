"""Updated GAXI Components with support for multiple data signals"""

import cocotb
from collections import deque
from cocotb_bus.drivers import BusDriver
from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time

from .flex_randomizer import FlexRandomizer
from Components.gaxi_packet import GAXIPacket
from Components.debug_object import print_object_details


# Standard signal names for GAXI components
gaxi_master_signals = ['i_wr_valid', 'o_wr_ready', 'i_wr_data']
gaxi_slave_signals = ['o_rd_valid', 'i_rd_ready', 'o_rd_data']

gaxi_master_default_constraints = {
    'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 2, 1])
}
gaxi_slave_default_constraints = {
    'ready_delay': ([[0, 1], [2, 8], [9, 30]], [5, 2, 1])
}

class GAXIMaster(BusDriver):
    """
    Master driver for GAXI transactions.
    Controls valid signal and waits for ready.
    Can optionally use a memory model for data.

    Supports either:
    1. Single data bus (standard mode)
    2. Individual signals for each field (multi-signal mode)
    """
    def __init__(self, dut, title, prefix, clock, signals=None,
                    field_config=None, packet_class=GAXIPacket, timeout_cycles=1000,
                    randomizer=None, memory_model=None, memory_fields=None, log=None,
                    signal_map=None, **kwargs):
        """
        Initialize the GAXI master.

        Args:
            dut: Device under test
            title: title of the bus
            prefix: prefix used in the bus code
            clock: The clock signal
            signals: Custom signal list (overrides gaxi_master_signals)
            field_config: Field configuration for packets
            packet_class: Class to use for creating packets
            timeout_cycles: Maximum cycles to wait before timeout
            randomizer: FlexRandomizer instance for randomizing timing
            memory_model: Optional MemoryModel instance for reading/writing data
            memory_fields: Dictionary mapping memory fields to packet field names
            log: Logger instance
            signal_map: Dictionary mapping GAXI signals to DUT signals
                Format: {'i_wr_valid': 'dut_valid_signal', 'o_wr_ready': 'dut_ready_signal',
                            'i_wr_data_field1': 'dut_field1', ...}
                If provided, enables multi-signal mode for field data
            **kwargs: Additional arguments to pass to BusDriver
        """
        # Determine if we're using multi-signal mode (individual signals for each field)
        self.use_multi_signal = signal_map is not None
        self.signal_map = signal_map

        # Use standard signals if in standard mode and no signals provided
        if not self.use_multi_signal:
            self._signals = signals or gaxi_master_signals
        else:
            # In multi-signal mode, we only need valid/ready in the base _signals
            # The field signals will be handled separately
            self._signals = []

            # Add valid/ready signals from signal_map if provided
            if 'i_wr_valid' in signal_map:
                self._signals.append(signal_map['i_wr_valid'])
            else:
                self._signals.append('i_wr_valid')

            if 'o_wr_ready' in signal_map:
                self._signals.append(signal_map['o_wr_ready'])
            else:
                self._signals.append('o_wr_ready')

        self._optional_signals = []

        # Set up remaining parameters
        self.title = title
        self.clock = clock
        self.timeout_cycles = timeout_cycles
        self.field_config = field_config or {'data': {'bits': 32, 'default': 0, 'format': 'hex', 'display_width': 8}}
        self.packet_class = packet_class

        # Set up randomizer
        if randomizer is None:
            self.randomizer = FlexRandomizer(gaxi_master_default_constraints)
        else:
            self.randomizer = randomizer

        if not isinstance(self.randomizer, FlexRandomizer):
            raise ValueError(f"Master ({self.title}) self.randomizer is not properly initialized!")

        # Set up memory model integration
        self.memory_model = memory_model
        if memory_model and not memory_fields:
            # Default memory field mapping if not provided
            self.memory_fields = {
                'addr': 'addr',
                'data': 'data',
                'strb': 'strb'
            }
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

        # In multi-signal mode, verify all required field signals exist
        if self.use_multi_signal:
            self._initialize_multi_signal_mode()
        else:
            # Standard mode - initialize the single data bus
            self.bus.i_wr_valid.setimmediatevalue(0)
            self.bus.i_wr_data.setimmediatevalue(0)

        # Debug output
        self.log.info(f"GAXIMaster initialized for {title} in {'multi-signal' if self.use_multi_signal else 'standard'} mode")
        print_object_details(self, self.log, f"GAXI Master '{self.title}' INIT")

    def _initialize_multi_signal_mode(self):
        """Initialize signals in multi-signal mode."""
        # Initialize valid signal
        self.bus.i_wr_valid.setimmediatevalue(0)

        # Initialize field-specific data signals
        for field_name in self.field_config.keys():
            # Create the signal name for this field in the signal map
            field_signal_name = f'i_wr_data_{field_name}'

            # Skip 'data' field in multi-signal mode (it's split into individual fields)
            if field_name == 'data' and len(self.field_config) > 1:
                continue

            # Check if this field has a signal mapping
            if self.signal_map and field_signal_name in self.signal_map:
                dut_signal_name = self.signal_map[field_signal_name]

                # Verify signal exists on DUT
                if hasattr(self.bus, dut_signal_name):
                    # Initialize with default value from field config
                    default_value = self.field_config[field_name].get('default', 0)
                    getattr(self.bus, dut_signal_name).setimmediatevalue(default_value)
                else:
                    self.log.warning(f"Signal {dut_signal_name} specified in signal_map but not found on DUT")
            else:
                self.log.warning(f"No signal mapping provided for field {field_name}")

    def set_randomizer(self, randomizer):
        """
        Swap the current randomizer with a new one.

        Args:
            randomizer: New FlexRandomizer instance
        """
        self.randomizer = randomizer
        self.log.info(f"Set new randomizer for Master({self.title})")

    def is_signal_present(self, signal_name):
        """Check if a signal is present on the bus"""
        return hasattr(self.bus, signal_name) and getattr(self.bus, signal_name)

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
            self.memory_fields = {
                'addr': 'addr',
                'data': 'data',
                'strb': 'strb'
            }

    async def reset_bus(self):
        """
        Reset the bus to initial state.
        """
        self.log.debug(f"Master({self.title}): resetting the bus")

        # Reset valid signal
        self.bus.i_wr_valid.value = 0

        if self.use_multi_signal:
            # Reset individual field signals
            for field_name in self.field_config.keys():
                field_signal_name = f'i_wr_data_{field_name}'

                # Skip 'data' field in multi-signal mode
                if field_name == 'data' and len(self.field_config) > 1:
                    continue

                if self.signal_map and field_signal_name in self.signal_map:
                    dut_signal_name = self.signal_map[field_signal_name]
                    if hasattr(self.bus, dut_signal_name):
                        getattr(self.bus, dut_signal_name).value = 0
        else:
            # Standard mode - reset aggregate data signal
            self.bus.i_wr_data.value = 0

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
        self.log.debug(f'Master({self.title}): Adding to transmit queue: {transaction.formatted(compact=True)}')

        # Start transmission pipeline if not already running
        if hold or self.transmit_coroutine:
            self.log.debug(f'Master({self.title}): Not starting transmit pipeline: hold={hold}, transmit_coroutine={self.transmit_coroutine is not None}')
        else:
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
            if self.use_multi_signal:
                # Multi-signal mode: drive individual field signals
                for field_name, field_value in transaction.fields.items():
                    # Skip 'data' field in multi-signal mode (it's split into individual fields)
                    if field_name == 'data' and len(self.field_config) > 1:
                        continue

                    field_signal_name = f'i_wr_data_{field_name}'

                    if self.signal_map and field_signal_name in self.signal_map:
                        dut_signal_name = self.signal_map[field_signal_name]
                        if hasattr(self.bus, dut_signal_name):
                            getattr(self.bus, dut_signal_name).value = field_value
                        else:
                            self.log.warning(f"Signal {dut_signal_name} not found on DUT")
                            return False
                    else:
                        self.log.warning(f"No signal mapping for field {field_name}")
                        return False
            else:
                # Standard mode: drive aggregate data signal
                fifo_data = transaction.pack_for_fifo()
                if 'data' in fifo_data:
                    self.bus.i_wr_data.value = fifo_data['data']

            return True
        except Exception as e:
            self.log.error(f"Error driving signals: {e}")
            return False

    async def _transmit_pipeline(self):
        """
        Pipeline for transmitting transactions with support for multi-signal mode.
        """
        self.log.debug(f'Master({self.title}): Transmit pipeline started, queue length: {len(self.transmit_queue)}')
        self.transfer_busy = True

        while len(self.transmit_queue):
            # Get next transaction from the queue
            transaction = self.transmit_queue.popleft()
            transaction.start_time = get_sim_time('ns')
            self.log.debug(f"Master({self.title}) Processing transaction, remaining: "
                            f"{len(self.transmit_queue)} at {transaction.start_time}ns\n"
                            f"transaction={transaction.formatted(compact=True)}")

            # Apply any configured delay before asserting valid
            delay_dict = self.randomizer.next()
            valid_delay = delay_dict.get('valid_delay', 0)
            if valid_delay > 0:
                self.log.debug(f"Master({self.title}) Delaying valid assertion for {valid_delay} cycles")
                # Deassert valid during the wait period to prevent early handshake
                self.bus.i_wr_valid.value = 0

                # Clear data signals during delay
                if self.use_multi_signal:
                    # Reset individual field signals
                    for field_name in self.field_config.keys():
                        field_signal_name = f'i_wr_data_{field_name}'

                        # Skip 'data' field in multi-signal mode
                        if field_name == 'data' and len(self.field_config) > 1:
                            continue

                        if self.signal_map and field_signal_name in self.signal_map:
                            dut_signal_name = self.signal_map[field_signal_name]
                            if hasattr(self.bus, dut_signal_name):
                                getattr(self.bus, dut_signal_name).value = 0
                else:
                    # Standard mode - reset aggregate data signal
                    self.bus.i_wr_data.value = 0

                await self.wait_cycles(valid_delay)

            # Drive signals for this transaction
            if not self._drive_signals(transaction):
                self.log.error(f"Failed to drive signals for transaction: {transaction.formatted()}")
                self.transfer_busy = False
                return

            # Assert valid for this transaction
            self.bus.i_wr_valid.value = 1

            # Wait for the DUT to assert o_wr_ready (handshake completion)
            timeout_counter = 0
            while not self.bus.o_wr_ready.value:
                await FallingEdge(self.clock)
                timeout_counter += 1
                if timeout_counter >= self.timeout_cycles:
                    self.log.error(f"Master({self.title}) TIMEOUT waiting for ready after {self.timeout_cycles} cycles")
                    # Stop driving if timeout (prevent hang)
                    self.bus.i_wr_valid.value = 0

                    # Clear data signals
                    if self.use_multi_signal:
                        # Reset field signals
                        for field_name in self.field_config.keys():
                            field_signal_name = f'i_wr_data_{field_name}'

                            # Skip 'data' field in multi-signal mode
                            if field_name == 'data' and len(self.field_config) > 1:
                                continue

                            if self.signal_map and field_signal_name in self.signal_map:
                                dut_signal_name = self.signal_map[field_signal_name]
                                if hasattr(self.bus, dut_signal_name):
                                    getattr(self.bus, dut_signal_name).value = 0
                    else:
                        # Standard mode - reset aggregate data signal
                        self.bus.i_wr_data.value = 0

                    self.transfer_busy = False
                    return

            # Handshake occurred – capture completion time
            await RisingEdge(self.clock)
            current_time_ns = get_sim_time('ns')
            self.log.debug(f"Master({self.title}) Transaction completed at {current_time_ns}ns: "
                          f"{transaction.formatted(compact=True)}")
            transaction.end_time = current_time_ns
            self.sent_queue.append(transaction)

            # If more transactions in queue, prepare next one for pipelining
            if len(self.transmit_queue) > 0:
                next_trans = self.transmit_queue[0]

                if self.use_multi_signal:
                    # Drive field signals for next transaction
                    self._drive_signals(next_trans)
                else:
                    # Standard mode - drive aggregate data signal
                    next_fifo = next_trans.pack_for_fifo()
                    if 'data' in next_fifo:
                        self.bus.i_wr_data.value = next_fifo['data']

                # Keep valid asserted for pipelining
            else:
                # No more transactions - deassert valid
                self.bus.i_wr_valid.value = 0

                # Clear data signals
                if self.use_multi_signal:
                    # Reset field signals
                    for field_name in self.field_config.keys():
                        field_signal_name = f'i_wr_data_{field_name}'

                        # Skip 'data' field in multi-signal mode
                        if field_name == 'data' and len(self.field_config) > 1:
                            continue

                        if self.signal_map and field_signal_name in self.signal_map:
                            dut_signal_name = self.signal_map[field_signal_name]
                            if hasattr(self.bus, dut_signal_name):
                                getattr(self.bus, dut_signal_name).value = 0
                else:
                    # Standard mode - reset aggregate data signal
                    self.bus.i_wr_data.value = 0

            # Wait for next clock edge before processing subsequent transactions
            await RisingEdge(self.clock)

        self.log.debug(f"Master({self.title}) Transmit pipeline completed")
        self.transfer_busy = False
        self.transmit_coroutine = None

        # Ensure signals are deasserted at the end
        self.bus.i_wr_valid.value = 0

        # Clear data signals
        if self.use_multi_signal:
            # Reset field signals
            for field_name in self.field_config.keys():
                field_signal_name = f'i_wr_data_{field_name}'

                # Skip 'data' field in multi-signal mode
                if field_name == 'data' and len(self.field_config) > 1:
                    continue

                if self.signal_map and field_signal_name in self.signal_map:
                    dut_signal_name = self.signal_map[field_signal_name]
                    if hasattr(self.bus, dut_signal_name):
                        getattr(self.bus, dut_signal_name).value = 0
        else:
            # Standard mode - reset aggregate data signal
            self.bus.i_wr_data.value = 0

    async def wait_cycles(self, cycles):
        """
        Wait for a specified number of clock cycles.

        Args:
            cycles: Number of cycles to wait
        """
        for _ in range(cycles):
            await RisingEdge(self.clock)


class GAXISlave(BusMonitor):
    """
    Slave driver for GAXI transactions.
    Controls ready signal and monitors valid signals.
    Can optionally use a memory model for data.

    Supports either:
    1. Single data bus (standard mode)
    2. Individual signals for each field (multi-signal mode)
    """
    def __init__(self, dut, title, prefix, clock, signals=None,
                    field_config=None, packet_class=GAXIPacket, timeout_cycles=1000,
                    randomizer=None, memory_model=None, memory_fields=None,
                    log=None, mode='skid', signal_map=None, **kwargs):
        """
        Initialize the GAXI slave.

        Args:
            dut: Device under test
            title: title of the bus
            prefix: prefix used in the bus code
            clock: The clock signal
            signals: Custom signal list (overrides gaxi_slave_signals)
            field_config: Field configuration for packets
            packet_class: Class to use for creating packets
            timeout_cycles: Maximum cycles to wait before timeout
            randomizer: FlexRandomizer instance for randomizing timing
            memory_model: Optional MemoryModel instance for reading/writing data
            memory_fields: Dictionary mapping memory fields to packet field names
            log: Logger instance
            mode: Operating mode ('skid', 'fifo_mux', 'fifo_flop')
                    In 'fifo_mux' mode, use 'ow_rd_data' instead of 'o_rd_data'.
                    In 'fifo_flop' mode, capture read data one clock cycle after o_rd_valid asserts.
            signal_map: Dictionary mapping GAXI signals to DUT signals
                Format: {'o_rd_valid': 'dut_valid_signal', 'i_rd_ready': 'dut_ready_signal',
                            'o_rd_data_field1': 'dut_field1', ...}
                If provided, enables multi-signal mode for field data
            **kwargs: Additional arguments to pass to BusMonitor
        """
        # Validate mode parameter
        valid_modes = ['skid', 'fifo_mux', 'fifo_flop']
        if mode not in valid_modes:
            raise ValueError(f"Invalid mode '{mode}' for Slave ({title}). Mode must be one of: {', '.join(valid_modes)}")
    
        # Store title and log early for debug logging
        self.title = title
        log.debug(f"GAXISlave init for '{title}': randomizer={randomizer}, mode={mode}")

        # Determine if we're using multi-signal mode
        self.use_multi_signal = signal_map is not None
        self.signal_map = signal_map

        if not self.use_multi_signal:
            # Standard mode - use default or provided signals
            if signals:
                self._signals = signals
            elif mode == 'fifo_mux':
                # Use multiplexed data signal in 'fifo_mux' mode
                self._signals = ['o_rd_valid', 'i_rd_ready', 'ow_rd_data']
            else:
                self._signals = gaxi_slave_signals
        else:
            # Multi-signal mode - only include valid/ready in _signals
            self._signals = []

            # Add valid/ready signals from signal_map if provided
            if 'o_rd_valid' in signal_map:
                self._signals.append(signal_map['o_rd_valid'])
            else:
                self._signals.append('o_rd_valid')

            if 'i_rd_ready' in signal_map:
                self._signals.append(signal_map['i_rd_ready'])
            else:
                self._signals.append('i_rd_ready')

            # Field data signals will be handled separately

        self._optional_signals = []

        # Set up remaining parameters
        self.clock = clock
        self.timeout_cycles = timeout_cycles
        self.field_config = field_config or {
            'data': {'bits': 32, 'default': 0, 'format': 'hex', 'display_width': 8}
        }
        self.packet_class = packet_class
        self.mode = mode

        # Set up randomizer
        if randomizer is None:
            self.randomizer = FlexRandomizer(gaxi_slave_default_constraints)
        else:
            self.randomizer = randomizer
        if not isinstance(self.randomizer, FlexRandomizer):
            raise ValueError(f"Slave ({self.title}) self.randomizer is not properly initialized!")

        # Set up memory model integration
        self.memory_model = memory_model
        if memory_model and not memory_fields:
            # Default memory field mapping if not provided
            self.memory_fields = {
                'addr': 'addr',
                'data': 'data',
                'strb': 'strb'
            }
        else:
            self.memory_fields = memory_fields

        # Initialize parent BusMonitor (without auto-starting monitor)
        BusMonitor.__init__(self, dut, prefix, clock, callback=None, event=None, **kwargs)
        self.log = log  # Use provided logger (or inherited BusMonitor log if None)

        # Store field signal mappings for use in _monitor_recv
        self.field_signals = {}
        if self.use_multi_signal:
            self._initialize_multi_signal_mode()

        # Initialize output signals
        self.bus.i_rd_ready.setimmediatevalue(0)

        # Create received queue
        self.received_queue = deque()

        # Debug output
        self.log.info(f"GAXISlave initialized for {self.title} in mode '{self.mode}', {'multi-signal' if self.use_multi_signal else 'standard'}")
        print_object_details(self, self.log, f"GAXI Slave '{self.title}' INIT")

    def _initialize_multi_signal_mode(self):
        """Initialize and verify signals in multi-signal mode."""
        # Check field signal mappings
        for field_name in self.field_config.keys():
            # Skip 'data' field in multi-signal mode (it's split into individual fields)
            if field_name == 'data' and len(self.field_config) > 1:
                continue

            field_signal_name = f'o_rd_data_{field_name}'

            if self.signal_map and field_signal_name in self.signal_map:
                dut_signal_name = self.signal_map[field_signal_name]

                # Store mapping for _monitor_recv
                self.field_signals[field_name] = dut_signal_name

                # Verify signal exists
                if not hasattr(self.bus, dut_signal_name):
                    self.log.warning(f"Signal {dut_signal_name} specified in signal_map but not found on DUT")
            else:
                self.log.warning(f"No signal mapping provided for field {field_name}")

    def is_signal_present(self, signal_name):
        """Check if a signal is present on the bus"""
        return hasattr(self.bus, signal_name) and getattr(self.bus, signal_name) is not None

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
            self.memory_fields = {
                'addr': 'addr',
                'data': 'data',
                'strb': 'strb'
            }

    async def reset_bus(self):
        """
        Reset the bus to initial state.
        """
        self.log.debug(f"Slave({self.title}): resetting the bus")
        # Deassert ready signal
        self.bus.i_rd_ready.value = 0
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

        Args:
            current_time: Current simulation time
            packet: The packet to finish
            data_dict: Dictionary of field data (for multi-signal mode)
                       or single 'data' value (for standard mode)
        """
        if self.use_multi_signal:
            # Multi-signal mode: data is already in correct fields
            if data_dict:
                for field_name, value in data_dict.items():
                    setattr(packet, field_name, value)
        else:
            # Standard mode: unpack data from single value
            if data_dict and 'data' in data_dict:
                fifo_data = {'data': data_dict['data']}
                packet.unpack_from_fifo(fifo_data)

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

    async def _monitor_recv(self):
        """
        Monitor for incoming transactions (read channel).
        Handles both standard and multi-signal modes.
        """
        try:
            last_packet = None
            last_xfer = False

            while True:
                # Wait a brief moment for signal stability
                await Timer(200, units='ps')

                current_time = get_sim_time('ns')

                # Check if last transfer is pending (fifo_flop mode)
                if last_xfer:
                    packet = last_packet

                    if self.use_multi_signal:
                        # Multi-signal mode: collect data from field signals
                        data_dict = {}
                        for field_name, dut_signal_name in self.field_signals.items():
                            if hasattr(self.bus, dut_signal_name):
                                signal = getattr(self.bus, dut_signal_name)
                                if signal.value.is_resolvable:
                                    data_dict[field_name] = int(signal.value)

                        self._finish_packet(current_time, packet, data_dict)
                    else:
                        # Standard mode
                        data_val = int(self.bus.o_rd_data.value)
                        self._finish_packet(current_time, packet, {'data': data_val})

                # Always clear the last transfer here
                last_xfer = False

                # Determine ready delay for this cycle
                delay_cfg = self.randomizer.next()
                ready_delay = delay_cfg.get('ready_delay', 0)
                if ready_delay > 0:
                    self.log.debug(f"Slave({self.title}) Delaying ready assertion for {ready_delay} cycles")
                    self.bus.i_rd_ready.value = 0
                    await self.wait_cycles(ready_delay)

                # Assert ready to accept data
                self.bus.i_rd_ready.value = 1

                # Wait for a falling edge to sample valid (allow combinatorial settle)
                await FallingEdge(self.clock)

                # Check for valid assertion
                if self.bus.o_rd_valid.value == 1:
                    # Create a new packet
                    packet = self.packet_class(self.field_config)
                    packet.start_time = current_time

                    if self.mode != 'fifo_flop':
                        # Immediate capture (skid and mux modes)
                        if self.use_multi_signal:
                            # Multi-signal mode: collect data from field signals
                            data_dict = {}
                            for field_name, dut_signal_name in self.field_signals.items():
                                if hasattr(self.bus, dut_signal_name):
                                    signal = getattr(self.bus, dut_signal_name)
                                    if signal.value.is_resolvable:
                                        data_dict[field_name] = int(signal.value)

                            self._finish_packet(current_time, packet, data_dict)
                        else:
                            # Standard mode
                            if self.mode == 'fifo_mux' and hasattr(self.bus, 'ow_rd_data'):
                                data_val = int(self.bus.ow_rd_data.value)
                            else:
                                data_val = int(self.bus.o_rd_data.value)

                            self._finish_packet(current_time, packet, {'data': data_val})
                    else:
                        # 'fifo_flop' mode: note handshake time, defer data capture to next cycle
                        last_xfer = True
                        last_packet = packet

                # Deassert ready on the rising edge (prepare for next cycle or delay)
                await RisingEdge(self.clock)
                self.bus.i_rd_ready.value = 0

        except Exception as e:
            self.log.error(f"Slave({self.title}) Exception in _monitor_recv: {e}")
            raise

    async def wait_cycles(self, cycles):
        """Wait for a number of clock cycles."""
        for _ in range(cycles):
            await RisingEdge(self.clock)


class GAXIMonitor(BusMonitor):
    """
    Monitor for GAXI bus transactions.
    Observes valid/ready handshake without driving signals.

    Supports either:
    1. Single data bus (standard mode)
    2. Individual signals for each field (multi-signal mode)
    """
    def __init__(self, dut, title, prefix, clock, signals=None, is_slave=False,
                    field_config=None, packet_class=GAXIPacket, timeout_cycles=1000,
                    log=None, mode='skid', signal_map=None, **kwargs):
        """
        Initialize the GAXI bus monitor.

        Args:
            dut: Device under test
            title: Title of the bus
            prefix: prefix used in the bus code
            clock: The clock signal
            signals: Custom signal list (overrides default signals)
            is_slave: If True, use slave signals; if False, use master signals
            field_config: Field configuration for packets
            packet_class: Class to use for creating packets
            timeout_cycles: Maximum cycles to wait before timeout
            log: Logger instance
            mode: Operating mode ('skid', 'fifo_mux', 'fifo_flop')
                    In 'fifo_mux' mode (slave side), use 'ow_rd_data' instead of 'o_rd_data'.
                    In 'fifo_flop' mode, capture data one clock after valid/ready handshake.
            signal_map: Dictionary mapping GAXI signals to DUT signals
                Format depends on is_slave parameter:
                - Slave: {'o_rd_valid': 'dut_valid', 'i_rd_ready': 'dut_ready', 'o_rd_data_field1': 'dut_field1', ...}
                - Master: {'i_wr_valid': 'dut_valid', 'o_wr_ready': 'dut_ready', 'i_wr_data_field1': 'dut_field1', ...}
                If provided, enables multi-signal mode for field data
            **kwargs: Additional arguments to pass to BusMonitor
        """
        # Validate mode parameter
        valid_modes = ['skid', 'fifo_mux', 'fifo_flop']
        if mode not in valid_modes:
            raise ValueError(f"Invalid mode '{mode}' for Slave ({title}). Mode must be one of: {', '.join(valid_modes)}")

        # Determine if we're using multi-signal mode
        self.use_multi_signal = signal_map is not None
        self.signal_map = signal_map

        # Default signal sets based on is_slave and mode
        if not self.use_multi_signal:
            if signals:
                self._signals = signals
            elif is_slave and mode == 'fifo_mux':
                # In mux mode (slave side), use multiplexed read data signal
                self._signals = ['o_rd_valid', 'i_rd_ready', 'ow_rd_data']
            else:
                self._signals = gaxi_slave_signals if is_slave else gaxi_master_signals
        else:
            # Multi-signal mode - only include valid/ready in _signals
            self._signals = []

            # Add valid/ready signals based on slave/master orientation
            if is_slave:
                # Slave-oriented monitor
                if 'o_rd_valid' in signal_map:
                    self._signals.append(signal_map['o_rd_valid'])
                else:
                    self._signals.append('o_rd_valid')

                if 'i_rd_ready' in signal_map:
                    self._signals.append(signal_map['i_rd_ready'])
                else:
                    self._signals.append('i_rd_ready')
            else:
                # Master-oriented monitor
                if 'i_wr_valid' in signal_map:
                    self._signals.append(signal_map['i_wr_valid'])
                else:
                    self._signals.append('i_wr_valid')

                if 'o_wr_ready' in signal_map:
                    self._signals.append(signal_map['o_wr_ready'])
                else:
                    self._signals.append('o_wr_ready')

        self._optional_signals = []

        # Initialize base BusMonitor (don't auto-start monitoring)
        BusMonitor.__init__(self, dut, prefix, clock, callback=None, event=None, **kwargs)

        # Set up instance attributes
        self.log = log or self._log
        self.clock = clock
        self.title = title
        self.timeout_cycles = timeout_cycles
        self.field_config = field_config or {
            'data': {'bits': 32, 'default': 0, 'format': 'hex', 'display_width': 8}
        }
        self.packet_class = packet_class
        self.mode = mode
        self.is_slave = is_slave

        # Initialize queue for observed transactions
        self.observed_queue = deque()

        # Store field signal mappings for use in _monitor_recv
        self.field_signals = {}

        if self.use_multi_signal:
            self._initialize_multi_signal_mode()
        else:
            # Map standard bus signals to internal references for easy access
            self._setup_standard_signals()

        # Debug output
        self.log.info(f"GAXIMonitor initialized for {title} (mode: {mode}, {'multi-signal' if self.use_multi_signal else 'standard'})")

    def _initialize_multi_signal_mode(self):
        """Initialize signal mappings for multi-signal mode."""
        # Set up valid/ready signal references
        if self.is_slave:
            # Slave-side monitor
            valid_signal_name = self.signal_map.get('o_rd_valid', 'o_rd_valid')
            ready_signal_name = self.signal_map.get('i_rd_ready', 'i_rd_ready')

            # Set up field signal mappings
            prefix = 'o_rd_data_'
        else:
            # Master-side monitor
            valid_signal_name = self.signal_map.get('i_wr_valid', 'i_wr_valid')
            ready_signal_name = self.signal_map.get('o_wr_ready', 'o_wr_ready')

            # Set up field signal mappings
            prefix = 'i_wr_data_'

        # Map valid/ready signals
        self.valid_signal = getattr(self.bus, valid_signal_name)
        self.ready_signal = getattr(self.bus, ready_signal_name)

        # Map field signals
        for field_name in self.field_config.keys():
            # Skip 'data' field in multi-signal mode (it's split into individual fields)
            if field_name == 'data' and len(self.field_config) > 1:
                continue

            field_signal_name = f'{prefix}{field_name}'

            if self.signal_map and field_signal_name in self.signal_map:
                dut_signal_name = self.signal_map[field_signal_name]

                # Store mapping for _monitor_recv
                self.field_signals[field_name] = dut_signal_name

                # Verify signal exists
                if not hasattr(self.bus, dut_signal_name):
                    self.log.warning(f"Signal {dut_signal_name} specified in signal_map but not found on DUT")
            else:
                self.log.warning(f"No signal mapping provided for field {field_name}")

    def _setup_standard_signals(self):
        """Set up references to standard signals."""
        if self.is_slave:
            self.valid_signal = self.bus.o_rd_valid
            self.ready_signal = self.bus.i_rd_ready
            if self.mode == 'fifo_mux' and hasattr(self.bus, 'ow_rd_data'):
                self.data_signal = self.bus.ow_rd_data
            else:
                self.data_signal = self.bus.o_rd_data
        else:
            self.valid_signal = self.bus.i_wr_valid
            self.ready_signal = self.bus.o_wr_ready
            self.data_signal = self.bus.i_wr_data

    def is_signal_present(self, signal_name):
        """Check if a signal is present on the bus"""
        return hasattr(self.bus, signal_name) and getattr(self.bus, signal_name) is not None

    def _finish_packet(self, current_time, packet, data_dict=None):
        """
        Finish packet processing and trigger callbacks.

        Args:
            current_time: Current simulation time
            packet: The packet to finish
            data_dict: Dictionary of field data (for multi-signal mode)
                       or single 'data' value (for standard mode)
        """
        if self.use_multi_signal:
            # Multi-signal mode: data is already in correct fields
            if data_dict:
                for field_name, value in data_dict.items():
                    setattr(packet, field_name, value)
        else:
            # Standard mode: unpack data from single value
            if data_dict and 'data' in data_dict:
                fifo_data = {'data': data_dict['data']}
                packet.unpack_from_fifo(fifo_data)

        # Record completion time and store packet
        packet.end_time = current_time
        self.observed_queue.append(packet)
        self.log.debug(f"Monitor({self.title}) Transaction received at {packet.end_time}ns: {packet.formatted(compact=True)}")
        self._recv(packet)  # trigger callbacks

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

                # Wait a brief moment for signal stability
                await Timer(200, units='ps')

                # Check if last transfer is pending (fifo_flop mode)
                if last_xfer:
                    packet = last_packet

                    if self.use_multi_signal:
                        # Multi-signal mode: collect data from field signals
                        data_dict = {}
                        for field_name, dut_signal_name in self.field_signals.items():
                            if hasattr(self.bus, dut_signal_name):
                                signal = getattr(self.bus, dut_signal_name)
                                if signal.value.is_resolvable:
                                    data_dict[field_name] = int(signal.value)

                        self._finish_packet(current_time, packet, data_dict)
                    else:
                        # Standard mode
                        data_val = int(self.data_signal.value)
                        self._finish_packet(current_time, packet, {'data': data_val})

                # Always clear the last transfer here
                last_xfer = False

                # Check for a valid handshake on this cycle
                if (self.valid_signal.value.is_resolvable and
                        self.ready_signal.value.is_resolvable and
                        self.valid_signal.value.integer == 1 and
                        self.ready_signal.value.integer == 1):

                    # Create a new packet
                    packet = self.packet_class(self.field_config)
                    packet.start_time = current_time

                    if self.mode != 'fifo_flop':
                        # Immediate capture (skid and mux modes)
                        if self.use_multi_signal:
                            # Multi-signal mode: collect data from field signals
                            data_dict = {}
                            for field_name, dut_signal_name in self.field_signals.items():
                                if hasattr(self.bus, dut_signal_name):
                                    signal = getattr(self.bus, dut_signal_name)
                                    if signal.value.is_resolvable:
                                        data_dict[field_name] = int(signal.value)

                            self._finish_packet(current_time, packet, data_dict)
                        else:
                            # Standard mode
                            data_val = int(self.data_signal.value)
                            self._finish_packet(current_time, packet, {'data': data_val})
                    else:
                        # 'fifo_flop' mode: note handshake time, defer data capture to next cycle
                        last_xfer = True
                        last_packet = packet

        except Exception as e:
            self.log.error(f"Exception in _monitor_recv: {str(e)}")
            import traceback
            self.log.error(traceback.format_exc())
            raise
