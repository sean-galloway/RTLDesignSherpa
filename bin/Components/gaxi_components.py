"""Updated GAXI Master/Slave/Monitor Components with required and optional signal support"""
import pprint

import cocotb
from collections import deque
from cocotb_bus.drivers import BusDriver
from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time

from .flex_randomizer import FlexRandomizer
from Components.gaxi_packet import GAXIPacket
from Components.debug_object import print_object_details, print_dict_to_log


# Standard signal names for GAXI Master components
gaxi_master_signals = ['i_wr_valid', 'o_wr_ready', 'i_wr_data']

gaxi_master_default_constraints = {
    'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 2, 1])
}

# Standard signal names for GAXI Slave components
gaxi_slave_signals = ['o_rd_valid', 'i_rd_ready', 'o_rd_data']

gaxi_slave_default_constraints = {
    'ready_delay': ([[0, 1], [2, 8], [9, 30]], [5, 2, 1])
}


class GAXIMaster(BusDriver):
    """
    Master driver for GAXI transactions.
    Controls valid signal and waits for ready.
    Can optionally use a memory model for data.

    Supports:
    1. Single data bus (standard mode)
    2. Individual signals for each field (multi-signal mode)
    3. Optional signals with fallback behavior
    """
    def __init__(self, dut, title, prefix, clock, signals=None,
                    field_config=None, packet_class=GAXIPacket, timeout_cycles=1000,
                    randomizer=None, memory_model=None, memory_fields=None, log=None,
                    signal_map=None, optional_signal_map=None, **kwargs):
        # sourcery skip: low-code-quality
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
                Format: {'i_wr_valid': 'dut_valid_signal', 'o_wr_ready': 'dut_ready_signal', ...}
            optional_signal_map: Dictionary mapping optional GAXI signals to DUT signals
                These signals won't cause errors if missing from the DUT
            **kwargs: Additional arguments to pass to BusDriver
        """
        # Determine if we're using multi-signal mode (individual signals for each field)
        self.use_multi_signal = (signal_map is not None) or (optional_signal_map is not None)
        self.signal_map = signal_map or {}
        self.optional_signal_map = optional_signal_map or {}

        msg_multi = None
        # Use standard signals if in standard mode and no signals provided
        if not self.use_multi_signal:
            self._signals = signals or gaxi_master_signals
        else:
            # In multi-signal mode, we need at least valid/ready in the base _signals
            msg_multi = (f'Master({title}) multi-signal model')
            msg_multi += f'{signal_map=}\n'
            msg_multi += f'{optional_signal_map=}\n'
            msg_multi += f'{field_config=}\n'

            self._signals = []

            # Add valid/ready signals from signal_map if provided
            required_signals = ['i_wr_valid', 'o_wr_ready']
            for sig_name in required_signals:
                if sig_name in self.signal_map:
                    # Map to DUT signal name
                    self._signals.append(self.signal_map[sig_name])
                else:
                    # Use default name
                    self._signals.append(sig_name)

        self._optional_signals = []
        # Add any optional signals to the optional_signals list
        if self.optional_signal_map:
            self._optional_signals.extend(
                dut_name for sig_name, dut_name in self.optional_signal_map.items()
            )
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
        if msg_multi is not None:
            self.log.debug(msg_multi)
            print_object_details(self, self.log, f"GAXI Master '{self.title}' INIT")
            print_object_details(self.bus, self.log, f"GAXI Master BUS'{self.title}' INIT")

        # Initialize queues
        self.transmit_queue = deque()
        self.sent_queue = deque()
        self.transmit_coroutine = None
        self.transfer_busy = False
        self.packet_generator = None

        # Create a mapping of field names to DUT signals for multi-signal mode
        self.field_signals = {}

        # In multi-signal mode, verify signals and store mappings
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
        """Initialize signals in multi-signal mode with fallback to defaults for optional signals."""
        # Initialize valid signal - this is always required
        if 'i_wr_valid' in self.signal_map:
            valid_signal = self.signal_map['i_wr_valid']
            if hasattr(self.bus, valid_signal):
                getattr(self.bus, valid_signal).setimmediatevalue(0)
            else:
                raise ValueError(f"Required signal '{valid_signal}' not found on DUT")
        else:
            self.bus.i_wr_valid.setimmediatevalue(0)

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
            elif field_name == 'data' and hasattr(self.bus, 'i_wr_data'):
                self.log.debug(f"Using standard data signal for field '{field_name}'")
                self.field_signals[field_name] = 'i_wr_data'
                self.bus.i_wr_data.setimmediatevalue(0)
                
            # No mapping and no standard data signal
            else:
                self.log.warning(f"No signal mapping provided for field {field_name}")

    def _register_field_signal(self, field_name, dut_signal_name, required=True):
        """Register a field signal with appropriate error handling"""
        # Verify signal exists on DUT
        if hasattr(self.bus, dut_signal_name):
            # Store the mapping
            self.field_signals[field_name] = dut_signal_name
            
            # Initialize with default value from field config
            default_value = self.field_config[field_name].get('default', 0)
            getattr(self.bus, dut_signal_name).setimmediatevalue(default_value)
            self.log.debug(f"Registered signal '{dut_signal_name}' for field '{field_name}'")
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
        self._set_wr_valid(value=0)

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

                    # If we have a mapping for this field
                    if field_name in self.field_signals:
                        dut_signal_name = self.field_signals[field_name]
                        if hasattr(self.bus, dut_signal_name):
                            getattr(self.bus, dut_signal_name).value = field_value
                        else:
                            # This warning should never happen if initialization was correct
                            self.log.warning(f"Signal {dut_signal_name} mapped but not found on DUT")
                    else:
                        self.log.debug(f"No signal mapping for field {field_name}")
            else:
                # Standard mode: drive aggregate data signal
                fifo_data = transaction.pack_for_fifo()
                if 'data' in fifo_data:
                    self.bus.i_wr_data.value = fifo_data['data']

            return True
        except Exception as e:
            self.log.error(f"Error driving signals: {e}")
            return False

    def _set_wr_valid(self, value):
        # Assert/Deassert valid
        if 'i_wr_valid' in self.signal_map:
            valid_signal = self.signal_map['i_wr_valid']
            if hasattr(self.bus, valid_signal):
                getattr(self.bus, valid_signal).value = value
        else:
            self.bus.i_wr_valid.value = value

    def _clear_data_bus(self):
        # Clear data signals during delay
        if self.use_multi_signal:
            # Reset individual field signals
            for _, dut_signal_name in self.field_signals.items():
                if hasattr(self.bus, dut_signal_name):
                    getattr(self.bus, dut_signal_name).value = 0
        else:
            # Standard mode - reset aggregate data signal
            self.bus.i_wr_data.value = 0

    async def _xmit_phase1(self):
        """First phase of transmission - delay and prepare signals"""
        # Apply any configured delay before asserting valid
        delay_dict = self.randomizer.next()
        valid_delay = delay_dict.get('valid_delay', 0)
        if valid_delay > 0:
            self.log.debug(f"Master({self.title}) Delaying valid assertion for {valid_delay} cycles")

            # Deassert wr_valid
            self._set_wr_valid(value=0)

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
        self._set_wr_valid(value=1)
        # wait a bit to keep from catching the last ready assertion
        await Timer(100, units='ps')

        # Wait for the DUT to assert ready (handshake completion)
        timeout_counter = 0
        ready_signal = self.signal_map.get('o_wr_ready', 'o_wr_ready')
        
        while not getattr(self.bus, ready_signal).value:
            await FallingEdge(self.clock)
            timeout_counter += 1
            if timeout_counter >= self.timeout_cycles:
                self.log.error(f"Master({self.title}) TIMEOUT waiting for ready after {self.timeout_cycles} cycles")

                # Stop driving if timeout (prevent hang)
                self._set_wr_valid(value=0)

                # Clear the data bus
                self._clear_data_bus()

                self.transfer_busy = False
                return False
                
        return True

    async def _xmit_phase3(self, transaction):
        """Third phase - capture handshake and prepare for next transaction"""
        # Handshake occurred – capture completion time
        await RisingEdge(self.clock)
        current_time_ns = get_sim_time('ns')
        self.log.debug(f"Master({self.title}) Transaction completed at {current_time_ns}ns: "
                        f"{transaction.formatted(compact=True)}")
        transaction.end_time = current_time_ns
        self.sent_queue.append(transaction)
        # clear wr valid
        self._set_wr_valid(value=0)
        # Clear the data bus
        self._clear_data_bus()

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
                            f"{len(self.transmit_queue)} at {transaction.start_time}ns "
                            f"transaction={transaction.formatted(compact=True)}")

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
        if 'i_wr_valid' in self.signal_map:
            valid_signal = self.signal_map['i_wr_valid']
            if hasattr(self.bus, valid_signal):
                getattr(self.bus, valid_signal).value = 0
        else:
            self.bus.i_wr_valid.value = 0

        # Clear data signals
        if self.use_multi_signal:
            # Reset field signals
            for field_name, dut_signal_name in self.field_signals.items():
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

    Supports:
    1. Single data bus (standard mode)
    2. Individual signals for each field (multi-signal mode)
    3. Optional signals with fallback behavior
    """
    def __init__(self, dut, title, prefix, clock, signals=None,
                    field_config=None, packet_class=GAXIPacket, timeout_cycles=1000,
                    randomizer=None, memory_model=None, memory_fields=None,
                    log=None, mode='skid', signal_map=None, optional_signal_map=None, **kwargs):
        # sourcery skip: low-code-quality
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
            signal_map: Dictionary mapping required GAXI signals to DUT signals
                Format: {'o_rd_valid': 'dut_valid_signal', 'i_rd_ready': 'dut_ready_signal', ...}
            optional_signal_map: Dictionary mapping optional GAXI signals to DUT signals
                These signals won't cause errors if missing from the DUT
            **kwargs: Additional arguments to pass to BusMonitor
        """
        # Validate mode parameter
        valid_modes = ['skid', 'fifo_mux', 'fifo_flop']
        if mode not in valid_modes:
            raise ValueError(f"Invalid mode '{mode}' for Slave ({title}). Mode must be one of: {', '.join(valid_modes)}")

        # Store title and log early for debug logging
        self.title = title

        # Determine if we're using multi-signal mode
        self.use_multi_signal = (signal_map is not None) or (optional_signal_map is not None)
        self.signal_map = signal_map or {}
        self.optional_signal_map = optional_signal_map or {}

        # Prepare signal lists
        msg_multi = None
        if self.use_multi_signal:
            # Multi-signal mode - only include valid/ready in _signals
            msg_multi = f'Slave({self.title}) multi-signal model\n'
            msg_multi += f'{signal_map=}\n'
            msg_multi += f'{optional_signal_map=}\n'
            msg_multi += f'{field_config=}\n'
            self._signals = []

            # Add required signals valid/ready
            required_signals = ['o_rd_valid', 'i_rd_ready']
            for sig_name in required_signals:
                if sig_name in self.signal_map:
                    # Map to DUT signal name
                    self._signals.append(self.signal_map[sig_name])
                    msg_multi += f'Adding {sig_name=} == {self.signal_map[sig_name]=}\n'
                else:
                    # Use default name
                    self._signals.append(sig_name)
                    msg_multi += f'Adding {sig_name=}\n'

        elif signals:
            self._signals = signals
        elif mode == 'fifo_mux':
            # Use multiplexed data signal in 'fifo_mux' mode
            self._signals = ['o_rd_valid', 'i_rd_ready', 'ow_rd_data']
        else:
            self._signals = gaxi_slave_signals


        # Set up optional signals
        self._optional_signals = []
        if self.optional_signal_map:
            self._optional_signals.extend(
                dut_name for _, dut_name in self.optional_signal_map.items()
            )
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
        self.log = log or self._log
        self.log.debug(f"GAXISlave init for '{title}': randomizer={randomizer}, mode={mode}")
        self.log.debug(f"GAXISlave init for '{title}': _signals={self._signals}")
        if msg_multi is not None:
            self.log.debug(msg_multi)
            print_object_details(self, self.log, f"GAXI Slave '{self.title}' INIT")
            print_object_details(self.bus, self.log, f"GAXI Slave BUS'{self.title}' INIT")


        # Create a mapping of field names to DUT signals for multi-signal mode
        self.field_signals = {}

        # In multi-signal mode, verify signals and store mappings
        if self.use_multi_signal:
            self._initialize_multi_signal_mode()

        # Initialize output signals
        if 'i_rd_ready' in self.signal_map:
            ready_signal = self.signal_map['i_rd_ready']
            if hasattr(self.bus, ready_signal):
                getattr(self.bus, ready_signal).setimmediatevalue(0)
        else:
            self.bus.i_rd_ready.setimmediatevalue(0)

        # Create received queue
        self.received_queue = deque()

        # Debug output
        if log:
            self.log.info(f"GAXISlave initialized for {self.title} in mode '{self.mode}', {'multi-signal' if self.use_multi_signal else 'standard'}")
            print_object_details(self, self.log, f"GAXI Slave '{self.title}' INIT")

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
                
            # If no mapping exists and we have a 'data' field, use standard data signal
            elif field_name == 'data':
                data_signal = None
                
                # Check mode-specific data signal
                if self.mode == 'fifo_mux' and hasattr(self.bus, 'ow_rd_data'):
                    data_signal = 'ow_rd_data'
                elif hasattr(self.bus, 'o_rd_data'):
                    data_signal = 'o_rd_data'
                    
                if data_signal:
                    self.log.debug(f"Using standard data signal '{data_signal}' for field '{field_name}'")
                    self.field_signals[field_name] = data_signal
                else:
                    self.log.warning(f"No suitable data signal found for field '{field_name}'")
            else:
                self.log.warning(f"No signal mapping provided for field {field_name}")

    def _register_field_signal(self, field_name, dut_signal_name, required=True):
        """Register a field signal with appropriate error handling"""
        # Verify signal exists on DUT
        if hasattr(self.bus, dut_signal_name):
            # Store the mapping
            self.field_signals[field_name] = dut_signal_name
            self.log.debug(f"Registered signal '{dut_signal_name}' for field '{field_name}'")
        elif required:
            # Signal is required but not found
            raise ValueError(f"Required signal '{dut_signal_name}' for field '{field_name}' not found on DUT")
        else:
            # Optional signal not found - log warning
            self.log.warning(f"Optional signal '{dut_signal_name}' for field '{field_name}' not found on DUT")

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
        if 'i_rd_ready' in self.signal_map:
            ready_signal = self.signal_map['i_rd_ready']
            if hasattr(self.bus, ready_signal):
                getattr(self.bus, ready_signal).value = 0
        else:
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
        elif data_dict and 'data' in data_dict:
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

    def _get_data_dict(self):
        # Multi-signal mode: collect data from field signals
        data_dict = {}
        for field_name, dut_signal_name in self.field_signals.items():
            if hasattr(self.bus, dut_signal_name):
                signal = getattr(self.bus, dut_signal_name)
                data_dict[field_name] = int(signal.value) if signal.value.is_resolvable else -1
        return data_dict

    def _get_data_value(self):
        data_signal = self.bus.ow_rd_data \
            if self.mode == 'fifo_mux' and hasattr(self.bus, 'ow_rd_data') \
            else self.bus.o_rd_data
        return int(data_signal.value)

    def _set_rd_ready(self, value):
        # Assert/Deassert ready
        if 'i_rd_ready' in self.signal_map:
            ready_signal = self.signal_map['i_rd_ready']
            if hasattr(self.bus, ready_signal):
                getattr(self.bus, ready_signal).value = value
        else:
            self.bus.i_rd_ready.value = value

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
            self.log.debug(f"Slave({self.title}) Delaying ready assertion for {ready_delay} cycles")
            
            # Deassert ready during delay
            self._set_rd_ready(0)
            await self.wait_cycles(ready_delay)

        # Assert ready to accept data
        self._set_rd_ready(1)

        # Wait for a falling edge to sample valid (allow combinatorial settle)
        await FallingEdge(self.clock)

    async def _recv_phase3(self, current_time):
        """Receive phase 3: Check for valid handshake and process transaction"""
        # Get valid signal
        valid_signal = 'o_rd_valid'
        if valid_signal in self.signal_map:
            valid_signal = self.signal_map[valid_signal]
            
        # Check for valid assertion
        if hasattr(self.bus, valid_signal) and getattr(self.bus, valid_signal).value == 1:
            # Create a new packet
            packet = self.packet_class(self.field_config)
            packet.start_time = current_time

            if self.mode == 'fifo_flop':
                # 'fifo_flop' mode: note handshake time, defer data capture to next cycle
                last_xfer = True
                last_packet = packet
                await RisingEdge(self.clock)
                return last_packet, last_xfer
            
            elif self.use_multi_signal:
                # Multi-signal mode: collect data from field signals
                data_dict = self._get_data_dict()
                self._finish_packet(current_time, packet, data_dict)
            else:
                # Standard mode - determine appropriate data signal based on mode
                data_val = self._get_data_value()
                self._finish_packet(current_time, packet, {'data': data_val})

        # Deassert ready on the rising edge (prepare for next cycle or delay)
        await RisingEdge(self.clock)
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

    Supports:
    1. Single data bus (standard mode)
    2. Individual signals for each field (multi-signal mode)
    3. Optional signals with fallback behavior
    """
    def __init__(self, dut, title, prefix, clock, signals=None, is_slave=False,
                    field_config=None, packet_class=GAXIPacket, timeout_cycles=1000,
                    log=None, mode='skid', signal_map=None, optional_signal_map=None, **kwargs):
        # sourcery skip: low-code-quality
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
            signal_map: Dictionary mapping required GAXI signals to DUT signals
                Format depends on is_slave parameter:
                - Slave: {'o_rd_valid': 'dut_valid', 'i_rd_ready': 'dut_ready', ...}
                - Master: {'i_wr_valid': 'dut_valid', 'o_wr_ready': 'dut_ready', ...}
            optional_signal_map: Dictionary mapping optional GAXI signals to DUT signals
                These signals won't cause errors if missing from the DUT
            **kwargs: Additional arguments to pass to BusMonitor
        """
        # Validate mode parameter
        valid_modes = ['skid', 'fifo_mux', 'fifo_flop']
        if mode not in valid_modes:
            raise ValueError(f"Invalid mode '{mode}' for Monitor ({title}). Mode must be one of: {', '.join(valid_modes)}")

        # Store title for logging
        self.title = title

        # Determine if we're using multi-signal mode
        self.use_multi_signal = (signal_map is not None) or (optional_signal_map is not None)
        self.signal_map = signal_map or {}
        self.optional_signal_map = optional_signal_map or {}
        self.is_slave = is_slave

        # Prepare signal lists
        msg_multi = None
        if self.use_multi_signal:
            # Multi-signal mode - only include valid/ready in _signals
            msg_multi = f'Monitor({self.title}) multi-signal model'
            self._signals = []

            # Add valid/ready signals based on slave/master orientation
            required_signals = ['o_rd_valid', 'i_rd_ready'] if is_slave else ['i_wr_valid', 'o_wr_ready']
            for sig_name in required_signals:
                if sig_name in self.signal_map:
                    # Map to DUT signal name
                    self._signals.append(self.signal_map[sig_name])
                else:
                    # Use default name
                    self._signals.append(sig_name)

        elif signals:
            self._signals = signals
        elif is_slave and mode == 'fifo_mux':
            # In mux mode (slave side), use multiplexed read data signal
            self._signals = ['o_rd_valid', 'i_rd_ready', 'ow_rd_data']
        else:
            # Use default signals based on orientation
            self._signals = ['o_rd_valid', 'i_rd_ready', 'o_rd_data'] if is_slave else ['i_wr_valid', 'o_wr_ready', 'i_wr_data']

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
        if msg_multi is not None:
            self.log.debug(msg_multi)
    
        # Set up instance attributes
        self.log = log or self._log
        self.clock = clock
        self.timeout_cycles = timeout_cycles
        self.field_config = field_config or {
            'data': {'bits': 32, 'default': 0, 'format': 'hex', 'display_width': 8}
        }
        self.packet_class = packet_class
        self.mode = mode

        # Initialize queue for observed transactions
        self.observed_queue = deque()

        # Create a mapping of field names to DUT signals for multi-signal mode
        self.field_signals = {}

        if self.use_multi_signal:
            self._initialize_multi_signal_mode()
        else:
            # Map standard bus signals to internal references for easy access
            self._setup_standard_signals()

        # Debug output
        if log:
            self.log.info(f"GAXIMonitor initialized for {title} (mode: {mode}, {'multi-signal' if self.use_multi_signal else 'standard'})")
            print_object_details(self, self.log, f"GAXI Monitor '{self.title}' INIT")
            print_object_details(self.field_config, self.log, f"GAXI Monitor Field Config'{self.title}' INIT")
            print_object_details(self.field_signals, self.log, f"GAXI Monitor Field Signals'{self.title}' INIT")


    def _initialize_multi_signal_mode(self):
        """Initialize signal mappings for multi-signal mode with fallback to standard signals."""
        # Set up valid/ready signal references
        if self.is_slave:
            # Slave-side monitor - find valid/ready signals
            valid_signal_name = self.signal_map.get('o_rd_valid', 'o_rd_valid')
            ready_signal_name = self.signal_map.get('i_rd_ready', 'i_rd_ready')
            data_prefix = 'o_rd_data_'
        else:
            # Master-side monitor - find valid/ready signals
            valid_signal_name = self.signal_map.get('i_wr_valid', 'i_wr_valid')
            ready_signal_name = self.signal_map.get('o_wr_ready', 'o_wr_ready')
            data_prefix = 'i_wr_data_'

        # Map valid/ready signals - these must be present
        if hasattr(self.bus, valid_signal_name):
            self.valid_signal = getattr(self.bus, valid_signal_name)
        else:
            raise ValueError(f"Required valid signal '{valid_signal_name}' not found on DUT")

        if hasattr(self.bus, ready_signal_name):
            self.ready_signal = getattr(self.bus, ready_signal_name)
        else:
            raise ValueError(f"Required ready signal '{ready_signal_name}' not found on DUT")

        # Map field signals
        for field_name in self.field_config.keys():

            # Create the signal name for this field
            field_signal_name = f'{data_prefix}{field_name}'

            # Check required signal map first
            if field_signal_name in self.signal_map:
                dut_signal_name = self.signal_map[field_signal_name]
                self._register_field_signal(field_name, dut_signal_name, required=True)

            elif field_signal_name in self.optional_signal_map:
                dut_signal_name = self.optional_signal_map[field_signal_name]
                self._register_field_signal(field_name, dut_signal_name, required=False)

            elif field_name == 'data':
                # Find appropriate standard data signal
                data_signal = None
                if self.is_slave:
                    if self.mode == 'fifo_mux' and hasattr(self.bus, 'ow_rd_data'):
                        data_signal = 'ow_rd_data'
                    elif hasattr(self.bus, 'o_rd_data'):
                        data_signal = 'o_rd_data'
                elif hasattr(self.bus, 'i_wr_data'):
                    data_signal = 'i_wr_data'

                if data_signal:
                    self.log.debug(f"Using standard data signal '{data_signal}' for field '{field_name}'")
                    self.field_signals[field_name] = data_signal
                    # Store for easy access
                    self.data_signal = getattr(self.bus, data_signal)
                else:
                    self.log.warning(f"No suitable data signal found for field '{field_name}'")
            else:
                self.log.warning(f"No signal mapping provided for field {field_name}")

    def _register_field_signal(self, field_name, dut_signal_name, required=True):
        """Register a field signal with appropriate error handling"""
        # Verify signal exists on DUT
        if hasattr(self.bus, dut_signal_name):
            # Store the mapping
            self.field_signals[field_name] = dut_signal_name
            self.log.debug(f"Registered signal '{dut_signal_name}' for field '{field_name}'")
            
            # Store standard data signal for easy access
            if field_name == 'data':
                self.data_signal = getattr(self.bus, dut_signal_name)
        elif required:
            # Signal is required but not found
            raise ValueError(f"Required signal '{dut_signal_name}' for field '{field_name}' not found on DUT")
        else:
            # Optional signal not found - log warning
            self.log.warning(f"Optional signal '{dut_signal_name}' for field '{field_name}' not found on DUT")

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
        elif data_dict and 'data' in data_dict:
            fifo_data = {'data': data_dict['data']}
            packet.unpack_from_fifo(fifo_data)

        # Record completion time and store packet
        packet.end_time = current_time
        self.observed_queue.append(packet)
        self.log.debug(f"Monitor({self.title}) Transaction received at {packet.end_time}ns: {packet.formatted(compact=True)}")
        self._recv(packet)  # trigger callbacks

    def _get_data_dict(self):
        """
        Collect data from field signals and properly handle X/Z values.
        
        Returns:
            Dictionary of field values with X/Z values represented as -1
        """
        print_dict_to_log(f"GAXI Monitor Field Siggnals({self.title}), recv_phase2:", self.field_signals, self.log, "field_signals")
        data_dict = {}
        for field_name, dut_signal_name in self.field_signals.items():
            if hasattr(self.bus, dut_signal_name):
                signal = getattr(self.bus, dut_signal_name)

                # Log the actual signal value and its resolvability
                self.log.debug(f"Signal {dut_signal_name} value: {signal.value}, resolvable: {signal.value.is_resolvable}")

                # Check if signal has a valid value
                if signal.value.is_resolvable:
                    data_dict[field_name] = int(signal.value)
                else:
                    # Signal is X or Z, represent it as -1
                    self.log.warning(f"Field {field_name} has X/Z value")
                    data_dict[field_name] = -1
            else:
                # Signal not found - could be optional or missing
                self.log.debug(f"Signal {dut_signal_name} not found on DUT")
        
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
                if self.data_signal.value.is_resolvable:
                    data_val = int(self.data_signal.value)
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
        if (not self.valid_signal.value.is_resolvable or
                not self.ready_signal.value.is_resolvable or
                self.valid_signal.value.integer != 1 or
                self.ready_signal.value.integer != 1):
            return last_packet, last_xfer

        # Create a new packet
        packet = self.packet_class(self.field_config)
        print_dict_to_log(f"GAXI Monitor Packet Field Config({self.title}), recv_phase2:", packet.field_config, self.log, "field_config")
        print_dict_to_log(f"GAXI Monitor Packet Fields({self.title}), recv_phase2:", packet.fields, self.log, "fields")

        packet.start_time = current_time

        if self.mode == 'fifo_flop':
            # 'fifo_flop' mode: note handshake time, defer data capture to next cycle
            last_xfer = True
            last_packet = packet
        elif self.use_multi_signal:
            # Multi-signal mode: collect data from field signals

            data_dict = self._get_data_dict()
            self._finish_packet(current_time, packet, data_dict)
        else:
            # Standard mode - check if data signal is X/Z
            if self.data_signal.value.is_resolvable:
                data_val = int(self.data_signal.value)
            else:
                self.log.warning("Data signal has X/Z value")
                data_val = -1  # Represent X/Z as -1
            
            self._finish_packet(current_time, packet, {'data': data_val})

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
            self.log.error(f"Exception in _monitor_recv: {str(e)}")
            import traceback
            self.log.error(traceback.format_exc())
            raise
