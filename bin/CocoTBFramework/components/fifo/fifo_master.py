"""
FIFO Master - Combines exact working cocotb methods with modern infrastructure
"""

import cocotb
from collections import deque
from cocotb_bus.drivers import BusDriver
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from ..field_config import FieldConfig
from ..signal_mapping_helper import SignalResolver
from ..data_strategies import DataDrivingStrategy
from ..master_statistics import MasterStatistics
from ..flex_randomizer import FlexRandomizer
from .fifo_packet import FIFOPacket


# Default constraints - keeping from original working code
fifo_master_default_constraints = {
    'write_delay': ([(0, 0), (1, 8), (9, 20)], [5, 2, 1])
}


class FIFOMaster(BusDriver):
    """
    FIFO Master combining exact working cocotb methods with modern infrastructure.

    Preserves all timing-critical cocotb methods while adding:
    - Automatic signal resolution via SignalResolver
    - High-performance data driving via DataDrivingStrategy
    - Comprehensive statistics via MasterStatistics
    - Flexible randomization via FlexRandomizer
    """

    def __init__(self, dut, title, prefix, clock, field_config,
                    timeout_cycles=1000, mode='fifo_mux',
                    in_prefix='i_',
                    out_prefix='o_',
                    bus_name='',
                    pkt_prefix='',
                    multi_sig=False,
                    randomizer=None, log=None, super_debug=False, **kwargs):
        """
        Initialize FIFO Master with modern infrastructure.
        """
        # Core attributes - keeping original working setup
        self.title = title
        self.clock = clock
        self.tick_delay = 100
        self.tick_units = 'ps'
        self.timeout_cycles = timeout_cycles
        self.reset_occurring = False
        self.mode = mode

        # set the naming convention params
        self.in_prefix = in_prefix
        self.out_prefix = out_prefix
        self.bus_name = bus_name
        self.pkt_prefix = pkt_prefix
        self.use_multi_signal = multi_sig

        # Handle field_config - convert dict if needed
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        else:
            self.field_config = field_config or FieldConfig.create_data_only()

        # Modern infrastructure - signal resolution
        self.signal_resolver = SignalResolver(
            protocol_type='fifo_master',
            dut=dut,
            bus=None,  # Set after BusDriver init
            log=log,
            component_name=title,
            field_config=self.field_config,
            multi_sig=self.use_multi_signal,
            in_prefix=self.in_prefix,
            out_prefix=self.out_prefix,
            bus_name=self.bus_name,
            pkt_prefix=self.pkt_prefix,
            mode=mode,
            super_debug=super_debug
        )

        # Get signal lists for BusDriver - ESSENTIAL FOR COCOTB
        self._signals, self._optional_signals = self.signal_resolver.get_signal_lists()

        # Initialize parent BusDriver - MUST BE CALLED WITH EXACT PATTERN
        BusDriver.__init__(self, dut, prefix, clock, **kwargs)
        self.log = log or self._log

        # Apply modern signal mappings after bus is created
        self.signal_resolver.bus = self.bus
        self.signal_resolver.apply_to_component(self)

        # Modern infrastructure - data driving strategy
        self.data_driver = DataDrivingStrategy(
            component=self,
            field_config=self.field_config,
            use_multi_signal=self.use_multi_signal,
            log=self.log
        )

        # Modern infrastructure - statistics
        self.stats = MasterStatistics()

        # Set up randomizer - keeping original default constraints
        if randomizer is None:
            self.randomizer = FlexRandomizer(fifo_master_default_constraints)
        else:
            self.randomizer = randomizer

        # EXACT WORKING COCOTB PATTERN - DO NOT MODIFY
        self.transmit_queue = deque()
        self.sent_queue = deque()
        self.transmit_coroutine = None
        self.transfer_busy = False

        # Initialize signals safely without async
        self._initialize_signals()

        self.log.info(f"FIFOMaster '{title}' initialized: mode={mode}, "
                        f"multi_sig={self.use_multi_signal}")

    def _initialize_signals(self):
        """Initialize signals to safe values - NO ASYNC"""
        try:
            # Initialize write signal using modern signal resolver
            if hasattr(self, 'write_sig') and self.write_sig is not None:
                self.write_sig.setimmediatevalue(0)

            # Clear data signals using modern data driver
            self.data_driver.clear_signals()

        except Exception as e:
            self.log.error(f"FIFOMaster '{self.title}': Error initializing signals: {e}")

    def set_randomizer(self, randomizer):
        """Set randomizer - modern interface"""
        self.randomizer = randomizer
        self.log.info(f"Set new randomizer for Master({self.title})")

    async def reset_bus(self):
        """Reset bus - EXACT WORKING PATTERN FROM ORIGINAL"""
        self.log.debug(f"Master({self.title}): resetting the bus")

        # Reset write signal
        self._assign_write_value(value=0)

        # Reset field signals using modern data driver
        self.data_driver.clear_signals()

        self.reset_occurring = True
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        self.reset_occurring = False

        # Clear queues - EXACT WORKING PATTERN
        self.transmit_queue = deque()
        self.sent_queue = deque()
        self.transmit_coroutine = None
        self.transfer_busy = False

    async def _driver_send(self, transaction, sync=True, hold=False, **kwargs):
        """
        EXACT WORKING COCOTB DRIVER METHOD - DO NOT MODIFY TIMING/LOGIC
        Only replace infrastructure calls (signal mapping, data driving, stats)
        """
        # Add transaction to queue - EXACT WORKING PATTERN
        self.transmit_queue.append(transaction)

        # Start transmission pipeline if not already running - EXACT WORKING PATTERN
        if not hold and not self.transmit_coroutine:
            self.log.debug(f'Master({self.title}): Starting new transmit pipeline, queue length: {len(self.transmit_queue)}')
            self.transmit_coroutine = cocotb.start_soon(self._transmit_pipeline())

    def _drive_signals(self, transaction):
        """
        Drive signals using modern data driving strategy.
        REPLACES original _drive_signals logic but keeps exact interface.
        """
        try:
            # Use modern data driving strategy instead of manual signal driving
            return self.data_driver.drive_transaction(transaction)
        except Exception as e:
            self.log.error(f"Error driving signals: {e}")
            return False

    def _assign_write_value(self, value):
        """Set write signal - EXACT WORKING PATTERN"""
        if hasattr(self, 'write_sig') and self.write_sig is not None:
            self.write_sig.value = value

    def _clear_data_bus(self):
        """Clear data signals - MODERNIZED"""
        self.data_driver.clear_signals()

    async def _xmit_phase1(self):
        """Phase 1: Apply delay - EXACT WORKING TIMING"""
        # Apply any configured delay before asserting write - EXACT WORKING PATTERN
        delay_dict = self.randomizer.next()
        write_delay = delay_dict.get('write_delay', 0)
        if write_delay > 0:
            # Deassert write
            self._assign_write_value(value=0)
            # Clear the data bus
            self._clear_data_bus()
            # write delay - EXACT WORKING TIMING
            await self.wait_cycles(write_delay)

    async def _xmit_phase2(self, transaction):
        """Phase 2: Drive signals and wait for not full - EXACT WORKING LOGIC"""
        # Drive signals for this transaction - MODERNIZED CALL
        if not self._drive_signals(transaction):
            self.log.error(f"Failed to drive signals for transaction: {transaction.formatted()}")
            self.transfer_busy = False
            return False

        # Wait for FIFO to not be full - EXACT WORKING PATTERN
        timeout_counter = 0

        # Check if full signal is high
        while hasattr(self, 'full_sig') and self.full_sig is not None and self.full_sig.value:
            await self.wait_cycles(1)

            # Keep write deasserted while full
            self._assign_write_value(value=0)

            # Update stats - MODERNIZED
            self.stats.record_flow_control_stall(1)

            timeout_counter += 1
            if timeout_counter >= self.timeout_cycles:
                self.log.error(f"Master({self.title}) TIMEOUT waiting for FIFO not full after {self.timeout_cycles} cycles")

                # Stop driving if timeout (prevent hang)
                self._assign_write_value(value=0)
                self._clear_data_bus()

                # Update stats - MODERNIZED
                self.stats.record_timeout()

                self.transfer_busy = False
                return False

        # Assert write for this transaction since FIFO is not full
        self._assign_write_value(value=1)

        # Check for write while full error - EXACT WORKING PATTERN
        if (hasattr(self, 'full_sig') and self.full_sig is not None and
            hasattr(self, 'write_sig') and self.write_sig is not None and
            self.full_sig.value and self.write_sig.value):
            current_time_ns = get_sim_time('ns')
            self.log.error(f"Master({self.title}) Error: {self.title} write while fifo full at {current_time_ns}ns")
            # Update stats - MODERNIZED
            self.stats.record_protocol_violation("write_while_full")

        # Wait a cycle for the write to take effect - EXACT WORKING TIMING
        await self.wait_cycles(1)

        return True

    async def _xmit_phase3(self, transaction):
        """Phase 3: Complete transfer - EXACT WORKING PATTERN"""
        # Write has been completed – capture completion time
        current_time_ns = get_sim_time('ns')
        self.log.debug(f"Master({self.title}) Transaction completed at {current_time_ns}ns: "
                        f"{transaction.formatted(compact=True)}")
        transaction.end_time = current_time_ns
        self.sent_queue.append(transaction)

        # Update stats - MODERNIZED
        bytes_transferred = self._calculate_bytes_transferred(transaction)
        # Note: start_time tracking handled in send() method

        # Deassert write
        self._assign_write_value(value=0)

        # Clear the data bus
        self._clear_data_bus()

    async def _transmit_pipeline(self):
        """
        EXACT WORKING TRANSMISSION PIPELINE - DO NOT MODIFY TIMING
        Only modernize infrastructure calls
        """
        self.log.debug(f'Master({self.title}): Transmit pipeline started, queue length: {len(self.transmit_queue)}')
        self.transfer_busy = True
        await self.wait_cycles(1)

        while len(self.transmit_queue):
            # Get next transaction from the queue
            transaction = self.transmit_queue.popleft()
            transaction.start_time = get_sim_time('ns')

            # Record transaction start - MODERNIZED
            start_time = self.stats.record_transaction_start()

            # xmit phase 1 - apply delay
            await self._xmit_phase1()

            # xmit phase 2 - drive signals and check if FIFO is full
            if not await self._xmit_phase2(transaction):
                # Error occurred in phase 2
                self.stats.record_transaction_failed("xmit_phase2_error", "Phase 2 failed")
                continue

            # xmit phase 3 - handle transfer completion
            await self._xmit_phase3(transaction)

            # Complete stats recording - MODERNIZED
            bytes_transferred = self._calculate_bytes_transferred(transaction)
            self.stats.record_transaction_complete(start_time, bytes_transferred)

        self.log.debug(f"Master({self.title}) Transmit pipeline completed")
        self.transfer_busy = False
        self.transmit_coroutine = None

        # Ensure signals are deasserted at the end - EXACT WORKING PATTERN
        self._assign_write_value(value=0)
        self._clear_data_bus()

    async def wait_cycles(self, cycles):
        """EXACT WORKING WAIT METHOD - DO NOT MODIFY"""
        for _ in range(cycles):
            await RisingEdge(self.clock)
            await Timer(200, units='ps')
            if self.reset_occurring:
                break

    def _calculate_bytes_transferred(self, packet):
        """Calculate bytes for statistics - MODERNIZED"""
        total_bits = packet.get_total_bits()
        return (total_bits + 7) // 8

    # Modern convenience methods
    async def send(self, packet):
        """Modern send interface"""
        await self._driver_send(packet, sync=True)
        # Wait for completion
        while self.transmit_coroutine is not None:
            await RisingEdge(self.clock)
        return True

    def create_packet(self, **field_values):
        """Create a packet with specified field values"""
        packet = FIFOPacket(self.field_config)
        for field_name, value in field_values.items():
            if hasattr(packet, field_name):
                setattr(packet, field_name, value)
        return packet

    def get_stats(self):
        """Get comprehensive statistics - MODERNIZED"""
        return {
            'master_stats': self.stats.get_stats(),
            'data_driver_stats': self.data_driver.get_stats(),
            'signal_resolver_stats': self.signal_resolver.get_stats(),
            'transfer_busy': self.transfer_busy,
            'queue_depth': len(self.transmit_queue)
        }

    def __str__(self):
        """String representation"""
        return f"FIFOMaster '{self.title}': {self.stats}"
