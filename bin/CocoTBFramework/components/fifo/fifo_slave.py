"""
FIFO Slave - Combines exact working cocotb methods with modern infrastructure
"""

import cocotb
from collections import deque
from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time

from ..field_config import FieldConfig
from ..signal_mapping_helper import SignalResolver
from ..data_strategies import DataCollectionStrategy
from ..master_statistics import SlaveStatistics
from ..flex_randomizer import FlexRandomizer
from .fifo_packet import FIFOPacket


# Default constraints - keeping from original working code
fifo_slave_default_constraints = {
    'read_delay': ([(0, 1), (2, 8), (9, 30)], [5, 2, 1])
}


class FIFOSlave(BusMonitor):
    """
    FIFO Slave combining exact working cocotb methods with modern infrastructure.

    Preserves all timing-critical cocotb methods while adding:
    - Automatic signal resolution via SignalResolver
    - High-performance data collection via DataCollectionStrategy
    - Comprehensive statistics via SlaveStatistics
    - Standard cocotb _recvQ pattern (no auto-read)
    """

    def __init__(self, dut, title, prefix, clock, field_config,
                    timeout_cycles=1000, mode='fifo_mux', bus_name='', pkt_prefix='',
                    randomizer=None, log=None, super_debug=False, **kwargs):
        """
        Initialize FIFO Slave with modern infrastructure.
        """
        # Core attributes - keeping original working setup
        self.title = title
        self.clock = clock
        self.tick_delay = 100
        self.tick_units = 'ps'
        self.timeout_cycles = timeout_cycles
        self.reset_occurring = False
        self.mode = mode

        # Handle field_config - convert dict if needed
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        else:
            self.field_config = field_config or FieldConfig.create_data_only()

        # Multi-signal mode detection
        self.use_multi_signal = len(self.field_config) > 1
        self.field_mode = self.use_multi_signal

        # Modern infrastructure - signal resolution
        self.signal_resolver = SignalResolver(
            protocol_type='fifo_slave',
            dut=dut,
            bus=None,  # Set after BusMonitor init
            log=log,
            component_name=title,
            field_config=self.field_config,
            multi_sig=self.use_multi_signal,
            in_prefix='i_',
            out_prefix='o_',
            bus_name=bus_name,
            pkt_prefix=pkt_prefix,
            mode=mode,
            super_debug=super_debug
        )

        # Get signal lists for BusMonitor - ESSENTIAL FOR COCOTB
        self._signals, self._optional_signals = self.signal_resolver.get_signal_lists()

        # Initialize parent BusMonitor - MUST BE CALLED WITH EXACT PATTERN
        BusMonitor.__init__(self, dut, prefix, clock, callback=None, event=None, **kwargs)
        self.log = log or self._log

        # Apply modern signal mappings after bus is created
        self.signal_resolver.bus = self.bus
        self.signal_resolver.apply_to_component(self)

        # Modern infrastructure - data collection strategy
        self.data_collector = DataCollectionStrategy(
            component=self,
            field_config=self.field_config,
            use_multi_signal=self.use_multi_signal,
            log=self.log
        )

        # Modern infrastructure - statistics
        # Note: BusMonitor parent class has its own self.stats (MonitorStatistics)
        # We'll keep the inherited stats and add our own enhanced stats
        self.enhanced_stats = SlaveStatistics()

        # Set up randomizer - keeping original default constraints
        if randomizer is None:
            self.randomizer = FlexRandomizer(fifo_slave_default_constraints)
        else:
            self.randomizer = randomizer

        # EXACT WORKING COCOTB PATTERN - inherit _recvQ from BusMonitor
        # DO NOT ADD: self.received_queue = deque()  # This would break cocotb pattern
        self.callbacks = []

        # Initialize signals safely without async
        self._initialize_signals()

        self.log.info(f"FIFOSlave '{title}' initialized: mode={mode}, "
                        f"multi_sig={self.use_multi_signal}")

    def _initialize_signals(self):
        """Initialize signals to safe values - NO ASYNC"""
        try:
            # Initialize read signal using modern signal resolver
            if hasattr(self, 'read_sig') and self.read_sig is not None:
                self.read_sig.setimmediatevalue(0)

        except Exception as e:
            self.log.error(f"FIFOSlave '{self.title}': Error initializing signals: {e}")

    def set_randomizer(self, randomizer):
        """Set randomizer - modern interface"""
        self.randomizer = randomizer
        self.log.info(f"FIFOSlave({self.title}) Set new randomizer for {self.title}")

    async def reset_bus(self):
        """Reset bus - EXACT WORKING PATTERN FROM ORIGINAL"""
        self.log.debug(f"FIFOSlave({self.title}): resetting the bus")
        self.reset_occurring = True
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        self.reset_occurring = False

        # Deassert read signal
        self._set_rd_ready(0)

        # Clear any queued transactions - EXACT WORKING PATTERN
        # Note: Use inherited _recvQ from BusMonitor, not custom queue
        self._recvQ.clear()

    def _get_data_dict(self):
        """
        MODERNIZED: Use DataCollectionStrategy instead of manual signal collection
        """
        return self.data_collector.collect_data()

    def _set_rd_ready(self, value):
        """Set read signal - EXACT WORKING PATTERN"""
        if hasattr(self, 'read_sig') and self.read_sig is not None:
            self.read_sig.value = value

    def _finish_packet(self, current_time, packet, data_dict=None):
        """
        EXACT WORKING PACKET FINISHING LOGIC - only modernize infrastructure calls
        """
        # Check if we need to unpack fields from a combined value - EXACT WORKING LOGIC
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
                    if hasattr(packet, field_name):
                        setattr(packet, field_name, value)

        # Record completion time - EXACT WORKING PATTERN
        packet.end_time = current_time

        # Update stats - MODERNIZED
        self.enhanced_stats.record_transaction_processed(get_sim_time('ns'))

        # Log packet
        packet_str = packet.formatted(compact=True) if hasattr(packet, 'formatted') else str(packet)
        self.log.debug(f"FIFOSlave({self.title}) Transaction received at {packet.end_time}ns: {packet_str}")

        # ESSENTIAL: Use cocotb _recv method to add to _recvQ and trigger callbacks
        self._recv(packet)

    def _finish_packet_helper(self, combined_value, unpacked_fields):
        """EXACT WORKING HELPER - DO NOT MODIFY"""
        bit_offset = 0
        # Process fields in the order defined in field_config
        for field_name in self.field_config.field_names():
            # Get field definition from FieldConfig
            field_def = self.field_config.get_field(field_name)
            field_width = field_def.bits
            mask = (1 << field_width) - 1

            # Extract field value using mask and shift
            field_value = (combined_value >> bit_offset) & mask

            unpacked_fields[field_name] = field_value
            bit_offset += field_width

        return unpacked_fields

    async def _recv_phase1(self, last_packet, last_xfer):
        """EXACT WORKING PHASE 1 - only modernize data collection call"""
        # Wait a brief moment for signal stability
        await Timer(200, units='ps')

        current_time = get_sim_time('ns')

        # Check if last transfer is pending (fifo_flop mode)
        if last_xfer:
            packet = last_packet

            # MODERNIZED: Use data collection strategy
            data_dict = self._get_data_dict()
            self._finish_packet(current_time, packet, data_dict)

        return current_time

    async def _recv_phase2(self):
        """EXACT WORKING PHASE 2 - DO NOT MODIFY TIMING"""
        # Check if FIFO is empty
        if hasattr(self, 'empty_sig') and self.empty_sig is not None and self.empty_sig.value:
            # FIFO is empty, keep read deasserted and update stats
            self._set_rd_ready(0)
            # MODERNIZED stats update
            # Note: empty_cycles tracking moved to modern stats
            return

        # Check if valid on this cycle, if so we can't drop read
        if not (not self.empty_sig.value.is_resolvable or
                not self.read_sig.value.is_resolvable or
                self.empty_sig.value.integer != 0 or
                self.read_sig.value.integer != 1):
            # Previous read in progress, no delay
            return

        # Determine read delay for this cycle - MODERNIZED randomizer call
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
        """EXACT WORKING PHASE 3 - only modernize data collection and stats"""
        # Check if reading and FIFO is not empty (valid read)
        if (hasattr(self, 'read_sig') and self.read_sig is not None and
            hasattr(self, 'empty_sig') and self.empty_sig is not None and
            self.read_sig.value.is_resolvable and
            self.empty_sig.value.is_resolvable and
            self.read_sig.value.integer == 1 and
            self.empty_sig.value.integer == 0):

            # Create a new packet
            packet = FIFOPacket(self.field_config)
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
                # MODERNIZED: Use data collection strategy
                data_dict = self._get_data_dict()
                self._finish_packet(current_time, packet, data_dict)

        elif (hasattr(self, 'read_sig') and self.read_sig is not None and
                hasattr(self, 'empty_sig') and self.empty_sig is not None and
                self.read_sig.value.is_resolvable and
                self.empty_sig.value.is_resolvable and
                self.read_sig.value.integer == 1 and
                self.empty_sig.value.integer == 1):
            # Attempting to read while empty - MODERNIZED stats
            self.enhanced_stats.record_transaction_rejected("read_while_empty")
            self.log.warning(f"FIFOSlave({self.title}) Read while empty detected at {current_time}ns")

        # Deassert read on the rising edge (prepare for next cycle or delay)
        await RisingEdge(self.clock)
        await Timer(self.tick_delay, units=self.tick_units)
        self._set_rd_ready(0)

        # Default return values
        return None, False

    async def _monitor_recv(self):
        """
        EXACT WORKING MONITOR RECV - DO NOT MODIFY TIMING/LOGIC
        This is the core cocotb method that MUST work exactly as debugged
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
        """EXACT WORKING WAIT METHOD - DO NOT MODIFY"""
        for _ in range(cycles):
            await RisingEdge(self.clock)
            if self.reset_occurring:
                break

        await Timer(self.tick_delay, units=self.tick_units)

    # Modern convenience methods
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
            'slave_stats': self.enhanced_stats.get_stats(),
            'data_collector_stats': self.data_collector.get_stats(),
            'signal_resolver_stats': self.signal_resolver.get_stats(),
            'queue_depth': len(self._recvQ)  # Use standard cocotb _recvQ
        }

    def __str__(self):
        """String representation"""
        return f"FIFOSlave '{self.title}': {self.enhanced_stats}"
