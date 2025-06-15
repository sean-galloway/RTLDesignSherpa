"""
Updated GAXISlave - Clean implementation using unified GAXIMonitorBase

Preserves exact timing-critical cocotb methods and external API while
eliminating code duplication through inheritance. Combines monitoring
capabilities with active ready signal driving.

All existing parameters are preserved and used exactly as before.
"""

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time

from .gaxi_monitor_base import GAXIMonitorBase
from ..monitor_statistics import MonitorStatistics
from .gaxi_packet import GAXIPacket


class GAXISlave(GAXIMonitorBase):
    """
    GAXI Slave - Clean implementation using unified base functionality.

    Inherits all common functionality from GAXIMonitorBase:
    - Signal resolution and data collection setup
    - Clean _get_data_dict() with automatic field unpacking
    - Unified _finish_packet() without conditional mess
    - Packet creation and statistics
    - Memory model integration using base MemoryModel directly

    Adds slave-specific functionality:
    - Active ready signal driving (_set_ready)
    - Phase-based receive logic with delays
    - Ready timing control with randomization
    - SlaveStatistics for performance tracking
    """

    def __init__(self, dut, title, prefix, clock, field_config,
                    timeout_cycles=1000, mode='skid',
                    in_prefix='i_',
                    out_prefix='o_',
                    bus_name='',
                    pkt_prefix='',
                    multi_sig=False,
                    randomizer=None, memory_model=None, log=None, super_debug=False, **kwargs):
        """
        Initialize GAXI Slave - EXACT SAME API AS BEFORE.

        Args:
            dut: Device under test
            title: Component title/name
            prefix: Bus prefix
            clock: Clock signal
            field_config: Field configuration
            timeout_cycles: Timeout for operations
            mode: GAXI mode ('skid', 'fifo_mux', 'fifo_flop')
            in_prefix: Input signal prefix
            out_prefix: Output signal prefix
            bus_name: Bus/channel name
            pkt_prefix: Packet field prefix
            multi_sig: Whether using multi-signal mode
            randomizer: Optional randomizer for ready delays
            memory_model: Optional memory model for transactions
            log: Logger instance
            super_debug: Enable detailed debugging
            **kwargs: Additional arguments
        """
        # Initialize base class with slave protocol type
        super().__init__(
            dut=dut,
            title=title,
            prefix=prefix,
            clock=clock,
            field_config=field_config,
            mode=mode,
            in_prefix=in_prefix,
            out_prefix=out_prefix,
            bus_name=bus_name,
            pkt_prefix=pkt_prefix,
            multi_sig=multi_sig,
            protocol_type='gaxi_slave',  # Slave monitors slave side
            memory_model=memory_model,
            randomizer=randomizer,
            log=log,
            super_debug=super_debug,
            **kwargs
        )

        # Slave-specific attributes
        self.tick_delay = 100
        self.tick_units = 'ps'
        self.timeout_cycles = timeout_cycles
        self.reset_occurring = False

        # Override statistics with monitor statistics (same as before)
        self.stats = MonitorStatistics()

        # Slave-specific initialization - callbacks for compatibility
        self.callbacks = []

        # Initialize signals safely without async
        self._initialize_signals()

        self.log.info(f"GAXISlave '{title}' initialized: mode={mode}, "
                        f"multi_sig={self.use_multi_signal}")

    def _initialize_signals(self):
        """Initialize signals to safe values - NO ASYNC"""
        try:
            # Initialize ready signal using inherited signal resolver
            if hasattr(self, 'ready_sig') and self.ready_sig is not None:
                self.ready_sig.setimmediatevalue(0)

        except Exception as e:
            self.log.error(f"GAXISlave '{self.title}': Error initializing signals: {e}")

    async def reset_bus(self):
        """Reset bus - EXACT WORKING PATTERN FROM ORIGINAL"""
        self.log.debug(f"GAXISlave({self.title}): resetting the bus")
        self.reset_occurring = True
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        self.reset_occurring = False

        # Deassert ready signal
        self._set_ready(0)

        # Clear any queued transactions - EXACT WORKING PATTERN
        # Note: Use inherited _recvQ from BusMonitor, not custom queue
        self._recvQ.clear()

    def _set_ready(self, value):
        """Set ready signal - EXACT WORKING PATTERN"""
        if hasattr(self, 'ready_sig') and self.ready_sig is not None:
            self.ready_sig.value = value

    async def _recv_phase1(self, last_packet, last_xfer):
        """EXACT WORKING PHASE 1 - uses inherited clean _get_data_dict()"""
        # Wait a brief moment for signal stability
        await Timer(200, units='ps')

        current_time = get_sim_time('ns')

        # Check if last transfer is pending (fifo_flop mode)
        if last_xfer:
            packet = last_packet

            # CLEAN: Use inherited _get_data_dict() - no conditional mess!
            data_dict = self._get_data_dict()
            # CLEAN: Use inherited _finish_packet() - unified implementation!
            self._finish_packet(current_time, packet, data_dict)

        return current_time

    async def _recv_phase2(self):
        """EXACT WORKING PHASE 2 - DO NOT MODIFY TIMING"""
        # Check if valid on this cycle, if so we can't drop ready
        if not (hasattr(self, 'valid_sig') and self.valid_sig is not None and
                hasattr(self, 'ready_sig') and self.ready_sig is not None and
                self.valid_sig.value.is_resolvable and
                self.ready_sig.value.is_resolvable and
                self.valid_sig.value.integer == 1 and
                self.ready_sig.value.integer == 1):

            # Wait for valid to assert to decide to delay the ready
            if (hasattr(self, 'valid_sig') and self.valid_sig is not None and
                self.valid_sig.value.is_resolvable):
                while self.valid_sig.value.integer == 0:
                    await self.wait_cycles(1)

            # Determine ready delay for this cycle - using inherited randomizer
            delay_cfg = self.randomizer.next()
            ready_delay = delay_cfg.get('ready_delay', 0)
            if ready_delay > 0:
                # Deassert ready during delay
                self._set_ready(0)
                await self.wait_cycles(ready_delay)

        # Assert ready to accept data
        self._set_ready(1)

        # Wait for a falling edge to sample signals
        await FallingEdge(self.clock)

    async def _recv_phase3(self, current_time):
        """EXACT WORKING PHASE 3 - uses inherited clean data collection and stats"""
        # Check for valid handshake (valid=1 and ready=1)
        if (hasattr(self, 'valid_sig') and self.valid_sig is not None and
            hasattr(self, 'ready_sig') and self.ready_sig is not None and
            self.valid_sig.value.is_resolvable and
            self.ready_sig.value.is_resolvable and
            self.valid_sig.value.integer == 1 and
            self.ready_sig.value.integer == 1):

            # Create a new packet
            packet = GAXIPacket(self.field_config)
            packet.start_time = current_time

            # Record transaction received (using MonitorStatistics interface)
            received_time = get_sim_time('ns')  # For logging purposes

            if self.mode == 'fifo_flop':
                # 'fifo_flop' mode: note handshake time, defer data capture to next cycle
                last_xfer = True
                last_packet = packet
                await RisingEdge(self.clock)
                await Timer(self.tick_delay, units=self.tick_units)
                return last_packet, last_xfer
            else:
                # In skid/fifo_mux mode, capture data in the same cycle
                # CLEAN: Use inherited _get_data_dict() - no conditional mess!
                data_dict = self._get_data_dict()
                # CLEAN: Use inherited _finish_packet() - unified implementation!
                self._finish_packet(current_time, packet, data_dict)

                # Record transaction processed (using MonitorStatistics interface)
                self.stats.transactions_observed += 1

                # Handle memory operations if memory model available
                if self.memory_model:
                    # Use unified memory integration
                    self.handle_memory_write(packet)

        # Deassert ready on the rising edge (prepare for next cycle or delay)
        await RisingEdge(self.clock)
        await Timer(self.tick_delay, units=self.tick_units)
        self._set_ready(0)

        # Default return values
        return None, False

    async def _monitor_recv(self):
        """
        EXACT WORKING MONITOR RECV - DO NOT MODIFY TIMING/LOGIC

        Uses inherited clean _get_data_dict() and _finish_packet() methods
        that eliminate the conditional mess while preserving exact timing.
        """
        try:
            last_packet = None
            last_xfer = False

            while True:
                # recv phase 1: Handle pending transactions
                current_time = await self._recv_phase1(last_packet, last_xfer)

                # Always clear the last transfer here
                last_xfer = False

                # recv phase 2: Handle ready delays and assert ready if valid
                await self._recv_phase2()

                # recv phase 3: Check for valid handshake and process transaction
                last_packet, last_xfer = await self._recv_phase3(current_time)

        except Exception as e:
            self.log.error(f"GAXISlave({self.title}) Exception in _monitor_recv: {e}")
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

    def get_stats(self):
        """Get comprehensive statistics"""
        base_stats = self.get_base_stats()

        # Override monitor stats with same stats (MonitorStatistics used for both)
        base_stats['monitor_stats'] = self.stats.get_stats()

        return base_stats

    def __str__(self):
        """String representation"""
        return f"GAXISlave '{self.title}': {self.stats.received_transactions} transactions"
