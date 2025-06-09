"""
FIFO Monitor Base - Common functionality for FIFO monitoring components

Provides shared initialization, signal resolution, data collection, and packet
finishing logic for both FIFOMonitor and FIFOSlave components.

Eliminates code duplication while preserving exact APIs and functionality.
"""

from cocotb_bus.monitors import BusMonitor
from cocotb.utils import get_sim_time

from ..field_config import FieldConfig
from ..signal_mapping_helper import SignalResolver
from ..data_strategies import DataCollectionStrategy
from ..monitor_statistics import MonitorStatistics
from .fifo_packet import FIFOPacket


class FIFOMonitorBase(BusMonitor):
    """
    Base class providing common FIFO monitoring functionality.

    Shared by FIFOMonitor and FIFOSlave to eliminate code duplication
    while preserving exact APIs and timing-critical behavior.

    Provides:
    - Common initialization logic
    - Signal resolution and data collection setup
    - Clean packet finishing without conditional mess
    - Unified statistics handling
    """

    def __init__(self, dut, title, prefix, clock, field_config,
                    mode='fifo_mux',
                    in_prefix='i_',
                    out_prefix='o_',
                    bus_name='',
                    pkt_prefix='',
                    multi_sig=False,
                    protocol_type=None,  # 'fifo_master' or 'fifo_slave' - set by subclass
                    log=None, super_debug=False, **kwargs):
        """
        Initialize common FIFO monitoring functionality.

        Args:
            dut: Device under test
            title: Component title/name
            prefix: Bus prefix
            clock: Clock signal
            field_config: Field configuration
            mode: FIFO mode ('fifo_mux' or 'fifo_flop')
            in_prefix: Input signal prefix
            out_prefix: Output signal prefix
            bus_name: Bus/channel name
            pkt_prefix: Packet field prefix
            multi_sig: Whether using multi-signal mode
            protocol_type: Must be set by subclass ('fifo_master' or 'fifo_slave')
            log: Logger instance
            super_debug: Enable detailed debugging
            **kwargs: Additional arguments for BusMonitor
        """
        # Core attributes - common setup
        self.title = title
        self.clock = clock
        self.mode = mode
        self.super_debug = super_debug

        # Signal naming convention params
        self.in_prefix = in_prefix
        self.out_prefix = out_prefix
        self.bus_name = bus_name
        self.pkt_prefix = pkt_prefix
        self.use_multi_signal = multi_sig

        # Validate protocol_type - must be set by subclass
        if protocol_type not in ['fifo_master', 'fifo_slave']:
            raise ValueError(f"protocol_type must be 'fifo_master' or 'fifo_slave', got: {protocol_type}")
        self.protocol_type = protocol_type

        # Handle field_config - convert dict if needed
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        else:
            self.field_config = field_config or FieldConfig.create_data_only()

        # Modern infrastructure - signal resolution
        self.signal_resolver = SignalResolver(
            protocol_type=self.protocol_type,
            dut=dut,
            bus=None,  # Set after BusMonitor init
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

        # Get signal lists for BusMonitor - ESSENTIAL FOR COCOTB
        self._signals, self._optional_signals = self.signal_resolver.get_signal_lists()

        # Initialize parent BusMonitor - MUST BE CALLED WITH EXACT PATTERN
        BusMonitor.__init__(self, dut, prefix, clock, callback=None, event=None, **kwargs)
        self.log = log or self._log

        # Apply modern signal mappings after bus is created
        self.signal_resolver.bus = self.bus
        self.signal_resolver.apply_to_component(self)

        # Modern infrastructure - data collection strategy with enhanced unpacking
        self.data_collector = DataCollectionStrategy(
            component=self,
            field_config=self.field_config,
            use_multi_signal=self.use_multi_signal,
            log=self.log
        )

        # Statistics - unified setup for all FIFO monitoring components
        from ..monitor_statistics import MonitorStatistics
        self.stats = MonitorStatistics()

        side_description = "read" if protocol_type == 'fifo_slave' else "write"
        self.log.info(f"FIFOMonitorBase '{title}' initialized: {side_description} side, "
                        f"mode={mode}, multi_sig={self.use_multi_signal}")

    def _get_data_dict(self):
        """
        UNIFIED: Clean data collection with automatic field unpacking.

        This replaces the messy _get_data_dict() + conditional unpacking logic
        that was duplicated in both FIFOMonitor and FIFOSlave.

        Uses the enhanced DataCollectionStrategy.collect_and_unpack_data() method
        that eliminates all the conditional mess.

        Returns:
            Dictionary of field values, properly unpacked
        """
        return self.data_collector.collect_and_unpack_data()

    def _finish_packet(self, current_time, packet, data_dict=None):
        """
        UNIFIED: Clean packet finishing without conditional mess.

        This replaces the duplicate _finish_packet logic that was in both
        FIFOMonitor and FIFOSlave with identical functionality.

        Args:
            current_time: Current simulation time
            packet: Packet to finish
            data_dict: Optional field data (if None, will collect fresh data)
        """
        # Get data if not provided
        if data_dict is None:
            data_dict = self._get_data_dict()

        # Use the packet's unpack_from_fifo method for field handling
        if data_dict:
            if hasattr(packet, 'unpack_from_fifo'):
                packet.unpack_from_fifo(data_dict)
            else:
                # Legacy fallback - set fields directly
                for field_name, value in data_dict.items():
                    if value != -1:  # Skip X/Z values
                        if hasattr(packet, field_name):
                            setattr(packet, field_name, value)

        # Set end time
        packet.end_time = current_time

        # Update statistics - use fields that exist in MonitorStatistics
        if hasattr(self.stats, 'received_transactions'):
            self.stats.received_transactions += 1
        if hasattr(self.stats, 'transactions_observed'):
            self.stats.transactions_observed += 1

        # Log the transaction
        packet_str = (packet.formatted(compact=True)
                        if hasattr(packet, 'formatted')
                        else str(packet))
        self.log.debug(f"FIFOMonitorBase({self.title}) Transaction at {current_time}ns: {packet_str}")

        # ESSENTIAL: Use cocotb _recv method to add to _recvQ and trigger callbacks
        self._recv(packet)

    def create_packet(self, **field_values):
        """
        UNIFIED: Create a packet with specified field values.

        This was duplicated identically in both FIFOMonitor and FIFOSlave.

        Args:
            **field_values: Initial field values

        Returns:
            FIFOPacket instance with specified field values
        """
        packet = FIFOPacket(self.field_config)
        for field_name, value in field_values.items():
            if hasattr(packet, field_name):
                setattr(packet, field_name, value)
        return packet

    def get_observed_packets(self, count=None):
        """
        Get observed packets from standard cocotb _recvQ.

        Args:
            count: Number of packets to return (None = all)

        Returns:
            List of observed packets
        """
        if count is None:
            return list(self._recvQ)
        return list(self._recvQ)[-count:]

    def clear_queue(self):
        """Clear the observed transactions queue - standard cocotb pattern"""
        self._recvQ.clear()
        self.log.info(f"FIFOMonitorBase ({self.title}): Observed queue cleared")

    def get_base_stats(self):
        """
        Get base statistics that are common to all FIFO monitoring components.

        Subclasses should call this and add their own specific statistics.

        Returns:
            Dictionary containing base statistics
        """
        return {
            'base_stats': self.stats.get_stats(),
            'data_collector_stats': self.data_collector.get_stats(),
            'signal_resolver_stats': self.signal_resolver.get_stats(),
            'observed_packets': len(self._recvQ),
            'protocol_type_used': self.protocol_type,
            'mode': self.mode,
            'multi_signal': self.use_multi_signal,
            'field_count': len(self.field_config) if self.field_config else 0
        }

    def __str__(self):
        """String representation"""
        side = "Read" if self.protocol_type == 'fifo_slave' else "Write"
        return (f"FIFOMonitorBase '{self.title}' ({side} Side): "
                f"{len(self._recvQ)} packets observed")


