"""
FIFO Monitor - Combines exact working cocotb methods with modern infrastructure
"""

import cocotb
from collections import deque
from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import FallingEdge, Timer
from cocotb.utils import get_sim_time

from ..field_config import FieldConfig
from ..signal_mapping_helper import SignalResolver
from ..data_strategies import DataCollectionStrategy
from ..monitor_statistics import MonitorStatistics
from .fifo_packet import FIFOPacket


class FIFOMonitor(BusMonitor):
    """
    FIFO Monitor combining exact working cocotb methods with modern infrastructure.
    
    Preserves all timing-critical cocotb methods while adding:
    - Automatic signal resolution via SignalResolver  
    - High-performance data collection via DataCollectionStrategy
    - Standard cocotb _recvQ pattern for packet queueing
    - Protocol violation detection
    """

    def __init__(self, dut, title, prefix, clock, field_config, is_slave=False,
                 mode='fifo_mux', bus_name='', pkt_prefix='', fifo_depth=16,
                 log=None, super_debug=False, **kwargs):
        """
        Initialize FIFO Monitor with modern infrastructure.
        """
        # Core attributes - keeping original working setup
        self.title = title
        self.clock = clock
        self.is_slave = is_slave
        self.mode = mode
        self.super_debug = super_debug
        self.fifo_depth = fifo_depth

        # Handle field_config - convert dict if needed
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        else:
            self.field_config = field_config or FieldConfig.create_data_only()

        # Multi-signal mode detection
        self.use_multi_signal = len(self.field_config) > 1
        self.field_mode = self.use_multi_signal

        # Choose protocol type based on what we're monitoring
        protocol_type = 'fifo_slave' if is_slave else 'fifo_master'

        # Modern infrastructure - signal resolution
        self.signal_resolver = SignalResolver(
            protocol_type=protocol_type,
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
        # We'll use our own enhanced stats that includes everything
        from ..monitor_statistics import MonitorStatistics
        self.enhanced_stats = MonitorStatistics()

        # EXACT WORKING COCOTB PATTERN - inherit _recvQ from BusMonitor
        # DO NOT ADD: self.observed_queue = deque()  # This would break cocotb pattern

        # Initialize tracking variables for FIFO state - from original working code
        self.fifo_depth_estimate = 0      # Current estimated FIFO depth
        self.fifo_capacity = fifo_depth    # FIFO capacity
        self.last_transaction = None       # Last observed transaction
        self.pending_transaction = None    # For fifo_flop mode

        side = "read" if is_slave else "write"
        self.log.info(f"FIFOMonitor '{title}' initialized: {side} side, mode={mode}, "
                      f"multi_sig={self.use_multi_signal}")

    def set_fifo_capacity(self, capacity):
        """Set the assumed FIFO capacity for depth tracking - from original"""
        self.fifo_capacity = capacity
        self.log.info(f"FIFOMonitor ({self.title}): Set FIFO capacity to {capacity}")

    def _get_data_dict(self):
        """
        MODERNIZED: Use DataCollectionStrategy instead of manual signal collection
        """
        return self.data_collector.collect_data()

    def _update_fifo_depth(self, is_write):
        """
        Update estimated FIFO depth - EXACT WORKING LOGIC FROM ORIGINAL
        """
        current_time = get_sim_time('ns')

        if is_write:
            # Check if FIFO is actually full before warning
            if (hasattr(self, 'full_sig') and self.full_sig is not None and 
                self.full_sig.value.is_resolvable and int(self.full_sig.value) == 1):
                self.log.warning(f"FIFOMonitor ({self.title}): Write to full FIFO detected at {current_time}ns")
                self.enhanced_stats.write_while_full += 1
            else:
                # Safe to increment depth
                self.fifo_depth_estimate = min(self.fifo_depth_estimate + 1, self.fifo_capacity)

            # Update full cycles counter
            if self.fifo_depth_estimate >= self.fifo_capacity:
                self.enhanced_stats.full_cycles += 1
        else:
            # Check for empty FIFO read
            if (hasattr(self, 'empty_sig') and self.empty_sig is not None and
                self.empty_sig.value.is_resolvable and int(self.empty_sig.value) == 1):
                self.log.warning(f"FIFOMonitor ({self.title}): Read from empty FIFO detected at {current_time}ns")
                self.enhanced_stats.read_while_empty += 1
            elif self.fifo_depth_estimate > 0:
                self.fifo_depth_estimate = max(0, self.fifo_depth_estimate - 1)

            # Update empty cycles counter
            if self.fifo_depth_estimate == 0:
                self.enhanced_stats.empty_cycles += 1

        return self.fifo_depth_estimate

    def _check_protocol_violation(self, is_write):
        """
        EXACT WORKING PROTOCOL VIOLATION CHECK FROM ORIGINAL
        """
        if is_write:
            # Check for write while full violation
            if (hasattr(self, 'write_sig') and self.write_sig is not None and
                hasattr(self, 'full_sig') and self.full_sig is not None and
                self.write_sig.value.is_resolvable and
                self.full_sig.value.is_resolvable and
                int(self.write_sig.value) == 1 and
                int(self.full_sig.value) == 1):
                self.log.warning(f"FIFOMonitor ({self.title}): Protocol violation - write while full at {get_sim_time('ns')}ns")
                self.enhanced_stats.protocol_violations += 1
                return True
        else:
            # Check for read while empty violation
            if (hasattr(self, 'read_sig') and self.read_sig is not None and
                hasattr(self, 'empty_sig') and self.empty_sig is not None and
                self.read_sig.value.is_resolvable and
                self.empty_sig.value.is_resolvable and
                int(self.read_sig.value) == 1 and
                int(self.empty_sig.value) == 1):
                self.log.warning(f"FIFOMonitor ({self.title}): Protocol violation - read while empty at {get_sim_time('ns')}ns")
                self.enhanced_stats.protocol_violations += 1
                return True

        return False

    def _finish_packet(self, current_time, packet, data_dict=None):
        """
        EXACT WORKING PACKET FINISHING FROM ORIGINAL - only modernize infrastructure
        """
        # Check if we need to unpack fields from a combined value - EXACT WORKING LOGIC
        if not self.use_multi_signal:
            if (
                self.field_mode
                and isinstance(data_dict, dict)
                and 'data' in data_dict
            ):
                # Field mode - extract fields from combined value
                unpacked_fields = {}
                combined_value = data_dict['data']
                data_dict = self._finish_packet_helper(combined_value, unpacked_fields)
            elif (
                not self.field_mode
                and isinstance(data_dict, dict)
                and 'data' in data_dict
                and hasattr(self.field_config, 'field_names')
                and len(self.field_config) > 1
            ):
                # Standard mode with complex field config
                unpacked_fields = {}
                combined_value = data_dict['data']
                data_dict = self._finish_packet_helper(combined_value, unpacked_fields)

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

        # Set end time - EXACT WORKING PATTERN
        packet.end_time = current_time

        # Update stats - use our enhanced stats that has both fields
        self.enhanced_stats.received_transactions += 1
        self.enhanced_stats.transactions_observed += 1

        self.log.debug(f"FIFOMonitor({self.title}) Transaction at {current_time}ns: "
                       f"{packet.formatted(compact=True) if hasattr(packet, 'formatted') else str(packet)}")

        # ESSENTIAL: Use cocotb _recv method to add to _recvQ and trigger callbacks
        self._recv(packet)

    def _finish_packet_helper(self, combined_value, unpacked_fields):
        """EXACT WORKING HELPER FROM ORIGINAL - DO NOT MODIFY"""
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

    async def _monitor_recv(self):
        """
        EXACT WORKING MONITOR RECV FROM ORIGINAL - DO NOT MODIFY TIMING
        Only modernize infrastructure calls (data collection, etc.)
        """
        try:
            # Set up pending transaction for fifo_flop mode
            pending_packet = None
            pending_capture = False

            while True:
                # Wait for a falling edge to sample signals - EXACT WORKING TIMING
                await FallingEdge(self.clock)

                # Get current time
                current_time = get_sim_time('ns')

                # Check for protocol violations - EXACT WORKING LOGIC
                self._check_protocol_violation(not self.is_slave)

                # Handle pending captures for fifo_flop mode - EXACT WORKING LOGIC
                if pending_capture and self.mode == 'fifo_flop':
                    # MODERNIZED: Use data collection strategy
                    data_dict = self._get_data_dict()
                    self._finish_packet(current_time, pending_packet, data_dict)
                    pending_capture = False
                    pending_packet = None

                # Check for write/read operations - EXACT WORKING LOGIC
                if self.is_slave:
                    # Monitoring read port - check if read=1 AND empty=0 (valid read)
                    valid_read = (
                        hasattr(self, 'read_sig') and self.read_sig is not None and
                        hasattr(self, 'empty_sig') and self.empty_sig is not None and
                        self.read_sig.value.is_resolvable and
                        int(self.read_sig.value) == 1 and   # read is asserted
                        self.empty_sig.value.is_resolvable and
                        int(self.empty_sig.value) == 0       # not empty
                    )

                    if valid_read:
                        # Create a packet and capture data immediately or in next cycle
                        # depending on the mode
                        packet = FIFOPacket(self.field_config)
                        packet.start_time = current_time

                        # Update FIFO depth
                        self._update_fifo_depth(is_write=False)

                        if self.mode == 'fifo_flop':
                            # Schedule capture for next cycle
                            pending_capture = True
                            pending_packet = packet
                        else:
                            # Capture data immediately from the data signal
                            # MODERNIZED: Use data collection strategy
                            data_dict = self._get_data_dict()
                            self._finish_packet(current_time, packet, data_dict)

                    elif (hasattr(self, 'read_sig') and self.read_sig is not None and
                          hasattr(self, 'empty_sig') and self.empty_sig is not None and
                          self.read_sig.value.is_resolvable and
                          int(self.read_sig.value) == 1 and
                          self.empty_sig.value.is_resolvable and
                          int(self.empty_sig.value) == 1):  # read while empty
                        # Already logged in _update_fifo_depth, just update stats
                        pass

                    # Update empty cycles counter if applicable
                    if (hasattr(self, 'empty_sig') and self.empty_sig is not None and
                        self.empty_sig.value.is_resolvable and int(self.empty_sig.value) == 1):
                        self.enhanced_stats.empty_cycles += 1
                else:
                    # Monitoring write port - check if write=1 (valid write)
                    if (hasattr(self, 'write_sig') and self.write_sig is not None and
                        self.write_sig.value.is_resolvable and int(self.write_sig.value) == 1):
                        
                        if (not hasattr(self, 'full_sig') or self.full_sig is None or
                            not self.full_sig.value.is_resolvable or
                            int(self.full_sig.value) == 0):  # write and not full
                            
                            # Create new packet
                            packet = FIFOPacket(self.field_config)
                            packet.start_time = current_time

                            # Update FIFO depth
                            self._update_fifo_depth(is_write=True)

                            # Capture data - MODERNIZED: Use data collection strategy
                            data_dict = self._get_data_dict()
                            self._finish_packet(current_time, packet, data_dict)
                        elif (hasattr(self, 'full_sig') and self.full_sig is not None and
                              self.full_sig.value.is_resolvable and int(self.full_sig.value) == 1):  # write while full
                            # Already logged in _update_fifo_depth, just update stats
                            pass

                    # Update full cycles counter if applicable
                    if (hasattr(self, 'full_sig') and self.full_sig is not None and
                        self.full_sig.value.is_resolvable and int(self.full_sig.value) == 1):
                        self.enhanced_stats.full_cycles += 1

                # Wait a bit to avoid oversampling - EXACT WORKING TIMING
                await Timer(1, units='ps')

        except Exception as e:
            self.log.error(f"FIFOMonitor ({self.title}): Exception in _monitor_recv: {e}")
            import traceback
            self.log.error(traceback.format_exc())
            raise

    # Modern convenience methods
    def create_packet(self, **field_values):
        """Create a packet with specified field values"""
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
        self.log.info(f"FIFOMonitor ({self.title}): Observed queue cleared")

    def get_stats(self):
        """Get comprehensive statistics - MODERNIZED"""
        # Use our enhanced stats that has all the fields we need
        result = {
            'monitor_stats': self.enhanced_stats.__dict__.copy(),
            'data_collector_stats': self.data_collector.get_stats(),
            'signal_resolver_stats': self.signal_resolver.get_stats(),
            'monitor_type': 'read' if self.is_slave else 'write',
            'fifo_depth_estimate': self.fifo_depth_estimate,
            'fifo_capacity': self.fifo_capacity,
            'utilization_percentage': (self.fifo_depth_estimate / self.fifo_capacity * 100) if self.fifo_capacity > 0 else 0,
            'observed_packets': len(self._recvQ),  # Use standard cocotb _recvQ
            'protocol_type_used': 'fifo_slave' if self.is_slave else 'fifo_master'
        }
        return result

    def __str__(self):
        """String representation"""
        side = "Read" if self.is_slave else "Write"
        return (f"FIFOMonitor '{self.title}' ({side} Side): "
                f"{len(self._recvQ)} packets observed")
