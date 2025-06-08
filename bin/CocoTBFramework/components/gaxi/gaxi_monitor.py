"""GAXI Monitor Component - Clean signal handling using generic helpers"""
from collections import deque
from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import FallingEdge, Timer
from cocotb.utils import get_sim_time

from ..field_config import FieldConfig
from ..signal_mapping_helper import setup_gaxi_signals
from ..packet_factory import create_monitor_system
from .gaxi_packet import GAXIPacket


gaxi_valid_modes = ['skid', 'fifo_mux', 'fifo_flop']


class GAXIMonitor(BusMonitor):
    """
    Monitor for GAXI bus transactions with clean signal handling.
    
    All signal resolution happens once in __init__, eliminating hasattr() calls
    throughout the code. Uses clean signal names (self.valid, self.ready, self.data).
    """
    
    def __init__(self, dut, title, prefix, clock, is_slave=False,
                    field_config=None, packet_class=GAXIPacket, timeout_cycles=1000,
                    field_mode=False, multi_sig=False, log=None, mode='skid', 
                    signal_map=None, optional_signal_map=None, **kwargs):
        """
        Initialize the GAXI bus monitor.

        Args:
            dut: Device under test
            title: Title of the bus
            prefix: prefix used in the bus code
            clock: The clock signal
            is_slave: If True, use slave signals; if False, use master signals
            field_config: Field configuration for packets
            packet_class: Class to use for creating packets
            timeout_cycles: Maximum cycles to wait before timeout
            field_mode: If True, treat standard data bus as containing multiple fields
            multi_sig: Use multiple signals or not
            log: Logger instance
            mode: Operating mode ('skid', 'fifo_mux', 'fifo_flop')
            signal_map: Dictionary mapping required GAXI signals to DUT signals
            optional_signal_map: Dictionary mapping optional GAXI signals to DUT signals
            **kwargs: Additional arguments to pass to BusMonitor
        """
        # Validate mode parameter
        if mode not in gaxi_valid_modes:
            raise ValueError(f"Invalid mode '{mode}' for Monitor ({title}). "
                           f"Mode must be one of: {', '.join(gaxi_valid_modes)}")

        # Set up basic properties
        self.title = title
        self.clock = clock
        self.timeout_cycles = timeout_cycles
        self.field_mode = field_mode or multi_sig
        self.use_multi_signal = multi_sig
        self.is_slave = is_slave
        self.mode = mode

        # Handle field_config - convert dict to FieldConfig if needed
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        else:
            self.field_config = field_config or FieldConfig.create_data_only()

        # Prepare signal lists for BusMonitor initialization
        # We'll let the signal mapper handle the actual mapping
        if not self.use_multi_signal:
            # Standard mode - we'll populate this after signal mapping
            self._signals = []
        else:
            # Multi-signal mode - only control signals in base
            self._signals = []

        self._optional_signals = []

        # Initialize base BusMonitor
        BusMonitor.__init__(self, dut, prefix, clock, callback=None, event=None, **kwargs)
        self.log = log or self._log

        # === CLEAN SIGNAL SETUP - NO MORE hasattr() CALLS ===
        self.signal_mapper = setup_gaxi_signals(
            component=self,
            dut=dut, 
            bus=self.bus,
            log=self.log,
            component_name=f"Monitor({self.title})",
            is_slave=self.is_slave,
            mode=self.mode,
            custom_signal_map=signal_map,
            custom_optional_signal_map=optional_signal_map
        )

        # After signal setup, we have clean attributes:
        # self.valid - for m2s_valid signal (or None if missing)
        # self.ready - for s2m_ready signal (or None if missing)  
        # self.data - for m2s_pkt signal (or None if missing)

        # Set up multi-signal field mappings if needed
        self.field_signals = {}
        if self.use_multi_signal:
            self._setup_multi_signal_fields()

        # Initialize packet handling system
        self.packet_factory, self.transaction_handler, self.field_unpacker = create_monitor_system(
            packet_class=packet_class,
            field_config=self.field_config,
            log=self.log,
            component_name=f"Monitor({self.title})"
        )

        # Initialize tracking
        self.observed_queue = deque()

        # Debug output
        self.log.info(f"GAXIMonitor initialized for {title} in mode '{mode}', "
                     f"{'slave' if is_slave else 'master'} port, "
                     f"{'multi-signal' if self.use_multi_signal else 'standard'} mode")

    def _setup_multi_signal_fields(self):
        """Setup field signal mappings for multi-signal mode."""
        for field_name in self.field_config.field_names():
            field_signal_name = f'm2s_pkt_{field_name}'
            
            # Check if this field has a signal mapping in our mapper
            if self.signal_mapper.has_signal(field_signal_name):
                self.field_signals[field_name] = self.signal_mapper.get_signal(field_signal_name)
            else:
                self.log.warning(f"No signal mapping for field {field_name}")

    def clear_queue(self):
        """Clear the observed transactions queue."""
        self.observed_queue.clear()
        self.log.info(f"Monitor({self.title}): Observed queue cleared")

    def _check_field_value(self, field_name, field_value):
        """Check if a field value exceeds the maximum for the field."""
        if not hasattr(self.field_config, 'get_field'):
            return field_value

        try:
            field_def = self.field_config.get_field(field_name)
            bits = field_def.bits
            max_value = (1 << bits) - 1

            if field_value > max_value:
                current_time = get_sim_time('ns')
                self.log.warning(
                    f"Monitor({self.title}) at {current_time}ns: Field '{field_name}' "
                    f"value 0x{field_value:X} exceeds maximum 0x{max_value:X} ({bits} bits). "
                    f"Value will be masked."
                )
                return field_value & max_value
        except Exception as e:
            self.log.error(f"Error checking field value: {e}")

        return field_value

    def _get_data_dict(self):
        """
        Collect data from signals and handle X/Z values.
        Uses clean signal references instead of hasattr() calls.
        """
        data_dict = {}

        if self.use_multi_signal:
            # Multi-signal mode: collect from individual field signals
            for field_name, signal in self.field_signals.items():
                if signal is not None:
                    if signal.value.is_resolvable:
                        field_value = int(signal.value)
                        field_value = self._check_field_value(field_name, field_value)
                        data_dict[field_name] = field_value
                    else:
                        self.log.warning(f"Field {field_name} has X/Z value")
                        data_dict[field_name] = -1
                        
        elif self.data is not None:
            # Standard mode using clean self.data reference
            if self.data.value.is_resolvable:
                raw_value = int(self.data.value)
                if self.field_mode:
                    # Multi-field mode (will be unpacked later)
                    data_dict['data'] = raw_value
                else:
                    # Single data field
                    field_value = self._check_field_value('data', raw_value)
                    data_dict['data'] = field_value
            else:
                self.log.warning("Data signal has X/Z value")
                data_dict['data'] = -1

        return data_dict

    def _process_transaction(self, current_time, data_dict):
        """Process a complete transaction."""
        packet = self.transaction_handler.create_transaction(current_time)
        
        # Handle field unpacking for different modes
        if not self.use_multi_signal and self.field_mode and 'data' in data_dict:
            # Unpack combined data value into individual fields
            combined_value = data_dict['data']
            unpacked_fields = self.field_unpacker.unpack_combined_fields(combined_value)
            data_dict = unpacked_fields

        # Complete the transaction
        completed_packet = self.transaction_handler.finish_transaction(packet, current_time, data_dict)
        self.observed_queue.append(completed_packet)
        
        return completed_packet

    async def _monitor_recv(self):
        """
        Monitor for GAXI transactions.
        Uses clean signal references (self.valid, self.ready) instead of hasattr() calls.
        """
        try:
            last_packet = None
            last_xfer = False

            while True:
                await FallingEdge(self.clock)
                current_time = get_sim_time('ns')

                # Handle pending transactions from previous cycle (fifo_flop mode)
                if last_xfer and last_packet:
                    data_dict = self._get_data_dict()
                    completed_packet = self.transaction_handler.finish_transaction(last_packet, current_time, data_dict)
                    self.observed_queue.append(completed_packet)
                    last_xfer = False
                    last_packet = None

                # Check for valid handshake using clean signal references
                if (self.valid is not None and self.ready is not None and
                    self.valid.value.is_resolvable and self.ready.value.is_resolvable and
                    self.valid.value.integer == 1 and self.ready.value.integer == 1):
                    
                    if self.mode == 'fifo_flop':
                        # Schedule data capture for next cycle
                        last_packet = self.transaction_handler.create_transaction(current_time)
                        last_xfer = True
                    else:
                        # Capture data immediately
                        data_dict = self._get_data_dict()
                        self._process_transaction(current_time, data_dict)

                # Brief delay for signal stability
                await Timer(1, units='ps')

        except Exception as e:
            self.log.error(f"Monitor({self.title}): Exception in _monitor_recv: {str(e)}")
            import traceback
            self.log.error(traceback.format_exc())
            raise

    def get_stats(self):
        """Get statistics about observed transactions."""
        result = {
            'transactions_observed': len(self.observed_queue),
            'monitor_type': 'slave' if self.is_slave else 'master'
        }
        
        # Add transaction handler stats
        if hasattr(self.transaction_handler, 'get_stats'):
            result.update(self.transaction_handler.get_stats())

        return result

    def get_observed_packets(self, count=None):
        """Get observed packets."""
        if count is None:
            return list(self.observed_queue)
        return list(self.observed_queue)[-count:]
