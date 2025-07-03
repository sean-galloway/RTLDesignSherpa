"""
Interrupt Bus Components for AXI/AXI-Lite Error Monitoring

This module provides field configurations and components for working with
the AXI interrupt bus framework. It includes:
1. Field configurations for interrupt packets
2. Master/slave/monitor components for the interrupt bus

Updated to properly use GAXIPacket and field_config design patterns.
Removed unnecessary extract_packet_fields() function.
Enhanced with validation and error handling for GAXIPacket usage.
"""

from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer


# AXI Error Monitor Constants - matches RTL definitions from axi_errmon_types.sv
EVENT_CODES = {
    'NONE': 0x0,           # EVT_NONE
    'ADDR_TIMEOUT': 0x1,   # EVT_ADDR_TIMEOUT
    'DATA_TIMEOUT': 0x2,   # EVT_DATA_TIMEOUT
    'RESP_TIMEOUT': 0x3,   # EVT_RESP_TIMEOUT
    'RESP_SLVERR': 0x4,    # EVT_RESP_SLVERR
    'RESP_DECERR': 0x5,    # EVT_RESP_DECERR
    'DATA_ORPHAN': 0x6,    # EVT_DATA_ORPHAN
    'RESP_ORPHAN': 0x7,    # EVT_RESP_ORPHAN
    'PROTOCOL': 0x8,       # EVT_PROTOCOL
    'TRANS_COMPLETE': 0x9, # EVT_TRANS_COMPLETE
    'RESERVED_A': 0xA,     # EVT_RESERVED_A
    'RESERVED_B': 0xB,     # EVT_RESERVED_B
    'RESERVED_C': 0xC,     # EVT_RESERVED_C
    'RESERVED_D': 0xD,     # EVT_RESERVED_D
    'RESERVED_E': 0xE,     # EVT_RESERVED_E
    'USER_DEFINED': 0xF    # EVT_USER_DEFINED
}

PACKET_TYPES = {
    'ERROR': 0x0,       # PktTypeError
    'COMPLETION': 0x1,  # PktTypeCompletion
    'THRESHOLD': 0x2,   # PktTypeThreshold
    'TIMEOUT': 0x3,     # PktTypeTimeout
    'PERF': 0x4,        # PktTypePerf
    'DEBUG': 0xF        # PktTypeDebug
}

# Reverse lookup dictionaries for convenience
EVENT_CODE_NAMES = {v: k for k, v in EVENT_CODES.items()}
PACKET_TYPE_NAMES = {v: k for k, v in PACKET_TYPES.items()}


def get_event_name(event_code):
    """Get event name from event code"""
    return EVENT_CODE_NAMES.get(event_code, f"UNKNOWN_EVENT_{event_code:X}")


def get_packet_type_name(packet_type):
    """Get packet type name from packet type code"""
    return PACKET_TYPE_NAMES.get(packet_type, f"UNKNOWN_PKT_TYPE_{packet_type:X}")


def is_error_event(packet_type, event_code):
    """Check if this is an error event"""
    return packet_type == PACKET_TYPES['ERROR']


def is_timeout_event(packet_type, event_code):
    """Check if this is a timeout event"""
    return (packet_type == PACKET_TYPES['ERROR'] and
            event_code in [EVENT_CODES['ADDR_TIMEOUT'],
                            EVENT_CODES['DATA_TIMEOUT'],
                            EVENT_CODES['RESP_TIMEOUT']])


def is_response_error_event(packet_type, event_code):
    """Check if this is a response error event"""
    return (packet_type == PACKET_TYPES['ERROR'] and
            event_code in [EVENT_CODES['RESP_SLVERR'], EVENT_CODES['RESP_DECERR']])


def create_intrbus_field_config(payload_width=38, packet_type_width=4, event_code_width=4,
                                channel_width=6, unit_id_width=4, agent_id_width=8):
    """
    Create a field configuration for the interrupt bus packet format.

    The interrupt bus packet is structured as follows:
    - packet_type: 4 bits  [63:60] (error, completion, threshold, etc.)
    - event_code:  4 bits  [59:56] (specific error or event code)
    - channel_id:  6 bits  [55:50] (channel ID and AXI ID)
    - unit_id:     4 bits  [49:46] (subsystem identifier)
    - agent_id:    8 bits  [45:38] (module identifier)
    - payload:    38 bits  [37:0]  (payload related to event)

    Args:
        payload_width: Width of the payload field (default: 38)
        packet_type_width: Width of the packet type field (default: 4)
        event_code_width: Width of the event code field (default: 4)
        channel_width: Width of the channel ID field (default: 6)
        unit_id_width: Width of the unit ID field (default: 4)
        agent_id_width: Width of the agent ID field (default: 8)

    Returns:
        FieldConfig object configured for the interrupt bus
    """
    # Create field configuration
    field_config = FieldConfig()

    # Add fields to the field configuration from LSB to MSB
    field_config.add_field(FieldDefinition(
        name="payload",
        bits=payload_width,
        default=0,
        format="hex",
        display_width=10,
        description="Event Payload"
    ))

    field_config.add_field(FieldDefinition(
        name="agent_id",
        bits=agent_id_width,
        default=0,
        format="hex",
        display_width=2,
        description="Agent ID"
    ))

    field_config.add_field(FieldDefinition(
        name="unit_id",
        bits=unit_id_width,
        default=0,
        format="hex",
        display_width=1,
        description="Unit ID"
    ))

    field_config.add_field(FieldDefinition(
        name="channel_id",
        bits=channel_width,
        default=0,
        format="hex",
        display_width=2,
        description="Channel ID"
    ))

    field_config.add_field(FieldDefinition(
        name="event_code",
        bits=event_code_width,
        default=0,
        format="hex",
        display_width=1,
        description="Event/Error Code"
    ))

    field_config.add_field(FieldDefinition(
        name="packet_type",
        bits=packet_type_width,
        default=0,
        format="hex",
        display_width=1,
        description="Packet Type"
    ))

    # Set packet type encoding - using constants
    field_config.set_encoding("packet_type", {
        PACKET_TYPES['ERROR']: "ERROR",
        PACKET_TYPES['COMPLETION']: "COMPLETION",
        PACKET_TYPES['THRESHOLD']: "THRESHOLD",
        PACKET_TYPES['TIMEOUT']: "TIMEOUT",
        PACKET_TYPES['PERF']: "PERF",
        PACKET_TYPES['DEBUG']: "DEBUG"
    })

    # Set event code encoding - using constants
    field_config.set_encoding("event_code", {
        EVENT_CODES['NONE']: "NONE",
        EVENT_CODES['ADDR_TIMEOUT']: "ADDR_TIMEOUT",
        EVENT_CODES['DATA_TIMEOUT']: "DATA_TIMEOUT",
        EVENT_CODES['RESP_TIMEOUT']: "RESP_TIMEOUT",
        EVENT_CODES['RESP_SLVERR']: "RESP_SLVERR",
        EVENT_CODES['RESP_DECERR']: "RESP_DECERR",
        EVENT_CODES['DATA_ORPHAN']: "DATA_ORPHAN",
        EVENT_CODES['RESP_ORPHAN']: "RESP_ORPHAN",
        EVENT_CODES['PROTOCOL']: "PROTOCOL",
        EVENT_CODES['TRANS_COMPLETE']: "TRANS_COMPLETE",
        EVENT_CODES['RESERVED_A']: "RESERVED_A",
        EVENT_CODES['RESERVED_B']: "RESERVED_B",
        EVENT_CODES['RESERVED_C']: "RESERVED_C",
        EVENT_CODES['RESERVED_D']: "RESERVED_D",
        EVENT_CODES['RESERVED_E']: "RESERVED_E",
        EVENT_CODES['USER_DEFINED']: "USER_DEFINED"
    })

    return field_config


def create_intrbus_slave(dut, clock, title_prefix="IntrBusSlave", log=None,
                        randomizer=None, signal_prefix="", field_config=None):
    """
    Create an interrupt bus slave component.

    Args:
        dut: Device under test
        clock: Clock signal
        title_prefix: Prefix for component name
        log: Logger instance
        randomizer: FlexRandomizer for timing control
        signal_prefix: Prefix for DUT signals
        field_config: Field configuration for interrupt packets

    Returns:
        GAXISlave configured for interrupt bus
    """
    if field_config is None:
        field_config = create_intrbus_field_config()

    if randomizer is None:
        randomizer = FlexRandomizer({
            'ready_delay': ([[0, 0], [1, 3]], [8, 2])
        })

    # Set up signal mappings
    signal_map = {
        'm2s_valid': f"{signal_prefix}o_intrbus_valid",
        's2m_ready': f"{signal_prefix}i_intrbus_ready"
    }

    optional_signal_map = {
        'm2s_pkt': f"{signal_prefix}o_intrbus_packet"
    }

    # Create the slave using field mode (similar to buffer example)
    slave = GAXISlave(
        dut, title_prefix, '', clock,
        field_config=field_config,
        field_mode=True,  # Use field mode for packed signals
        randomizer=randomizer,
        log=log,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map
    )

    return slave


def create_intrbus_monitor(dut, clock, title_prefix="IntrBusMonitor", log=None,
                            signal_prefix="", field_config=None, is_slave=True):
    """
    Create an interrupt bus monitor component.

    Args:
        dut: Device under test
        clock: Clock signal
        title_prefix: Prefix for component name
        log: Logger instance
        signal_prefix: Prefix for DUT signals
        field_config: Field configuration for interrupt packets
        is_slave: Monitor from slave perspective

    Returns:
        GAXIMonitor configured for interrupt bus
    """
    if field_config is None:
        field_config = create_intrbus_field_config()

    # Set up signal mappings
    signal_map = {
        'm2s_valid': f"{signal_prefix}o_intrbus_valid",
        's2m_ready': f"{signal_prefix}i_intrbus_ready"
    }

    optional_signal_map = {
        'm2s_pkt': f"{signal_prefix}o_intrbus_packet"
    }

    # Create the monitor using field mode
    monitor = GAXIMonitor(
        dut, title_prefix, '', clock,
        field_config=field_config,
        field_mode=True,  # Use field mode for packed signals
        is_slave=is_slave,
        log=log,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map
    )

    return monitor


class AXIIntrBusMonitor:
    """
    Specialized monitor for AXI interrupt bus packets.

    This class provides a higher-level interface for monitoring AXI-specific
    interrupt packets, with methods for filtering by specific error types.

    Updated to use proper GAXIPacket field access with validation and error handling.
    """

    def __init__(self, dut, clock, title_prefix="AXIIntrBus", log=None, signal_prefix=""):
        """
        Initialize the AXI interrupt bus monitor.

        Args:
            dut: Device under test
            clock: Clock signal
            title_prefix: Prefix for component names
            log: Logger instance
            signal_prefix: Prefix for DUT signals
        """
        self.log = log

        # Create field configuration for interrupt bus
        self.field_config = create_intrbus_field_config()

        # Create the underlying monitor
        self.monitor = create_intrbus_monitor(
            dut, clock, f"{title_prefix}_GAXIMonitor", log, signal_prefix, self.field_config
        )

        # Create callback handlers
        self.callbacks = {
            'all': [],           # Called for all events
            'error': [],         # Called for error events
            'completion': [],    # Called for completion events
            'timeout': [],       # Called for timeout events
            'slverr': [],        # Called for slave error events
            'decerr': [],        # Called for decode error events
            'addr_timeout': [],  # Called for address timeout events
            'data_timeout': [],  # Called for data timeout events
            'resp_timeout': []   # Called for response timeout events
        }

        # Set up monitor callback
        self.monitor.add_callback(self._handle_packet)

        # Statistics
        self.stats = {
            'total_events': 0,
            'error_events': 0,
            'completion_events': 0,
            'timeout_events': 0,
            'slverr_events': 0,
            'decerr_events': 0,
            'addr_timeout_events': 0,
            'data_timeout_events': 0,
            'resp_timeout_events': 0
        }

    def _handle_packet(self, packet):
        """
        Handle a monitored packet using direct field access with validation.

        Args:
            packet: GAXIPacket from the monitor
        """
        # Validate that this is a GAXIPacket with the expected fields
        if not isinstance(packet, GAXIPacket):
            if self.log:
                self.log.error(f"Expected GAXIPacket, got {type(packet)}")
            return

        required_fields = ['packet_type', 'event_code', 'channel_id', 'unit_id', 'agent_id', 'payload']
        for field in required_fields:
            if not hasattr(packet, field):
                if self.log:
                    self.log.error(f"Packet missing required field: {field}")
                return

        # Update statistics
        self.stats['total_events'] += 1

        # Use direct field access - no need for field extraction!
        packet_type = packet.packet_type
        event_code = packet.event_code

        # Validate field values are within expected ranges
        if packet_type > 0xF:
            if self.log:
                self.log.warning(f"packet_type value {packet_type} exceeds 4-bit field")

        if event_code > 0xF:
            if self.log:
                self.log.warning(f"event_code value {event_code} exceeds 4-bit field")

        # Determine event type and update specific statistics
        if packet_type == PACKET_TYPES['ERROR']:  # ERROR
            self.stats['error_events'] += 1

            # Check specific error types using direct field access
            if event_code == EVENT_CODES['ADDR_TIMEOUT']:  # ADDR_TIMEOUT
                self.stats['addr_timeout_events'] += 1
                self.stats['timeout_events'] += 1
                self._call_callbacks('addr_timeout', packet)
                self._call_callbacks('timeout', packet)

            elif event_code == EVENT_CODES['DATA_TIMEOUT']:  # DATA_TIMEOUT
                self.stats['data_timeout_events'] += 1
                self.stats['timeout_events'] += 1
                self._call_callbacks('data_timeout', packet)
                self._call_callbacks('timeout', packet)

            elif event_code == EVENT_CODES['RESP_TIMEOUT']:  # RESP_TIMEOUT
                self.stats['resp_timeout_events'] += 1
                self.stats['timeout_events'] += 1
                self._call_callbacks('resp_timeout', packet)
                self._call_callbacks('timeout', packet)

            elif event_code == EVENT_CODES['RESP_SLVERR']:  # RESP_SLVERR
                self.stats['slverr_events'] += 1
                self._call_callbacks('slverr', packet)

            elif event_code == EVENT_CODES['RESP_DECERR']:  # RESP_DECERR
                self.stats['decerr_events'] += 1
                self._call_callbacks('decerr', packet)

            # Call error callbacks for all error types
            self._call_callbacks('error', packet)

        elif packet_type == PACKET_TYPES['COMPLETION']:  # COMPLETION
            self.stats['completion_events'] += 1
            self._call_callbacks('completion', packet)

        # Call general callbacks for all packet types
        self._call_callbacks('all', packet)

    def _call_callbacks(self, category, packet):
        """
        Call all callbacks registered for a specific category.

        Args:
            category: Callback category
            packet: GAXIPacket to pass to callbacks
        """
        for callback in self.callbacks[category]:
            try:
                callback(packet)
            except Exception as e:
                if self.log:
                    self.log.error(f"Error in callback for category {category}: {str(e)}")

    def add_callback(self, callback, category='all'):
        """
        Add a callback for specific packet types.

        Args:
            callback: Function to call when a matching packet is monitored
            category: Which packets to monitor. One of:
                        'all', 'error', 'completion', 'timeout', 'slverr', 'decerr',
                        'addr_timeout', 'data_timeout', 'resp_timeout'
        """
        if category in self.callbacks:
            self.callbacks[category].append(callback)
        else:
            raise ValueError(f"Unknown callback category: {category}")

    def format_event(self, packet):
        """
        Format an event packet into a human-readable description using direct field access with validation.

        Args:
            packet: GAXIPacket containing an interrupt event

        Returns:
            String description of the event
        """
        # Validate packet has required fields
        if not isinstance(packet, GAXIPacket):
            return f"Invalid packet type: {type(packet)}"

        required_fields = ['packet_type', 'event_code', 'channel_id', 'unit_id', 'agent_id', 'payload']
        if not all(hasattr(packet, field) for field in required_fields):
            missing_fields = [field for field in required_fields if not hasattr(packet, field)]
            return f"Invalid packet - missing required fields: {missing_fields}"

        # Use direct field access with encoding lookup
        packet_type_str = self.field_config._get_encoding("packet_type", packet.packet_type)
        event_code_str = self.field_config._get_encoding("event_code", packet.event_code)

        # Handle case where encoding lookup fails
        if packet_type_str is None:
            packet_type_str = f"UNKNOWN_PKT_TYPE_{packet.packet_type:X}"
        if event_code_str is None:
            event_code_str = f"UNKNOWN_EVENT_{packet.event_code:X}"

        # Format the event description
        event_desc = f"{packet_type_str}"
        if packet.packet_type == PACKET_TYPES['ERROR']:  # ERROR
            event_desc += f": {event_code_str}"

        # Add details using direct field access
        details = (
            f"Ch: 0x{packet.channel_id:X}, "
            f"Unit: 0x{packet.unit_id:X}, "
            f"Agent: 0x{packet.agent_id:X}, "
            f"Payload: 0x{packet.payload:X}"
        )

        return f"{event_desc} - {details}"

    def get_stats(self):
        """
        Get monitoring statistics.

        Returns:
            Dictionary of statistics
        """
        return dict(self.stats)

    def reset_stats(self):
        """Reset all statistics to zero"""
        for key in self.stats:
            self.stats[key] = 0

    def clear_monitor_queue(self):
        """Clear the monitor's queue of observed packets"""
        self.monitor.clear_queue()


# Factory functions for backward compatibility
def create_intrbus_specialized_monitor(dut, clock, title_prefix="IntrBusSpecializedMonitor",
                                        log=None, signal_prefix="", field_config=None):
    """
    Create a specialized interrupt bus monitor.

    Args:
        dut: Device under test
        clock: Clock signal
        title_prefix: Prefix for component name
        log: Logger instance
        signal_prefix: Prefix for DUT signals
        field_config: Field configuration for interrupt packets

    Returns:
        AXIIntrBusMonitor instance
    """
    return AXIIntrBusMonitor(dut, clock, title_prefix, log, signal_prefix)


# Example usage
if __name__ == "__main__":
    # This would normally be run under cocotb
    import cocotb
    from cocotb.triggers import RisingEdge, Timer
    from cocotb.clock import Clock

    @cocotb.test()
    async def test_intrbus(dut):
        # Create a clock
        clock = Clock(dut.clk, 10, units="ns")
        cocotb.start_soon(clock.start())

        # Reset the DUT
        dut.rst_n.value = 0
        await RisingEdge(dut.clk)
        await RisingEdge(dut.clk)
        dut.rst_n.value = 1

        # Create intrbus monitor
        intrbus = AXIIntrBusMonitor(dut, dut.clk)

        # Add callbacks using direct field access
        def print_all_events(packet):
            print(f"Event: {intrbus.format_event(packet)}")

        def print_error_events(packet):
            print(f"ERROR: {intrbus.format_event(packet)}")

        intrbus.add_callback(print_all_events, 'all')
        intrbus.add_callback(print_error_events, 'error')

        # Wait for packets to be processed
        await Timer(100, units='ns')

        # Check statistics
        stats = intrbus.get_stats()
        print(f"Statistics: {stats}")
