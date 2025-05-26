"""
Interrupt Bus Components for AXI/AXI-Lite Error Monitoring Verification

This module provides components for working with the AXI interrupt bus framework used in
the AXI Error Monitor system. It includes:
1. Field configurations for interrupt packets based on axi_errmon_types.sv
2. Master/slave/monitor components for the interrupt bus
3. Event/callback handling for interrupt events

Updated to match the RTL's consolidated 64-bit interrupt bus packet format.
"""

from CocoTBFramework.components.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.flex_randomizer import FlexRandomizer


def create_intrbus_field_config():
    """
    Create a field configuration for the interrupt bus packet format based on
    axi_errmon_types.sv definitions.
    
    The interrupt bus packet is structured as a 64-bit consolidated packet:
    - packet_type: 4 bits  [63:60] (error, completion, threshold, etc.)
    - event_code:  4 bits  [59:56] (specific error or event code) 
    - channel_id:  6 bits  [55:50] (channel ID and AXI ID)
    - unit_id:     4 bits  [49:46] (subsystem identifier)
    - agent_id:    8 bits  [45:38] (module identifier)
    - addr:        38 bits [37:0]  (address related to event)
        
    Returns:
        FieldConfig object configured for the interrupt bus
    """
    # Create field configuration for the full 64-bit packet
    field_config = FieldConfig()
    
    # Add the consolidated packet field
    field_config.add_field(FieldDefinition(
        name="intrbus_packet",
        bits=64,
        default=0,
        format="hex",
        display_width=16,
        description="64-bit Interrupt Bus Packet"
    ))
    
    # Add convenience fields for extracting packet components
    field_config.add_field(FieldDefinition(
        name="packet_type",
        bits=4,
        default=0,
        format="hex",
        display_width=1,
        description="Packet Type [63:60]"
    ))
    
    field_config.add_field(FieldDefinition(
        name="event_code",
        bits=4,
        default=0,
        format="hex",
        display_width=1,
        description="Event/Error Code [59:56]"
    ))
    
    field_config.add_field(FieldDefinition(
        name="channel_id",
        bits=6,
        default=0,
        format="hex",
        display_width=2,
        description="Channel ID [55:50]"
    ))
    
    field_config.add_field(FieldDefinition(
        name="unit_id",
        bits=4,
        default=0,
        format="hex",
        display_width=1,
        description="Unit ID [49:46]"
    ))
    
    field_config.add_field(FieldDefinition(
        name="agent_id",
        bits=8,
        default=0,
        format="hex",
        display_width=2,
        description="Agent ID [45:38]"
    ))
    
    field_config.add_field(FieldDefinition(
        name="addr",
        bits=38,
        default=0,
        format="hex",
        display_width=10,
        description="Address/Data [37:0]"
    ))
    
    # Set packet type encoding from axi_errmon_types.sv
    field_config.set_encoding("packet_type", {
        0x0: "ERROR",       # PktTypeError
        0x1: "COMPLETION",  # PktTypeCompletion
        0x2: "THRESHOLD",   # PktTypeThreshold
        0x3: "TIMEOUT",     # PktTypeTimeout
        0x4: "PERF",        # PktTypePerf
        0xF: "DEBUG"        # PktTypeDebug
    })
    
    # Set event code encoding from axi_errmon_types.sv
    field_config.set_encoding("event_code", {
        0x0: "NONE",             # EVT_NONE
        0x1: "ADDR_TIMEOUT",     # EVT_ADDR_TIMEOUT
        0x2: "DATA_TIMEOUT",     # EVT_DATA_TIMEOUT
        0x3: "RESP_TIMEOUT",     # EVT_RESP_TIMEOUT
        0x4: "RESP_SLVERR",      # EVT_RESP_SLVERR
        0x5: "RESP_DECERR",      # EVT_RESP_DECERR
        0x6: "DATA_ORPHAN",      # EVT_DATA_ORPHAN
        0x7: "RESP_ORPHAN",      # EVT_RESP_ORPHAN
        0x8: "PROTOCOL",         # EVT_PROTOCOL
        0x9: "TRANS_COMPLETE",   # EVT_TRANS_COMPLETE
        0xA: "RESERVED_A",       # EVT_RESERVED_A
        0xB: "RESERVED_B",       # EVT_RESERVED_B
        0xC: "RESERVED_C",       # EVT_RESERVED_C
        0xD: "RESERVED_D",       # EVT_RESERVED_D
        0xE: "RESERVED_E",       # EVT_RESERVED_E
        0xF: "USER_DEFINED"      # EVT_USER_DEFINED
    })
    
    return field_config


def extract_packet_fields(packet_value):
    """
    Extract individual fields from a 64-bit interrupt bus packet.
    
    Args:
        packet_value: 64-bit integer packet value
        
    Returns:
        Dictionary with extracted fields
    """
    return {
        'packet_type': (packet_value >> 60) & 0xF,
        'event_code': (packet_value >> 56) & 0xF,
        'channel_id': (packet_value >> 50) & 0x3F,
        'unit_id': (packet_value >> 46) & 0xF,
        'agent_id': (packet_value >> 38) & 0xFF,
        'addr': packet_value & 0x3FFFFFFFFF  # 38 bits
    }


def create_packet_value(packet_type, event_code, channel_id, unit_id, agent_id, addr):
    """
    Create a 64-bit interrupt bus packet from individual fields.
    
    Args:
        packet_type: 4-bit packet type
        event_code: 4-bit event code
        channel_id: 6-bit channel ID
        unit_id: 4-bit unit ID
        agent_id: 8-bit agent ID
        addr: 38-bit address/data
        
    Returns:
        64-bit integer packet value
    """
    packet = 0
    packet |= (packet_type & 0xF) << 60
    packet |= (event_code & 0xF) << 56
    packet |= (channel_id & 0x3F) << 50
    packet |= (unit_id & 0xF) << 46
    packet |= (agent_id & 0xFF) << 38
    packet |= addr & 0x3FFFFFFFFF  # 38 bits
    return packet


class IntrBusComponents:
    """
    Combined components for the interrupt bus, providing master, slave, and monitor functionality.
    
    This class creates and manages the components needed to interface with the AXI interrupt bus,
    including field configurations and signal mappings for the consolidated 64-bit packet format.
    """
    
    def __init__(self, dut, clock, field_config=None, title_prefix="IntrBus", 
                log=None, randomizer=None, signal_prefix=""):
        """
        Initialize the interrupt bus components.
        
        Args:
            dut: Device under test
            clock: Clock signal
            field_config: Field configuration for interrupt packets (created automatically if None)
            title_prefix: Prefix for component names
            log: Logger instance
            randomizer: Randomizer for timing constraints
            signal_prefix: Prefix for DUT signals (e.g., "fub_" or "")
        """
        # Store parameters
        self.dut = dut
        self.clock = clock
        self.title_prefix = title_prefix
        self.log = log
        
        # Create field configuration if not provided
        if field_config is None:
            self.field_config = create_intrbus_field_config()
        else:
            self.field_config = field_config
        
        # Set up signal names with optional prefix - matching RTL interface
        self.signal_prefix = signal_prefix
        self.valid_signal = f"{signal_prefix}o_intrbus_valid"
        self.ready_signal = f"{signal_prefix}i_intrbus_ready"
        self.packet_signal = f"{signal_prefix}o_intrbus_packet"
        
        # Create randomizer if not provided
        if randomizer is None:
            self.randomizer = FlexRandomizer({
                'valid_delay': ([[0, 0], [1, 3]], [8, 2]),  # Mostly back-to-back with occasional delay
                'ready_delay': ([[0, 0], [1, 2]], [9, 1])   # Mostly ready immediately
            })
        else:
            self.randomizer = randomizer
        
        # Create the components
        self._create_components()
    
    def _create_components(self):
        """Create the master, slave, and monitor components"""
        
        # Create master for driving interrupt packets (not typically used in monitoring)
        self.master = GAXIMaster(
            self.dut, f'{self.title_prefix}Master', '', self.clock,
            field_config=self.field_config,
            randomizer=self.randomizer,
            log=self.log,
            signal_map={
                'm2s_valid': self.valid_signal,
                's2m_ready': self.ready_signal
            },
            optional_signal_map={
                'm2s_pkt_intrbus_packet': self.packet_signal
            }
        )
        
        # Create slave for receiving interrupt packets (this is the main interface)
        self.slave = GAXISlave(
            self.dut, f'{self.title_prefix}Slave', '', self.clock,
            field_config=self.field_config,
            randomizer=self.randomizer,
            log=self.log,
            signal_map={
                'm2s_valid': self.valid_signal,
                's2m_ready': self.ready_signal
            },
            optional_signal_map={
                'm2s_pkt_intrbus_packet': self.packet_signal
            }
        )
        
        # Create monitor for tracking interrupt packets
        self.monitor = GAXIMonitor(
            self.dut, f'{self.title_prefix}Monitor', '', self.clock,
            field_config=self.field_config,
            is_slave=True,  # Monitor from slave perspective
            log=self.log,
            signal_map={
                'm2s_valid': self.valid_signal,
                's2m_ready': self.ready_signal
            },
            optional_signal_map={
                'm2s_pkt_intrbus_packet': self.packet_signal
            }
        )
    
    def set_randomizer(self, randomizer):
        """
        Update the randomizer used for timing control.
        
        Args:
            randomizer: New FlexRandomizer instance
        """
        self.randomizer = randomizer
        self.master.set_randomizer(randomizer)
        self.slave.set_randomizer(randomizer)
    
    async def reset_bus(self):
        """Reset the master and slave interfaces"""
        await self.master.reset_bus()
        await self.slave.reset_bus()
    
    def add_monitor_callback(self, callback):
        """
        Add a callback function to the monitor.
        
        Args:
            callback: Function to call when a packet is monitored
        """
        self.monitor.add_callback(callback)
    
    def clear_monitor_queue(self):
        """Clear the monitor's queue of observed packets"""
        self.monitor.clear_queue()
    
    def format_event(self, packet):
        """
        Format an event packet into a human-readable description.
        
        Args:
            packet: GAXIPacket containing an interrupt event
            
        Returns:
            String description of the event
        """
        # Extract fields from the packet
        if hasattr(packet, 'intrbus_packet'):
            fields = extract_packet_fields(packet.intrbus_packet)
        else:
            # Use individual fields if available
            fields = {
                'packet_type': getattr(packet, 'packet_type', 0),
                'event_code': getattr(packet, 'event_code', 0),
                'channel_id': getattr(packet, 'channel_id', 0),
                'unit_id': getattr(packet, 'unit_id', 0),
                'agent_id': getattr(packet, 'agent_id', 0),
                'addr': getattr(packet, 'addr', 0)
            }
        
        # Get decoded field values
        packet_type_str = self.field_config._get_encoding("packet_type", fields['packet_type'])
        event_code_str = self.field_config._get_encoding("event_code", fields['event_code'])
        
        # Format the event description
        event_desc = f"{packet_type_str}"
        if fields['packet_type'] == 0:  # ERROR
            event_desc += f": {event_code_str}"
        elif fields['packet_type'] == 3:  # TIMEOUT
            event_desc += f": {event_code_str}"
        
        # Add details
        details = (
            f"Ch: 0x{fields['channel_id']:X}, "
            f"Unit: 0x{fields['unit_id']:X}, "
            f"Agent: 0x{fields['agent_id']:X}, "
            f"Addr: 0x{fields['addr']:X}"
        )
        
        return f"{event_desc} - {details}"


class AXIIntrBusMonitor:
    """
    Specialized monitor for AXI interrupt bus packets.
    
    This class provides a higher-level interface for monitoring AXI error monitor
    interrupt packets, with methods for filtering by specific error types and
    event categories. It aligns with the axi_errmon_types.sv definitions.
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
        # Create field configuration for interrupt bus
        self.field_config = create_intrbus_field_config()
        
        # Create components
        self.components = IntrBusComponents(
            dut, clock, self.field_config, title_prefix, log, signal_prefix=signal_prefix
        )
        
        # Create callback handlers for all event types from axi_errmon_types.sv
        self.callbacks = {
            'all': [],               # Called for all events
            'error': [],             # Called for error events
            'completion': [],        # Called for completion events
            'threshold': [],         # Called for threshold events
            'timeout': [],           # Called for timeout events
            'perf': [],              # Called for performance events
            'debug': [],             # Called for debug/trace events
            
            # Error event types
            'slverr': [],            # Called for slave error events
            'decerr': [],            # Called for decode error events
            'addr_timeout': [],      # Called for address timeout events
            'data_timeout': [],      # Called for data timeout events
            'resp_timeout': [],      # Called for response timeout events
            'data_orphan': [],       # Called for data orphan events
            'resp_orphan': [],       # Called for response orphan events
            'protocol': [],          # Called for protocol violation events
            
            # Performance metric types
            'perf_latency': [],      # Called for latency metrics
            'perf_throughput': [],   # Called for throughput metrics
            'perf_utilization': [],  # Called for utilization metrics
            'perf_count': [],        # Called for transaction count metrics
            'perf_error_rate': [],   # Called for error rate metrics
        }
        
        # Set up monitor callback
        self.components.add_monitor_callback(self._handle_packet)
        
        # Statistics - expanded to match all types in axi_errmon_types.sv
        self.stats = {
            'total_events': 0,
            'error_events': 0,
            'completion_events': 0,
            'threshold_events': 0,
            'timeout_events': 0,
            'perf_events': 0,
            'debug_events': 0,
            
            # Error event counters
            'slverr_events': 0,
            'decerr_events': 0,
            'addr_timeout_events': 0,
            'data_timeout_events': 0,
            'resp_timeout_events': 0,
            'data_orphan_events': 0,
            'resp_orphan_events': 0,
            'protocol_events': 0,
            'trans_complete_events': 0,
            
            # Performance metric counters
            'perf_latency_events': 0,
            'perf_throughput_events': 0,
            'perf_utilization_events': 0,
            'perf_count_events': 0,
            'perf_error_rate_events': 0,
        }
    
    def _handle_packet(self, packet):
        """
        Handle a monitored packet.
        
        Args:
            packet: GAXIPacket from the monitor
        """
        # Extract fields from the consolidated packet
        if hasattr(packet, 'intrbus_packet'):
            fields = extract_packet_fields(packet.intrbus_packet)
        else:
            # Fallback to individual fields
            fields = {
                'packet_type': getattr(packet, 'packet_type', 0),
                'event_code': getattr(packet, 'event_code', 0),
                'channel_id': getattr(packet, 'channel_id', 0),
                'unit_id': getattr(packet, 'unit_id', 0),
                'agent_id': getattr(packet, 'agent_id', 0),
                'addr': getattr(packet, 'addr', 0)
            }
        
        # Update statistics
        self.stats['total_events'] += 1
        
        # Determine packet type and update specific statistics
        if fields['packet_type'] == 0x0:  # ERROR
            self.stats['error_events'] += 1
            
            # Check specific error types
            if fields['event_code'] == 0x1:  # ADDR_TIMEOUT
                self.stats['addr_timeout_events'] += 1
                self._call_callbacks('addr_timeout', packet)
            
            elif fields['event_code'] == 0x2:  # DATA_TIMEOUT
                self.stats['data_timeout_events'] += 1
                self._call_callbacks('data_timeout', packet)
            
            elif fields['event_code'] == 0x3:  # RESP_TIMEOUT
                self.stats['resp_timeout_events'] += 1
                self._call_callbacks('resp_timeout', packet)
            
            elif fields['event_code'] == 0x4:  # RESP_SLVERR
                self.stats['slverr_events'] += 1
                self._call_callbacks('slverr', packet)
            
            elif fields['event_code'] == 0x5:  # RESP_DECERR
                self.stats['decerr_events'] += 1
                self._call_callbacks('decerr', packet)
                
            elif fields['event_code'] == 0x6:  # DATA_ORPHAN
                self.stats['data_orphan_events'] += 1
                self._call_callbacks('data_orphan', packet)
                
            elif fields['event_code'] == 0x7:  # RESP_ORPHAN
                self.stats['resp_orphan_events'] += 1
                self._call_callbacks('resp_orphan', packet)
                
            elif fields['event_code'] == 0x8:  # PROTOCOL
                self.stats['protocol_events'] += 1
                self._call_callbacks('protocol', packet)
            
            # Call error callbacks for all error types
            self._call_callbacks('error', packet)
        
        elif fields['packet_type'] == 0x1:  # COMPLETION
            self.stats['completion_events'] += 1
            
            # Check for transaction complete event code
            if fields['event_code'] == 0x9:  # TRANS_COMPLETE
                self.stats['trans_complete_events'] += 1
            
            self._call_callbacks('completion', packet)
            
        elif fields['packet_type'] == 0x2:  # THRESHOLD
            self.stats['threshold_events'] += 1
            self._call_callbacks('threshold', packet)
            
        elif fields['packet_type'] == 0x3:  # TIMEOUT
            self.stats['timeout_events'] += 1
            self._call_callbacks('timeout', packet)
            
        elif fields['packet_type'] == 0x4:  # PERF
            self.stats['perf_events'] += 1
            self._call_callbacks('perf', packet)
            
        elif fields['packet_type'] == 0xF:  # DEBUG
            self.stats['debug_events'] += 1
            self._call_callbacks('debug', packet)
        
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
            callback(packet)
    
    def add_callback(self, callback, category='all'):
        """
        Add a callback for specific packet types.
        
        Args:
            callback: Function to call when a matching packet is monitored
            category: Which packets to monitor. One of:
                      'all', 'error', 'completion', 'threshold', 'timeout', 'perf', 'debug',
                      'slverr', 'decerr', 'addr_timeout', 'data_timeout', 'resp_timeout',
                      'data_orphan', 'resp_orphan', 'protocol',
                      'perf_latency', 'perf_throughput', 'perf_utilization', 'perf_count', 'perf_error_rate'
        """
        if category in self.callbacks:
            self.callbacks[category].append(callback)
        else:
            raise ValueError(f"Unknown callback category: {category}")
    
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
    
    async def reset_bus(self):
        """Reset the bus interfaces"""
        await self.components.reset_bus()
    
    def clear_monitor_queue(self):
        """Clear the monitor's queue of observed packets"""
        self.components.clear_monitor_queue()
