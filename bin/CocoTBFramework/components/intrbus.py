"""
Interrupt Bus Components for AXI/AXI-Lite Error Monitoring

This module provides field configurations and components for working with
the AXI interrupt bus framework. It includes:
1. Field configurations for interrupt packets
2. Master/slave/monitor components for the interrupt bus
"""

from .shared.field_config import FieldConfig, FieldDefinition
from .shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket


def create_intrbus_field_config(addr_width=38, packet_type_width=4, event_code_width=4,
                               channel_width=6, unit_id_width=4, agent_id_width=8):
    """
    Create a field configuration for the interrupt bus packet format.

    The interrupt bus packet is structured as follows:
    - packet_type: 4 bits  [63:60] (error, completion, threshold, etc.)
    - event_code:  4 bits  [59:56] (specific error or event code)
    - channel_id:  6 bits  [55:50] (channel ID and AXI ID)
    - unit_id:     4 bits  [49:46] (subsystem identifier)
    - agent_id:    8 bits  [45:38] (module identifier)
    - addr:        38 bits [37:0]  (address related to event)

    Args:
        addr_width: Width of the address field (default: 38)
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

    # Add fields
    field_config.add_field(FieldDefinition(
        name="packet_type",
        bits=packet_type_width,
        default=0,
        format="hex",
        display_width=1,
        description="Packet Type"
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
        name="channel_id",
        bits=channel_width,
        default=0,
        format="hex",
        display_width=2,
        description="Channel ID"
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
        name="agent_id",
        bits=agent_id_width,
        default=0,
        format="hex",
        display_width=2,
        description="Agent ID"
    ))

    field_config.add_field(FieldDefinition(
        name="addr",
        bits=addr_width,
        default=0,
        format="hex",
        display_width=8,
        description="Address"
    ))

    # Set packet type encoding
    field_config.set_encoding("packet_type", {
        0x0: "ERROR",       # Error event
        0x1: "COMPLETION",  # Transaction completion
        0x2: "THRESHOLD",   # Threshold crossed
        0x3: "TIMEOUT",     # Timeout event
        0xF: "DEBUG"        # Debug/trace event
    })

    # Set event code encoding (based on intrbus_types.sv)
    field_config.set_encoding("event_code", {
        0x0: "NONE",           # No event
        0x1: "ADDR_TIMEOUT",   # Address channel timeout
        0x2: "DATA_TIMEOUT",   # Data channel timeout
        0x3: "RESP_TIMEOUT",   # Response channel timeout
        0x4: "RESP_SLVERR",    # Error response (SLVERR)
        0x5: "RESP_DECERR",    # Error response (DECERR)
        0x6: "DATA_ORPHAN",    # Data without address
        0x7: "RESP_ORPHAN",    # Response without transaction
        0x8: "PROTOCOL",       # Protocol violation
        0xF: "USER_DEFINED"    # User-defined event
    })

    return field_config


class IntrBusComponents:
    """
    Combined components for the interrupt bus, providing master, slave, and monitor functionality.

    This class creates and manages the components needed to interface with the AXI interrupt bus,
    including field configurations and signal mappings.
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

        # Set up signal names with optional prefix
        self.signal_prefix = signal_prefix
        self.valid_signal = f"{signal_prefix}intrbus_valid"
        self.ready_signal = f"{signal_prefix}intrbus_ready"
        self.packet_signal = f"{signal_prefix}intrbus_packet"

        # Set up signal mappings for master
        self.master_signal_map = {
            'm2s_valid': self.valid_signal,
            's2m_ready': self.ready_signal
        }
        self.master_optional_signal_map = {
            'm2s_pkt': self.packet_signal
        }

        # Set up signal mappings for slave
        self.slave_signal_map = {
            'm2s_valid': self.valid_signal,
            's2m_ready': self.ready_signal
        }
        self.slave_optional_signal_map = {
            'm2s_pkt': self.packet_signal
        }

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

        # Create master for driving interrupt packets
        self.master = GAXIMaster(
            self.dut, f'{self.title_prefix}Master', '', self.clock,
            field_config=self.field_config,
            randomizer=self.randomizer,
            log=self.log,
            signal_map=self.master_signal_map,
            optional_signal_map=self.master_optional_signal_map
        )

        # Create slave for receiving interrupt packets
        self.slave = GAXISlave(
            self.dut, f'{self.title_prefix}Slave', '', self.clock,
            field_config=self.field_config,
            randomizer=self.randomizer,
            log=self.log,
            signal_map=self.slave_signal_map,
            optional_signal_map=self.slave_optional_signal_map
        )

        # Create monitor for tracking interrupt packets
        self.monitor = GAXIMonitor(
            self.dut, f'{self.title_prefix}Monitor', '', self.clock,
            field_config=self.field_config,
            is_slave=True,  # Monitor from slave perspective
            log=self.log,
            signal_map=self.slave_signal_map,
            optional_signal_map=self.slave_optional_signal_map
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

    async def send_error_packet(self, error_type, event_code, channel_id, unit_id, agent_id, addr):
        """
        Send an error packet through the master.

        Args:
            error_type: Packet type (usually 0 for ERROR)
            event_code: Specific error code
            channel_id: Channel ID
            unit_id: Unit ID
            agent_id: Agent ID
            addr: Address associated with the error

        Returns:
            The sent packet
        """
        packet = GAXIPacket(self.field_config)
        packet.packet_type = error_type
        packet.event_code = event_code
        packet.channel_id = channel_id
        packet.unit_id = unit_id
        packet.agent_id = agent_id
        packet.addr = addr

        await self.master.send(packet)
        return packet

    async def send_timeout_packet(self, timeout_type, channel_id, unit_id, agent_id, addr):
        """
        Send a timeout packet through the master.

        Args:
            timeout_type: Type of timeout (1=ADDR_TIMEOUT, 2=DATA_TIMEOUT, 3=RESP_TIMEOUT)
            channel_id: Channel ID
            unit_id: Unit ID
            agent_id: Agent ID
            addr: Address associated with the timeout

        Returns:
            The sent packet
        """
        return await self.send_error_packet(
            error_type=0,  # ERROR packet type
            event_code=timeout_type,
            channel_id=channel_id,
            unit_id=unit_id,
            agent_id=agent_id,
            addr=addr
        )

    async def send_completion_packet(self, channel_id, unit_id, agent_id, addr):
        """
        Send a completion packet through the master.

        Args:
            channel_id: Channel ID
            unit_id: Unit ID
            agent_id: Agent ID
            addr: Address associated with the completed transaction

        Returns:
            The sent packet
        """
        return await self.send_error_packet(
            error_type=1,  # COMPLETION packet type
            event_code=0,  # No event
            channel_id=channel_id,
            unit_id=unit_id,
            agent_id=agent_id,
            addr=addr
        )

    def format_event(self, packet):
        """
        Format an event packet into a human-readable description.

        Args:
            packet: GAXIPacket containing an interrupt event

        Returns:
            String description of the event
        """
        # Get decoded field values
        packet_type = self.field_config._get_encoding("packet_type", packet.packet_type)
        event_code = self.field_config._get_encoding("event_code", packet.event_code)

        # Format the event description
        event_desc = f"{packet_type}"
        if packet.packet_type == 0:  # ERROR
            event_desc += f": {event_code}"

        # Add details
        details = (
            f"Channel: 0x{packet.channel_id:X}, "
            f"Unit: 0x{packet.unit_id:X}, "
            f"Agent: 0x{packet.agent_id:X}, "
            f"Address: 0x{packet.addr:X}"
        )

        return f"{event_desc} - {details}"


class AXIIntrBusMonitor:
    """
    Specialized monitor for AXI interrupt bus packets.

    This class provides a higher-level interface for monitoring AXI-specific
    interrupt packets, with methods for filtering by specific error types.
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
        self.components.add_monitor_callback(self._handle_packet)

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
        Handle a monitored packet.

        Args:
            packet: GAXIPacket from the monitor
        """
        # Update statistics
        self.stats['total_events'] += 1

        # Determine event type and update specific statistics
        if packet.packet_type == 0:  # ERROR
            self.stats['error_events'] += 1

            # Check specific error types
            if packet.event_code == 0x1:  # ADDR_TIMEOUT
                self.stats['addr_timeout_events'] += 1
                self.stats['timeout_events'] += 1
                self._call_callbacks('addr_timeout', packet)
                self._call_callbacks('timeout', packet)

            elif packet.event_code == 0x2:  # DATA_TIMEOUT
                self.stats['data_timeout_events'] += 1
                self.stats['timeout_events'] += 1
                self._call_callbacks('data_timeout', packet)
                self._call_callbacks('timeout', packet)

            elif packet.event_code == 0x3:  # RESP_TIMEOUT
                self.stats['resp_timeout_events'] += 1
                self.stats['timeout_events'] += 1
                self._call_callbacks('resp_timeout', packet)
                self._call_callbacks('timeout', packet)

            elif packet.event_code == 0x4:  # RESP_SLVERR
                self.stats['slverr_events'] += 1
                self._call_callbacks('slverr', packet)

            elif packet.event_code == 0x5:  # RESP_DECERR
                self.stats['decerr_events'] += 1
                self._call_callbacks('decerr', packet)

            # Call error callbacks for all error types
            self._call_callbacks('error', packet)

        elif packet.packet_type == 0x1:  # COMPLETION
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
            callback(packet)

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

        # Add callbacks
        def print_all_events(packet):
            print(f"Event: {intrbus.components.format_event(packet)}")

        def print_error_events(packet):
            print(f"ERROR: {intrbus.components.format_event(packet)}")

        intrbus.add_callback(print_all_events, 'all')
        intrbus.add_callback(print_error_events, 'error')

        # Reset the bus
        await intrbus.reset_bus()

        # Send some test packets
        await intrbus.components.send_timeout_packet(
            timeout_type=1,  # ADDR_TIMEOUT
            channel_id=0x10,
            unit_id=0x9,
            agent_id=0x99,
            addr=0x12345678
        )

        await intrbus.components.send_error_packet(
            error_type=0,  # ERROR
            event_code=4,  # RESP_SLVERR
            channel_id=0x20,
            unit_id=0x9,
            agent_id=0x99,
            addr=0x87654321
        )

        await intrbus.components.send_completion_packet(
            channel_id=0x30,
            unit_id=0x9,
            agent_id=0x99,
            addr=0xABCDEF01
        )

        # Wait for all packets to be processed
        await Timer(100, units='ns')

        # Check statistics
        stats = intrbus.get_stats()
        print(f"Statistics: {stats}")
