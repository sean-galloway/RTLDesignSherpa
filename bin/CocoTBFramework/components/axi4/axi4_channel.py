"""
AXI4 Channel - Single channel wrapper around GAXI components.

This module provides the AXI4Channel class that wraps a single GAXI component
and provides AXI4-specific functionality while leveraging the working GAXI foundation.

Key Design Principles:
1. Composition over inheritance - wraps GAXI component
2. AXI4-specific semantics and validation
3. Clean interface for higher-level coordination
4. Preserves all GAXI functionality through delegation
"""

import time
from typing import Optional, Callable, Any, Dict, List
from ..gaxi.gaxi_factories import create_gaxi_master, create_gaxi_slave, create_gaxi_monitor
from .axi4_signal_mapper import AXI4SignalMapper
from .axi4_field_configs import AXI4FieldConfigHelper


class AXI4Channel:
    """
    Represents a single AXI4 channel backed by a GAXI component.

    This is a clean wrapper that handles AXI4-specific concerns while
    delegating the actual protocol handling to the underlying GAXI component.
    """

    def __init__(self, channel_name: str, gaxi_component, prefix: str,
                    field_config=None, log=None):
        """
        Initialize AXI4 Channel wrapper.

        Args:
            channel_name: AXI4 channel name ('AW', 'AR', 'W', 'R', 'B')
            gaxi_component: Underlying GAXI component (master/slave/monitor)
            prefix: AXI4 signal prefix like 'm_axi', 's_axi'
            field_config: Field configuration for this channel
            log: Logger instance
        """
        # Validate channel name
        if not AXI4SignalMapper.validate_axi4_channel(channel_name):
            raise ValueError(f"Invalid AXI4 channel: {channel_name}")

        self.channel_name = channel_name
        self.gaxi_component = gaxi_component
        self.prefix = prefix
        self.field_config = field_config
        self.log = log

        # AXI4-specific channel properties
        self.is_address_channel = channel_name in ['AW', 'AR']
        self.is_data_channel = channel_name in ['W', 'R']
        self.is_response_channel = channel_name in ['B', 'R']
        self.is_master_driven = AXI4SignalMapper.is_master_driven_channel(channel_name)
        self.is_slave_driven = AXI4SignalMapper.is_slave_driven_channel(channel_name)

        # Track channel statistics
        self._channel_stats = {
            'packets_sent': 0,
            'packets_received': 0,
            'last_packet_time': None,
            'first_packet_time': None,
            'total_active_time': 0,
            'channel_errors': 0
        }

        # Callback registry for packet events
        self._packet_callbacks = []
        self._error_callbacks = []

        # Set up monitoring if underlying component supports it
        self._setup_monitoring()

    def _setup_monitoring(self):
        """Set up monitoring hooks on the underlying GAXI component."""
        try:
            # Try to add callback for received packets
            if hasattr(self.gaxi_component, 'add_callback'):
                self.gaxi_component.add_callback(self._on_packet_received)
        except Exception as e:
            if self.log:
                self.log.debug(f"Could not set up monitoring for {self.channel_name}: {e}")

    def _on_packet_received(self, packet):
        """Handle packet received from underlying GAXI component."""
        # Update statistics
        self._channel_stats['packets_received'] += 1
        current_time = time.time()

        if self._channel_stats['first_packet_time'] is None:
            self._channel_stats['first_packet_time'] = current_time
        self._channel_stats['last_packet_time'] = current_time

        # Validate AXI4 protocol if packet supports it
        if hasattr(packet, 'validate_axi4_protocol'):
            try:
                is_valid, error_msg = packet.validate_axi4_protocol()
                if not is_valid:
                    self._channel_stats['channel_errors'] += 1
                    if self.log:
                        self.log.error(f"{self.channel_name} protocol violation: {error_msg}")

                    # Notify error callbacks
                    for callback in self._error_callbacks:
                        try:
                            callback(self.channel_name, packet, error_msg)
                        except Exception as e:
                            if self.log:
                                self.log.error(f"Error callback failed: {e}")
            except Exception as e:
                if self.log:
                    self.log.warning(f"Could not validate packet: {e}")

        # Notify packet callbacks
        for callback in self._packet_callbacks:
            try:
                callback(self.channel_name, packet)
            except Exception as e:
                if self.log:
                    self.log.error(f"Packet callback failed: {e}")

    async def send(self, packet):
        """
        Send a packet on this channel.

        Args:
            packet: Packet to send

        Returns:
            Result from underlying GAXI component

        Raises:
            ValueError: If trying to send on slave-driven channel
        """
        if not self.is_master_driven:
            raise ValueError(f"Cannot send on slave-driven channel {self.channel_name}")

        # Validate packet before sending
        if hasattr(packet, 'validate_axi4_protocol'):
            is_valid, error_msg = packet.validate_axi4_protocol()
            if not is_valid:
                raise ValueError(f"Invalid AXI4 packet for {self.channel_name}: {error_msg}")

        # Update statistics
        self._channel_stats['packets_sent'] += 1

        # Delegate to GAXI component
        if hasattr(self.gaxi_component, 'send'):
            return await self.gaxi_component.send(packet)
        else:
            raise NotImplementedError(f"Underlying GAXI component does not support sending")

    def add_callback(self, callback: Callable[[str, Any], None]):
        """
        Add callback for received packets.

        Args:
            callback: Function called with (channel_name, packet) when packet received

        Returns:
            Callback registration for removal
        """
        self._packet_callbacks.append(callback)
        return callback

    def remove_callback(self, callback: Callable[[str, Any], None]):
        """Remove a packet callback."""
        if callback in self._packet_callbacks:
            self._packet_callbacks.remove(callback)

    def add_error_callback(self, callback: Callable[[str, Any, str], None]):
        """
        Add callback for protocol errors.

        Args:
            callback: Function called with (channel_name, packet, error_msg) on errors
        """
        self._error_callbacks.append(callback)
        return callback

    def remove_error_callback(self, callback: Callable[[str, Any, str], None]):
        """Remove an error callback."""
        if callback in self._error_callbacks:
            self._error_callbacks.remove(callback)

    @property
    def stats(self) -> Dict[str, Any]:
        """
        Get channel statistics.

        Returns:
            Dictionary with channel-specific statistics
        """
        # Combine channel stats with underlying GAXI stats
        combined_stats = self._channel_stats.copy()

        if hasattr(self.gaxi_component, 'stats'):
            gaxi_stats = self.gaxi_component.stats
            if hasattr(gaxi_stats, '__dict__'):
                combined_stats.update(gaxi_stats.__dict__)
            elif isinstance(gaxi_stats, dict):
                combined_stats.update(gaxi_stats)

        return combined_stats

    @property
    def component_type(self) -> str:
        """Get the underlying GAXI component type."""
        return type(self.gaxi_component).__name__

    def get_expected_signals(self) -> Dict[str, str]:
        """Get expected signal names for this channel."""
        return AXI4SignalMapper.get_expected_axi4_signals(self.prefix, self.channel_name)

    def validate_signal_connectivity(self) -> Dict[str, Any]:
        """
        Validate that expected signals are properly connected.

        Returns:
            Dictionary with validation results
        """
        expected_signals = self.get_expected_signals()

        # Check if underlying GAXI component has signal validation
        if hasattr(self.gaxi_component, 'signal_resolver'):
            # Use signal resolver to check connectivity
            resolver = self.gaxi_component.signal_resolver
            if hasattr(resolver, 'validate_signals'):
                return resolver.validate_signals()

        # Fallback: basic validation
        return {
            'is_valid': True,
            'expected_signals': expected_signals,
            'missing_signals': [],
            'extra_signals': [],
            'message': "Signal validation not available for underlying component"
        }

    def get_debug_info(self) -> Dict[str, Any]:
        """
        Get comprehensive debug information about this channel.

        Returns:
            Dictionary with debug information
        """
        debug_info = {
            'channel_name': self.channel_name,
            'prefix': self.prefix,
            'component_type': self.component_type,
            'is_address_channel': self.is_address_channel,
            'is_data_channel': self.is_data_channel,
            'is_response_channel': self.is_response_channel,
            'is_master_driven': self.is_master_driven,
            'is_slave_driven': self.is_slave_driven,
            'stats': self.stats,
            'expected_signals': self.get_expected_signals(),
            'field_config': None,
            'callbacks_registered': len(self._packet_callbacks),
            'error_callbacks_registered': len(self._error_callbacks)
        }

        # Add field config info if available
        if self.field_config:
            debug_info['field_config'] = {
                'num_fields': len(self.field_config),
                'total_bits': self.field_config.get_total_bits(),
                'field_names': self.field_config.field_names()
            }

        # Add underlying component debug info if available
        if hasattr(self.gaxi_component, 'get_debug_info'):
            debug_info['gaxi_component'] = self.gaxi_component.get_debug_info()

        return debug_info

    def __str__(self) -> str:
        """String representation of the channel."""
        return f"AXI4Channel({self.channel_name}, {self.prefix}, {self.component_type})"

    def __repr__(self) -> str:
        """Detailed string representation."""
        return (f"AXI4Channel(channel_name='{self.channel_name}', "
                f"prefix='{self.prefix}', "
                f"component_type='{self.component_type}', "
                f"is_master_driven={self.is_master_driven})")


def create_axi4_channel(dut, clock, prefix: str, channel_name: str,
                        id_width: int = 8, addr_width: int = 32, data_width: int = 32, user_width: int = 1,
                        memory_model=None, timing_config=None, log=None, **kwargs) -> AXI4Channel:
    """
    Factory function to create a single AXI4 channel using GAXI foundation.

    This is the main factory function referenced in the ground-up design.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: AXI4 prefix like 'm_axi', 's_axi'
        channel_name: Channel like 'AW', 'AR', 'W', 'R', 'B'
        id_width: Width of ID fields
        addr_width: Width of address fields
        data_width: Width of data fields
        user_width: Width of user fields
        memory_model: Optional memory model for transactions
        timing_config: Optional timing configuration/randomizer
        log: Logger instance
        **kwargs: Additional arguments passed to GAXI component

    Returns:
        AXI4Channel object wrapping the appropriate GAXI component
    """
    # Validate inputs
    if not AXI4SignalMapper.validate_axi4_channel(channel_name):
        raise ValueError(f"Invalid AXI4 channel: {channel_name}")

    is_valid, errors = AXI4FieldConfigHelper.validate_axi4_widths(id_width, addr_width, data_width, user_width)
    if not is_valid:
        raise ValueError(f"Invalid field widths: {', '.join(errors)}")

    # Get GAXI parameters for this channel
    gaxi_params = AXI4SignalMapper.get_channel_gaxi_params(prefix, channel_name)

    # Create field configuration for this channel
    field_config = AXI4FieldConfigHelper.create_all_field_configs(
        id_width, addr_width, data_width, user_width, [channel_name]
    )[channel_name]

    # Determine GAXI component type and create it
    protocol_type = gaxi_params['protocol_type']

    # Common parameters for GAXI component creation
    gaxi_component_params = {
        'dut': dut,
        'title': f"{prefix}_{channel_name}",
        'clock': clock,
        'field_config': field_config,
        'memory_model': memory_model,
        'log': log,
        'prefix': gaxi_params['prefix'],
        'in_prefix': gaxi_params['in_prefix'],
        'out_prefix': gaxi_params['out_prefix'],
        'bus_name': gaxi_params['bus_name'],
        'pkt_prefix': gaxi_params['pkt_prefix'],
        **kwargs  # Pass through additional arguments
    }

    # Add timing configuration if provided
    if timing_config is not None:
        gaxi_component_params['randomizer'] = timing_config

    # Create the appropriate GAXI component
    if protocol_type == 'gaxi_master':
        gaxi_component = create_gaxi_master(**gaxi_component_params)
    elif protocol_type == 'gaxi_slave':
        gaxi_component = create_gaxi_slave(**gaxi_component_params)
    else:
        raise ValueError(f"Unknown protocol type: {protocol_type}")

    # Create and return the AXI4Channel wrapper
    return AXI4Channel(
        channel_name=channel_name,
        gaxi_component=gaxi_component,
        prefix=prefix,
        field_config=field_config,
        log=log
    )


# Example usage for testing
if __name__ == "__main__":
    print("AXI4 Channel - Testing")
    print("=" * 50)

    # Test signal mapping
    expected_signals = AXI4SignalMapper.get_expected_axi4_signals('m_axi', 'AW')
    print(f"Expected AW signals: {expected_signals}")

    # Test GAXI parameter mapping
    gaxi_params = AXI4SignalMapper.get_channel_gaxi_params('m_axi', 'AW')
    print(f"GAXI parameters for AW: {gaxi_params}")

    # Test channel properties
    for channel in ['AW', 'W', 'B', 'AR', 'R']:
        is_master = AXI4SignalMapper.is_master_driven_channel(channel)
        is_slave = AXI4SignalMapper.is_slave_driven_channel(channel)
        print(f"{channel}: master_driven={is_master}, slave_driven={is_slave}")
