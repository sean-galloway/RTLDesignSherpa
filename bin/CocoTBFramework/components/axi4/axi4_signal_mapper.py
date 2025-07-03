"""
AXI4 Signal Mapper - Clean signal mapping for AXI4 that works with enhanced GAXI patterns.

This is the lowest level component that handles the mapping from AXI4 signal names
to GAXI parameters that work with the updated SignalResolver.

Key insight: The SignalResolver now includes pkt_prefix in control signals:
    '{prefix}{in_prefix}{pkt_prefix}{bus_name}wr_valid',
    '{prefix}{in_prefix}{pkt_prefix}{bus_name}valid',
    '{prefix}{in_prefix}{pkt_prefix}{bus_name}m2s_valid',

Strategy: Use your working parameter approach consistently.
"""

from typing import Dict, List


class AXI4SignalMapper:
    """
    Clean signal mapping for AXI4 that works with enhanced GAXI patterns.

    Maps AXI4 signal conventions to GAXI parameter combinations that will
    be resolved by the updated SignalResolver.
    """

    # AXI4 to GAXI protocol mapping for each channel
    AXI4_PROTOCOL_MAP = {
        # Master-driven channels use gaxi_master
        'AW': 'gaxi_master',  # Address Write
        'W':  'gaxi_master',  # Write Data
        'AR': 'gaxi_master',  # Address Read

        # Slave-driven channels use gaxi_slave (from master's perspective)
        'B': 'gaxi_slave',    # Write Response
        'R': 'gaxi_slave',    # Read Data + Response
    }

    @staticmethod
    def get_channel_gaxi_params(axi4_prefix: str, channel: str,
                                bus_name: str = "", in_prefix: str = "", out_prefix: str = "") -> Dict[str, str]:
        """
        Convert AXI4 prefix and channel to GAXI parameters for SignalResolver.

        Args:
            axi4_prefix: AXI4 prefix like 'm_axi', 's_axi'
            channel: AXI4 channel like 'AW', 'AR', 'W', 'R', 'B'
            bus_name: Optional bus identifier
            in_prefix: Input prefix override (usually empty for AXI4)
            out_prefix: Output prefix override (usually empty for AXI4)

        Returns:
            Dictionary of GAXI parameters for SignalResolver

        Example:
            get_channel_gaxi_params('m_axi', 'AW') returns:
            {
                'prefix': 'm_axi_',
                'pkt_prefix': 'aw',
                'in_prefix': '',
                'out_prefix': '',
                'bus_name': '',
                'protocol_type': 'gaxi_master'
            }

            This will match patterns like: m_axi_awvalid, m_axi_awready
        """
        # Ensure prefix has trailing underscore for pattern matching
        if axi4_prefix and not axi4_prefix.endswith('_'):
            prefix = axi4_prefix + '_'
        else:
            prefix = axi4_prefix or ''

        # Get protocol type for this channel
        protocol_type = AXI4SignalMapper.AXI4_PROTOCOL_MAP.get(channel)
        if not protocol_type:
            raise ValueError(f"Unknown AXI4 channel: {channel}")

        return {
            'prefix': prefix,                    # 'm_axi_', 's_axi_'
            'pkt_prefix': channel.lower(),       # 'aw', 'ar', 'w', 'r', 'b'
            'in_prefix': in_prefix,              # Usually empty for AXI4
            'out_prefix': out_prefix,            # Usually empty for AXI4
            'bus_name': bus_name,                # Usually empty
            'protocol_type': protocol_type       # 'gaxi_master' or 'gaxi_slave'
        }

    @staticmethod
    def get_expected_axi4_signals(axi4_prefix: str, channel: str, bus_name: str = "") -> Dict[str, str]:
        """
        Get the expected AXI4 signal names for verification/debugging.

        Args:
            axi4_prefix: AXI4 prefix like 'm_axi', 's_axi'
            channel: AXI4 channel like 'AW', 'AR', 'W', 'R', 'B'
            bus_name: Optional bus identifier

        Returns:
            Dictionary with expected signal names

        Example:
            get_expected_axi4_signals('m_axi', 'AW') returns:
            {
                'valid': 'm_axi_awvalid',
                'ready': 'm_axi_awready',
                'data_signals': ['m_axi_awid', 'm_axi_awaddr', ...]
            }
        """
        # Build base prefix
        base = axi4_prefix.rstrip('_')  # Remove trailing underscore if present
        if bus_name:
            base = f"{base}_{bus_name}"

        ch = channel.lower()

        return {
            'valid': f'{base}_{ch}valid',
            'ready': f'{base}_{ch}ready',
            'data_signals': AXI4SignalMapper._get_channel_data_signals(base, ch)
        }

    @staticmethod
    def _get_channel_data_signals(base: str, channel: str) -> List[str]:
        """Get expected data signal names for each AXI4 channel."""
        data_signals = {
            'aw': ['awid', 'awaddr', 'awlen', 'awsize', 'awburst', 'awlock', 'awcache', 'awprot', 'awqos', 'awregion', 'awuser'],
            'w':  ['wdata', 'wstrb', 'wlast', 'wuser'],
            'b':  ['bid', 'bresp', 'buser'],
            'ar': ['arid', 'araddr', 'arlen', 'arsize', 'arburst', 'arlock', 'arcache', 'arprot', 'arqos', 'arregion', 'aruser'],
            'r':  ['rid', 'rdata', 'rresp', 'rlast', 'ruser']
        }

        return [f'{base}_{signal}' for signal in data_signals.get(channel, [])]

    @staticmethod
    def validate_axi4_channel(channel: str) -> bool:
        """Validate that the channel is a valid AXI4 channel."""
        return channel in AXI4SignalMapper.AXI4_PROTOCOL_MAP

    @staticmethod
    def get_all_axi4_channels() -> List[str]:
        """Get list of all valid AXI4 channels."""
        return list(AXI4SignalMapper.AXI4_PROTOCOL_MAP.keys())

    @staticmethod
    def is_master_driven_channel(channel: str) -> bool:
        """Check if channel is driven by master."""
        return AXI4SignalMapper.AXI4_PROTOCOL_MAP.get(channel) == 'gaxi_master'

    @staticmethod
    def is_slave_driven_channel(channel: str) -> bool:
        """Check if channel is driven by slave."""
        return AXI4SignalMapper.AXI4_PROTOCOL_MAP.get(channel) == 'gaxi_slave'

    @staticmethod
    def preview_signal_mapping(axi4_prefix: str, channels: List[str], bus_name: str = "") -> None:
        """
        Preview what signal mappings will be generated for debugging.

        Args:
            axi4_prefix: AXI4 prefix like 'm_axi', 's_axi'
            channels: List of channels to preview
            bus_name: Optional bus identifier

        Prints the expected signal mappings for verification.
        """
        print(f"\nAXI4 Signal Mapping Preview")
        print(f"AXI4 Prefix: '{axi4_prefix}'")
        print(f"Bus Name: '{bus_name}'")
        print("-" * 60)

        for channel in channels:
            if not AXI4SignalMapper.validate_axi4_channel(channel):
                print(f"\n❌ {channel}: INVALID CHANNEL")
                continue

            print(f"\n✅ {channel} Channel:")

            # Show GAXI parameters
            gaxi_params = AXI4SignalMapper.get_channel_gaxi_params(axi4_prefix, channel, bus_name)
            print(f"   GAXI Parameters:")
            for key, value in gaxi_params.items():
                print(f"     {key}: '{value}'")

            # Show expected signals
            expected = AXI4SignalMapper.get_expected_axi4_signals(axi4_prefix, channel, bus_name)
            print(f"   Expected Signals:")
            print(f"     valid: {expected['valid']}")
            print(f"     ready: {expected['ready']}")
            print(f"     data: {len(expected['data_signals'])} signals")


# Example usage for testing
if __name__ == "__main__":
    # Test the signal mapper
    print("AXI4 Signal Mapper - Testing")
    print("=" * 50)

    # Test basic mapping
    params = AXI4SignalMapper.get_channel_gaxi_params('m_axi', 'AW')
    print(f"AW Channel GAXI params: {params}")

    expected = AXI4SignalMapper.get_expected_axi4_signals('m_axi', 'AW')
    print(f"AW Channel expected signals: {expected}")

    # Test preview
    AXI4SignalMapper.preview_signal_mapping('m_axi', ['AW', 'W', 'B'], '')
