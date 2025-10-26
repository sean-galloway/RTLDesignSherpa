# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: gaxi_factories
# Purpose: Updated GAXI Factories - FIXED to match TB instantiation patterns
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Updated GAXI Factories - FIXED to match TB instantiation patterns

This version fixes the parameter handling to match how the TB actually creates
components, with proper defaults for signal prefixes and naming.

All existing APIs are preserved exactly as before.
"""

from ..shared.memory_model import MemoryModel
from ..shared.field_config import FieldConfig
from .gaxi_master import GAXIMaster
from .gaxi_slave import GAXISlave
from .gaxi_monitor import GAXIMonitor
from CocoTBFramework.scoreboards.gaxi_scoreboard import GAXIScoreboard


def get_default_field_config(data_width=32):
    """
    Get standard field configuration for GAXI protocol.

    Args:
        data_width: Data width in bits

    Returns:
        FieldConfig object for standard data field
    """
    return FieldConfig.create_data_only(data_width)


def create_gaxi_master(dut, title, prefix, clock, field_config=None, packet_class=None,
                        randomizer=None, memory_model=None,
                        memory_fields=None, log=None, signal_map=None,
                        optional_signal_map=None, field_mode=False, multi_sig=False,
                        mode='skid', bus_name='', pkt_prefix='',
                        **kwargs):
    """
    Create a GAXI Master component with simplified configuration.

    All existing parameters are preserved and passed through exactly as before.
    

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        field_config: Field configuration (default: standard data field)
        packet_class: Packet class to use
        randomizer: Timing randomizer (default: standard master constraints)
        memory_model: Memory model for transactions (optional)
        memory_fields: Field mapping for memory operations (unused - kept for compatibility)
        log: Logger instance (default: dut's logger)
        signal_map: Signal mapping (unused - kept for compatibility)
        optional_signal_map: Optional signal mapping (unused - kept for compatibility)
        field_mode: Field mode (unused - kept for compatibility)
        multi_sig: Whether using multi-signal mode
        mode: Operating mode ('skid', 'fifo_mux', 'fifo_flop')
        bus_name: Bus/channel name
        pkt_prefix: Packet field prefix
        **kwargs: Additional arguments

    Returns:
        GAXIMaster instance
    """
    # Use default field config if none provided
    if field_config is None:
        field_config = get_default_field_config()

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create master - pass through all parameters explicitly like TB does
    return GAXIMaster(
        dut=dut,
        title=title,
        prefix=prefix,
        clock=clock,
        field_config=field_config,
        randomizer=randomizer,
        memory_model=memory_model,
        log=log,
        mode=mode,
        bus_name=bus_name,
        pkt_prefix=pkt_prefix,
        multi_sig=multi_sig,
        **kwargs  # Pass through remaining parameters
    )


def create_gaxi_slave(dut, title, prefix, clock, field_config=None, field_mode=False, packet_class=None,
                        randomizer=None, memory_model=None,
                        memory_fields=None, log=None, mode='skid',
                        signal_map=None, optional_signal_map=None, multi_sig=False,
                        bus_name='', pkt_prefix='',
                        **kwargs):
    """
    Create a GAXI Slave component with simplified configuration.

    All existing parameters are preserved and passed through exactly as before.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        field_config: Field configuration (default: standard data field)
        field_mode: Field mode (unused - kept for compatibility)
        packet_class: Packet class to use
        randomizer: Timing randomizer (default: standard slave constraints)
        memory_model: Memory model for transactions (optional)
        memory_fields: Field mapping for memory operations (unused - kept for compatibility)
        log: Logger instance (default: dut's logger)
        mode: Operating mode ('skid', 'fifo_mux', 'fifo_flop')
        signal_map: Signal mapping (unused - kept for compatibility)
        optional_signal_map: Optional signal mapping (unused - kept for compatibility)
        multi_sig: Whether using multi-signal mode
        bus_name: Bus/channel name
        pkt_prefix: Packet field prefix
        **kwargs: Additional arguments

    Returns:
        GAXISlave instance
    """
    # Use default field config if none provided
    if field_config is None:
        field_config = get_default_field_config()

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create slave - pass through all parameters explicitly like TB does
    return GAXISlave(
        dut=dut,
        title=title,
        prefix=prefix,
        clock=clock,
        field_config=field_config,
        mode=mode,
        randomizer=randomizer,
        memory_model=memory_model,
        log=log,
        bus_name=bus_name,
        pkt_prefix=pkt_prefix,
        multi_sig=multi_sig,
        **kwargs  # Pass through remaining parameters
    )


def create_gaxi_monitor(dut, title, prefix, clock, field_config=None,
                        is_slave=False, log=None, mode='skid',
                        bus_name='', pkt_prefix='',
                        multi_sig=False,
                        **kwargs):
    """
    Create a GAXI Monitor component with simplified configuration.

    All existing parameters are preserved and passed through exactly as before.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        field_config: Field configuration (default: standard data field)
        field_mode: Field mode (unused - kept for compatibility)
        packet_class: Packet class to use
        is_slave: If True, monitor slave side; if False, monitor master side
        log: Logger instance (default: dut's logger)
        mode: Operating mode ('skid', 'fifo_mux', 'fifo_flop')
        signal_map: Signal mapping (unused - kept for compatibility)
        optional_signal_map: Optional signal mapping (unused - kept for compatibility)
        multi_sig: Whether using multi-signal mode
        bus_name: Bus/channel name
        pkt_prefix: Packet field prefix
        **kwargs: Additional arguments

    Returns:
        GAXIMonitor instance
    """
    # Use default field config if none provided
    if field_config is None:
        field_config = get_default_field_config()

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create monitor - pass through all parameters explicitly like TB does
    return GAXIMonitor(
        dut=dut,
        title=title,
        prefix=prefix,
        clock=clock,
        field_config=field_config,
        is_slave=is_slave,
        mode=mode,
        log=log,
        bus_name=bus_name,
        pkt_prefix=pkt_prefix,
        multi_sig=multi_sig,
        **kwargs  # Pass through remaining parameters
    )


def create_gaxi_scoreboard(name, field_config=None, log=None):
    """
    Create a GAXI Scoreboard with simplified configuration.

    Args:
        name: Scoreboard name
        field_config: Field configuration (default: standard data field)
        log: Logger instance

    Returns:
        GAXIScoreboard instance
    """
    # Use default field config if none provided
    if field_config is None:
        field_config = get_default_field_config()

    # Create scoreboard (unchanged - already simple)
    return GAXIScoreboard(name, field_config, log=log)


def create_gaxi_components(dut, clock, title_prefix="", field_config=None, field_mode=False, packet_class=None,
                            memory_model=None, log=None,
                            mode='skid', signal_map=None, optional_signal_map=None, multi_sig=False,
                            bus_name='', pkt_prefix='',
                            **kwargs):
    """
    Create a complete set of GAXI components (master, slave, monitors, scoreboard).

    All existing parameters are preserved and passed through exactly as before.

    Args:
        dut: Device under test
        clock: Clock signal
        title_prefix: Prefix for component titles
        field_config: Field configuration (default: standard data field)
        field_mode: Field mode (unused - kept for compatibility)
        packet_class: Packet class to use
        memory_model: Memory model for components (auto-created if None)
        log: Logger instance
        mode: Operating mode for slave/monitor
        signal_map: Signal mapping (unused - kept for compatibility)
        optional_signal_map: Optional signal mapping (unused - kept for compatibility)
        multi_sig: Whether using multi-signal mode
        bus_name: Bus/channel name
        pkt_prefix: Packet field prefix
        **kwargs: Additional configuration passed to all components

    Returns:
        Dictionary containing all created components
    """
    # Use default field config if none provided
    if field_config is None:
        field_config = get_default_field_config()

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create memory model if needed but not provided - use base MemoryModel directly
    if memory_model is None:
        memory_model = MemoryModel(
            num_lines=1024,
            bytes_per_line=4,  # 32-bit default
            log=log
        )

    # Create components using simplified factories with consistent parameters
    master = create_gaxi_master(
        dut, f"{title_prefix}Master", "", clock,
        field_config=field_config,
        field_mode=field_mode,
        packet_class=packet_class,
        memory_model=memory_model,
        log=log,
        mode=mode,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map,
        multi_sig=multi_sig,
        bus_name=bus_name,
        pkt_prefix=pkt_prefix,
        **kwargs
    )

    slave = create_gaxi_slave(
        dut, f"{title_prefix}Slave", "", clock,
        field_config=field_config,
        field_mode=field_mode,
        packet_class=packet_class,
        memory_model=memory_model,
        log=log,
        mode=mode,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map,
        multi_sig=multi_sig,
        bus_name=bus_name,
        **kwargs
    )

    master_monitor = create_gaxi_monitor(
        dut, f"{title_prefix}MasterMonitor", "", clock,
        field_config=field_config,
        field_mode=field_mode,
        packet_class=packet_class,
        is_slave=False,
        log=log,
        mode=mode,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map,
        multi_sig=multi_sig,
        bus_name=bus_name,
        pkt_prefix=pkt_prefix,
        **kwargs
    )

    slave_monitor = create_gaxi_monitor(
        dut, f"{title_prefix}SlaveMonitor", "", clock,
        field_config=field_config,
        field_mode=field_mode,
        packet_class=packet_class,
        is_slave=True,
        log=log,
        mode=mode,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map,
        multi_sig=multi_sig,
        bus_name=bus_name,
        pkt_prefix=pkt_prefix,
        **kwargs
    )

    scoreboard = create_gaxi_scoreboard(
        f"{title_prefix}Scoreboard",
        field_config=field_config,
        log=log
    )

    # Return all components - same format as before
    return {
        'master': master,
        'slave': slave,
        'master_monitor': master_monitor,
        'slave_monitor': slave_monitor,
        'scoreboard': scoreboard,
        'memory_model': memory_model
    }


def create_gaxi_system(dut, clock, title_prefix="", field_config=None,
                        memory_model=None, log=None,
                        bus_name='', pkt_prefix='',
                        **kwargs):
    """
    Create a complete GAXI system with all components - alias for create_gaxi_components.

    This maintains backward compatibility while providing a cleaner name.

    Args:
        dut: Device under test
        clock: Clock signal
        title_prefix: Prefix for component titles
        field_config: Field configuration (default: standard data field)
        memory_model: Shared memory model (auto-created if None)
        log: Logger instance (default: dut's logger)
        bus_name: Bus/channel name
        pkt_prefix: Packet field prefix
        **kwargs: Additional arguments passed to all components

    Returns:
        Dictionary containing all created components and shared resources
    """
    return create_gaxi_components(
        dut=dut,
        clock=clock,
        title_prefix=title_prefix,
        field_config=field_config,
        memory_model=memory_model,
        log=log,
        bus_name=bus_name,
        pkt_prefix=pkt_prefix,
        **kwargs
    )


def create_gaxi_test_environment(dut, clock, 
                                bus_name='', pkt_prefix='',
                                **kwargs):
    """
    Create a complete GAXI test environment ready for immediate use.

    This convenience function creates a full system with sensible defaults
    and commonly needed configurations for testing.

    Args:
        dut: Device under test
        clock: Clock signal
        bus_name: Bus/channel name
        pkt_prefix: Packet field prefix
        **kwargs: Configuration overrides

    Returns:
        Dictionary with complete test environment
    """
    # Extract common test parameters with defaults
    test_config = {
        'title_prefix': kwargs.pop('title_prefix', 'GAXI_'),
        'field_config': kwargs.pop('field_config', None),
        'data_width': kwargs.pop('data_width', 32),
        'memory_size': kwargs.pop('memory_size', 1024),
        'log': kwargs.pop('log', getattr(dut, '_log', None)),
    }

    # Create field config if not provided
    if test_config['field_config'] is None:
        test_config['field_config'] = get_default_field_config(test_config['data_width'])

    # Create memory model sized for test - use base MemoryModel directly
    memory_model = MemoryModel(
        num_lines=test_config['memory_size'],
        bytes_per_line=test_config['data_width'] // 8,
        log=test_config['log']
    )

    # Create complete system
    system = create_gaxi_system(
        dut=dut,
        clock=clock,
        title_prefix=test_config['title_prefix'],
        field_config=test_config['field_config'],
        memory_model=memory_model,
        log=test_config['log'],
        bus_name=bus_name,
        pkt_prefix=pkt_prefix,
        **kwargs  # Pass through remaining configuration
    )

    # Add test-specific conveniences
    system.update({
        'test_config': test_config,

        # Quick access to common operations
        'send_data': lambda data: system['master'].send(
            system['master'].create_packet(data=data)
        ),
        'read_memory': lambda addr: memory_model.read(addr, test_config['data_width'] // 8),
        'write_memory': lambda addr, data: memory_model.write(
            addr, memory_model.integer_to_bytearray(data, test_config['data_width'] // 8)
        ),

        # Statistics aggregation
        'get_all_stats': lambda: {
            comp_name: comp.get_stats()
            for comp_name, comp in system.items()
            if hasattr(comp, 'get_stats')
        }
    })

    return system


# Backward compatibility aliases - maintain existing API
get_gaxi_field_config = get_default_field_config
