# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axis_factories
# Purpose: AXIS Factory Functions - Component creation with consistent APIs
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIS Factory Functions - Component creation with consistent APIs

This module provides factory functions for creating AXIS components
with APIs similar to AXI4 factories for consistency.
"""

from typing import Dict, Any, Optional
from ..gaxi.gaxi_master import GAXIMaster
from ..gaxi.gaxi_slave import GAXISlave
from ..gaxi.gaxi_monitor import GAXIMonitor
from .axis_field_configs import AXISFieldConfigs


def create_axis_master(dut, clock, prefix="", data_width=32, id_width=8,
                      dest_width=4, user_width=1, log=None, **kwargs) -> Dict[str, Any]:
    """
    Create AXIS Master interface.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix ("m_axis_", "fub_axis_", etc.)
        data_width: Width of TDATA field
        id_width: Width of TID field
        dest_width: Width of TDEST field
        user_width: Width of TUSER field
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        Dictionary containing AXIS master components
    """
    # Create field configuration
    field_config = AXISFieldConfigs.create_axis_config_from_hw_params(
        data_width=data_width,
        id_width=id_width,
        dest_width=dest_width,
        user_width=user_width
    )

    # Create the master using GAXIMaster directly with AXIS protocol
    master = GAXIMaster(
        dut=dut,
        title=f"AXIS_Master_{prefix}",
        prefix=prefix,
        clock=clock,
        field_config=field_config,
        protocol_type='axis_master',  # Use AXIS protocol for proper signal mapping
        pkt_prefix="",  # AXIS is a single channel, no prefix needed
        multi_sig=True,  # Use multi-signal mode for AXIS fields
        log=log,
        **kwargs
    )

    # Return components in format expected by testbench
    return {
        'T': master,                # T channel master component
        'interface': master,        # High-level interface
        'master': master           # Direct access
    }


def create_axis_slave(dut, clock, prefix="", data_width=32, id_width=8,
                     dest_width=4, user_width=1, log=None, **kwargs) -> Dict[str, Any]:
    """
    Create AXIS Slave interface.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix ("s_axis_", "axis_", etc.)
        data_width: Width of TDATA field
        id_width: Width of TID field
        dest_width: Width of TDEST field
        user_width: Width of TUSER field
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        Dictionary containing AXIS slave components
    """
    # Create field configuration
    field_config = AXISFieldConfigs.create_axis_config_from_hw_params(
        data_width=data_width,
        id_width=id_width,
        dest_width=dest_width,
        user_width=user_width
    )

    # Create the slave using GAXISlave directly with AXIS protocol
    slave = GAXISlave(
        dut=dut,
        title=f"AXIS_Slave_{prefix}",
        prefix=prefix,
        clock=clock,
        field_config=field_config,
        protocol_type='axis_slave',  # Use AXIS protocol for proper signal mapping
        pkt_prefix="",  # AXIS is a single channel, no prefix needed
        multi_sig=True,  # Use multi-signal mode for AXIS fields
        log=log,
        **kwargs
    )

    # Return components in format expected by testbench
    return {
        'T': slave,                 # T channel slave component
        'interface': slave,         # High-level interface
        'slave': slave             # Direct access
    }


def create_axis_monitor(dut, clock, prefix="", data_width=32, id_width=8,
                       dest_width=4, user_width=1, is_slave=False,
                       log=None, **kwargs) -> Dict[str, Any]:
    """
    Create AXIS Monitor interface.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix ("s_axis_", "m_axis_", etc.)
        data_width: Width of TDATA field
        id_width: Width of TID field
        dest_width: Width of TDEST field
        user_width: Width of TUSER field
        is_slave: True if monitoring slave side, False for master side
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        Dictionary containing AXIS monitor components
    """
    # Create field configuration
    field_config = AXISFieldConfigs.create_axis_config_from_hw_params(
        data_width=data_width,
        id_width=id_width,
        dest_width=dest_width,
        user_width=user_width
    )

    # Create the monitor using GAXIMonitor directly with AXIS protocol
    protocol_type = 'axis_slave' if is_slave else 'axis_master'
    monitor = GAXIMonitor(
        dut=dut,
        title=f"AXIS_Monitor_{prefix}",
        prefix=prefix,
        clock=clock,
        field_config=field_config,
        protocol_type=protocol_type,  # Use AXIS protocol for proper signal mapping
        pkt_prefix="",  # AXIS is a single channel, no prefix needed
        multi_sig=True,  # Use multi-signal mode for AXIS fields
        log=log,
        **kwargs
    )

    # Return components in format expected by testbench
    return {
        'T': monitor,               # T channel monitor component
        'interface': monitor,       # High-level interface
        'monitor': monitor         # Direct access
    }


def create_axis_master_interface(dut, clock, prefix="", data_width=32,
                               id_width=8, dest_width=4, user_width=1,
                               log=None, **kwargs):
    """
    Create AXIS master interface (for API compatibility with AXI4).

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix
        data_width: Width of TDATA field
        id_width: Width of TID field
        dest_width: Width of TDEST field
        user_width: Width of TUSER field
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        AXISMaster instance
    """
    result = create_axis_master(
        dut, clock, prefix, data_width, id_width,
        dest_width, user_width, log, **kwargs
    )
    return result['interface']


def create_axis_slave_interface(dut, clock, prefix="", data_width=32,
                              id_width=8, dest_width=4, user_width=1,
                              log=None, **kwargs):
    """
    Create AXIS slave interface (for API compatibility with AXI4).

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix
        data_width: Width of TDATA field
        id_width: Width of TID field
        dest_width: Width of TDEST field
        user_width: Width of TUSER field
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        AXISSlave instance
    """
    result = create_axis_slave(
        dut, clock, prefix, data_width, id_width,
        dest_width, user_width, log, **kwargs
    )
    return result['interface']


def create_axis_testbench(dut, clock, master_prefix="m_axis_", 
                         slave_prefix="s_axis_", data_width=32,
                         id_width=8, dest_width=4, user_width=1,
                         log=None, **kwargs):
    """
    Create complete AXIS testbench setup with master, slave, and monitors.

    Args:
        dut: Device under test
        clock: Clock signal
        master_prefix: Prefix for master signals
        slave_prefix: Prefix for slave signals
        data_width: Width of TDATA field
        id_width: Width of TID field
        dest_width: Width of TDEST field
        user_width: Width of TUSER field
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        Dictionary with all AXIS components

    Note: Creates components based on signal availability
    """
    components = {}
    
    # Create master interface if signals exist
    try:
        if hasattr(dut, f'{master_prefix}tvalid'):
            components['master'] = create_axis_master(
                dut, clock, master_prefix, data_width, id_width,
                dest_width, user_width, log=log, **kwargs
            )
            
            # Add master monitor
            components['master_monitor'] = create_axis_monitor(
                dut, clock, master_prefix, data_width, id_width,
                dest_width, user_width, is_slave=False, log=log, **kwargs
            )
    except Exception as e:
        if log:
            log.debug(f"Master interface creation: {e}")
    
    # Create slave interface if signals exist
    try:
        if hasattr(dut, f'{slave_prefix}tready'):
            components['slave'] = create_axis_slave(
                dut, clock, slave_prefix, data_width, id_width,
                dest_width, user_width, log=log, **kwargs
            )
            
            # Add slave monitor
            components['slave_monitor'] = create_axis_monitor(
                dut, clock, slave_prefix, data_width, id_width,
                dest_width, user_width, is_slave=True, log=log, **kwargs
            )
    except Exception as e:
        if log:
            log.debug(f"Slave interface creation: {e}")
    
    # Add convenience methods
    components['get_all_stats'] = lambda: {
        name: comp.get('interface', comp).get_stats()
        for name, comp in components.items()
        if hasattr(comp.get('interface', comp), 'get_stats')
    }
    
    return components


def create_simple_axis_master(dut, clock, prefix="", data_width=32, log=None, **kwargs):
    """
    Create simple AXIS master with minimal sideband signals.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix
        data_width: Width of TDATA field
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        AXISMaster instance
    """
    field_config = AXISFieldConfigs.create_simple_axis_config(data_width=data_width)
    
    master = AXISMaster(
        dut=dut,
        title=f"Simple_AXIS_Master_{prefix}",
        prefix=prefix,
        clock=clock,
        field_config=field_config,
        log=log,
        **kwargs
    )
    
    return master


def create_simple_axis_slave(dut, clock, prefix="", data_width=32, log=None, **kwargs):
    """
    Create simple AXIS slave with minimal sideband signals.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix
        data_width: Width of TDATA field
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        AXISSlave instance
    """
    field_config = AXISFieldConfigs.create_simple_axis_config(data_width=data_width)
    
    slave = AXISSlave(
        dut=dut,
        title=f"Simple_AXIS_Slave_{prefix}",
        prefix=prefix,
        clock=clock,
        field_config=field_config,
        log=log,
        **kwargs
    )
    
    return slave


# Utility functions for signal mapping
def get_axis_signal_map(prefix="", direction="master"):
    """
    Get standard AXIS signal mapping for manual override.
    
    Args:
        prefix: Signal prefix (e.g., "m_axis_", "s_axis_")
        direction: "master" or "slave" for signal direction
    
    Returns:
        Dictionary mapping simplified names to DUT signal names
    """
    if direction == "master":
        return {
            'valid': f'{prefix}tvalid',
            'ready': f'{prefix}tready',
            'data': f'{prefix}tdata',
            'strb': f'{prefix}tstrb',
            'last': f'{prefix}tlast',
            'id': f'{prefix}tid',
            'dest': f'{prefix}tdest',
            'user': f'{prefix}tuser'
        }
    else:  # slave
        return {
            'valid': f'{prefix}tvalid',
            'ready': f'{prefix}tready', 
            'data': f'{prefix}tdata',
            'strb': f'{prefix}tstrb',
            'last': f'{prefix}tlast',
            'id': f'{prefix}tid',
            'dest': f'{prefix}tdest',
            'user': f'{prefix}tuser'
        }


def print_axis_stats_to_log(components, log):
    """
    Print AXIS statistics to log file instead of console.

    Args:
        components: Dictionary of AXIS components from factory functions
        log: Logger instance
    """
    if not log:
        return
        
    log.info("=== AXIS Component Statistics ===")
    
    for name, component_dict in components.items():
        if isinstance(component_dict, dict) and 'interface' in component_dict:
            interface = component_dict['interface']
            if hasattr(interface, 'get_stats'):
                stats = interface.get_stats()
                log.info(f"\n{name.upper()} Statistics:")
                
                # Print key statistics
                for key, value in stats.items():
                    if isinstance(value, dict):
                        log.info(f"  {key}:")
                        for subkey, subvalue in value.items():
                            log.info(f"    {subkey}: {subvalue}")
                    else:
                        log.info(f"  {key}: {value}")


def get_axis_stats_summary(components):
    """
    Get summary of statistics from all AXIS components.

    Args:
        components: Dictionary of AXIS components from factory functions

    Returns:
        Dictionary with aggregated statistics
    """
    summary = {
        'total_packets_sent': 0,
        'total_packets_received': 0,
        'total_packets_observed': 0,
        'total_frames_sent': 0,
        'total_frames_received': 0,
        'total_frames_observed': 0,
        'total_data_bytes': 0,
        'protocol_violations': 0,
        'timeouts': 0,
        'errors': 0
    }
    
    for name, component_dict in components.items():
        if isinstance(component_dict, dict) and 'interface' in component_dict:
            interface = component_dict['interface']
            if hasattr(interface, 'get_stats'):
                stats = interface.get_stats()
                
                # Aggregate statistics
                summary['total_packets_sent'] += stats.get('packets_sent', 0)
                summary['total_packets_received'] += stats.get('packets_received', 0)
                summary['total_packets_observed'] += stats.get('packets_observed', 0)
                summary['total_frames_sent'] += stats.get('frames_sent', 0)
                summary['total_frames_received'] += stats.get('frames_received', 0)
                summary['total_frames_observed'] += stats.get('frames_observed', 0)
                summary['total_data_bytes'] += stats.get('total_data_bytes', 0)
                summary['timeouts'] += stats.get('timeouts', 0)
                summary['errors'] += stats.get('errors', 0)
                
                # Protocol violations from monitors
                if 'protocol_stats' in stats:
                    summary['protocol_violations'] += stats['protocol_stats'].get('protocol_violations', 0)
    
    return summary