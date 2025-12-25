# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axis5_factories
# Purpose: AXIS5 Factory Functions - Component creation with AMBA5 extensions
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""
AXIS5 Factory Functions - Component creation with AMBA5 extensions

This module provides factory functions for creating AXIS5 components
with APIs similar to AXIS4 factories for consistency.

AXIS5 extends AXIS4 with:
- TWAKEUP: Wake-up signaling
- TPARITY: Data parity protection
"""

from typing import Dict, Any
from .axis5_master import AXIS5Master
from .axis5_slave import AXIS5Slave
from .axis5_monitor import AXIS5Monitor
from .axis5_field_configs import AXIS5FieldConfigs


def create_axis5_master(dut, clock, prefix="", data_width=32, id_width=8,
                        dest_width=4, user_width=1, enable_wakeup=True,
                        enable_parity=False, wakeup_cycles=3,
                        log=None, **kwargs) -> Dict[str, Any]:
    """
    Create AXIS5 Master interface.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix ("m_axis5_", "fub_axis5_", etc.)
        data_width: Width of TDATA field
        id_width: Width of TID field
        dest_width: Width of TDEST field
        user_width: Width of TUSER field
        enable_wakeup: Enable TWAKEUP signaling
        enable_parity: Enable TPARITY generation
        wakeup_cycles: Number of cycles for wakeup signaling
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        Dictionary containing AXIS5 master components
    """
    # Create field configuration
    field_config = AXIS5FieldConfigs.create_axis5_config_from_hw_params(
        data_width=data_width,
        id_width=id_width,
        dest_width=dest_width,
        user_width=user_width,
        enable_wakeup=enable_wakeup,
        enable_parity=enable_parity
    )

    # Create the master
    master = AXIS5Master(
        dut=dut,
        title=f"AXIS5_Master_{prefix}",
        prefix=prefix,
        clock=clock,
        field_config=field_config,
        enable_wakeup=enable_wakeup,
        enable_parity=enable_parity,
        wakeup_cycles=wakeup_cycles,
        log=log,
        **kwargs
    )

    # Return components in format expected by testbench
    return {
        'T': master,                # T channel master component
        'interface': master,        # High-level interface
        'master': master           # Direct access
    }


def create_axis5_slave(dut, clock, prefix="", data_width=32, id_width=8,
                       dest_width=4, user_width=1, enable_wakeup=True,
                       enable_parity=False, log=None, **kwargs) -> Dict[str, Any]:
    """
    Create AXIS5 Slave interface.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix ("s_axis5_", "axis5_", etc.)
        data_width: Width of TDATA field
        id_width: Width of TID field
        dest_width: Width of TDEST field
        user_width: Width of TUSER field
        enable_wakeup: Enable TWAKEUP detection
        enable_parity: Enable TPARITY checking
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        Dictionary containing AXIS5 slave components
    """
    # Create field configuration
    field_config = AXIS5FieldConfigs.create_axis5_config_from_hw_params(
        data_width=data_width,
        id_width=id_width,
        dest_width=dest_width,
        user_width=user_width,
        enable_wakeup=enable_wakeup,
        enable_parity=enable_parity
    )

    # Create the slave
    slave = AXIS5Slave(
        dut=dut,
        title=f"AXIS5_Slave_{prefix}",
        prefix=prefix,
        clock=clock,
        field_config=field_config,
        enable_wakeup=enable_wakeup,
        enable_parity=enable_parity,
        log=log,
        **kwargs
    )

    # Return components in format expected by testbench
    return {
        'T': slave,                 # T channel slave component
        'interface': slave,         # High-level interface
        'slave': slave             # Direct access
    }


def create_axis5_monitor(dut, clock, prefix="", data_width=32, id_width=8,
                         dest_width=4, user_width=1, is_slave=False,
                         enable_wakeup=True, enable_parity=False,
                         log=None, **kwargs) -> Dict[str, Any]:
    """
    Create AXIS5 Monitor interface.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix ("s_axis5_", "m_axis5_", etc.)
        data_width: Width of TDATA field
        id_width: Width of TID field
        dest_width: Width of TDEST field
        user_width: Width of TUSER field
        is_slave: True if monitoring slave side, False for master side
        enable_wakeup: Enable TWAKEUP observation
        enable_parity: Enable TPARITY verification
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        Dictionary containing AXIS5 monitor components
    """
    # Create field configuration
    field_config = AXIS5FieldConfigs.create_axis5_config_from_hw_params(
        data_width=data_width,
        id_width=id_width,
        dest_width=dest_width,
        user_width=user_width,
        enable_wakeup=enable_wakeup,
        enable_parity=enable_parity
    )

    # Create the monitor
    monitor = AXIS5Monitor(
        dut=dut,
        title=f"AXIS5_Monitor_{prefix}",
        prefix=prefix,
        clock=clock,
        field_config=field_config,
        is_slave=is_slave,
        enable_wakeup=enable_wakeup,
        enable_parity=enable_parity,
        log=log,
        **kwargs
    )

    # Return components in format expected by testbench
    return {
        'T': monitor,               # T channel monitor component
        'interface': monitor,       # High-level interface
        'monitor': monitor         # Direct access
    }


def create_axis5_master_interface(dut, clock, prefix="", data_width=32,
                                  id_width=8, dest_width=4, user_width=1,
                                  enable_wakeup=True, enable_parity=False,
                                  log=None, **kwargs):
    """
    Create AXIS5 master interface (for API compatibility).

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix
        data_width: Width of TDATA field
        id_width: Width of TID field
        dest_width: Width of TDEST field
        user_width: Width of TUSER field
        enable_wakeup: Enable TWAKEUP signaling
        enable_parity: Enable TPARITY generation
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        AXIS5Master instance
    """
    result = create_axis5_master(
        dut, clock, prefix, data_width, id_width,
        dest_width, user_width, enable_wakeup, enable_parity,
        log=log, **kwargs
    )
    return result['interface']


def create_axis5_slave_interface(dut, clock, prefix="", data_width=32,
                                 id_width=8, dest_width=4, user_width=1,
                                 enable_wakeup=True, enable_parity=False,
                                 log=None, **kwargs):
    """
    Create AXIS5 slave interface (for API compatibility).

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix
        data_width: Width of TDATA field
        id_width: Width of TID field
        dest_width: Width of TDEST field
        user_width: Width of TUSER field
        enable_wakeup: Enable TWAKEUP detection
        enable_parity: Enable TPARITY checking
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        AXIS5Slave instance
    """
    result = create_axis5_slave(
        dut, clock, prefix, data_width, id_width,
        dest_width, user_width, enable_wakeup, enable_parity,
        log=log, **kwargs
    )
    return result['interface']


def create_axis5_testbench(dut, clock, master_prefix="m_axis5_",
                           slave_prefix="s_axis5_", data_width=32,
                           id_width=8, dest_width=4, user_width=1,
                           enable_wakeup=True, enable_parity=False,
                           log=None, **kwargs):
    """
    Create complete AXIS5 testbench setup with master, slave, and monitors.

    Args:
        dut: Device under test
        clock: Clock signal
        master_prefix: Prefix for master signals
        slave_prefix: Prefix for slave signals
        data_width: Width of TDATA field
        id_width: Width of TID field
        dest_width: Width of TDEST field
        user_width: Width of TUSER field
        enable_wakeup: Enable TWAKEUP signaling/detection
        enable_parity: Enable TPARITY generation/checking
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        Dictionary with all AXIS5 components
    """
    components = {}

    # Create master interface if signals exist
    try:
        if hasattr(dut, f'{master_prefix}tvalid'):
            components['master'] = create_axis5_master(
                dut, clock, master_prefix, data_width, id_width,
                dest_width, user_width, enable_wakeup, enable_parity,
                log=log, **kwargs
            )

            # Add master monitor
            components['master_monitor'] = create_axis5_monitor(
                dut, clock, master_prefix, data_width, id_width,
                dest_width, user_width, is_slave=False,
                enable_wakeup=enable_wakeup, enable_parity=enable_parity,
                log=log, **kwargs
            )
    except Exception as e:
        if log:
            log.debug(f"Master interface creation: {e}")

    # Create slave interface if signals exist
    try:
        if hasattr(dut, f'{slave_prefix}tready'):
            components['slave'] = create_axis5_slave(
                dut, clock, slave_prefix, data_width, id_width,
                dest_width, user_width, enable_wakeup, enable_parity,
                log=log, **kwargs
            )

            # Add slave monitor
            components['slave_monitor'] = create_axis5_monitor(
                dut, clock, slave_prefix, data_width, id_width,
                dest_width, user_width, is_slave=True,
                enable_wakeup=enable_wakeup, enable_parity=enable_parity,
                log=log, **kwargs
            )
    except Exception as e:
        if log:
            log.debug(f"Slave interface creation: {e}")

    # Add convenience methods
    components['get_all_stats'] = lambda: {
        name: comp.get('interface', comp).get_stats()
        for name, comp in components.items()
        if hasattr(comp.get('interface', comp) if isinstance(comp, dict) else comp, 'get_stats')
    }

    return components


def create_simple_axis5_master(dut, clock, prefix="", data_width=32,
                               enable_wakeup=True, enable_parity=False,
                               log=None, **kwargs):
    """
    Create simple AXIS5 master with minimal sideband signals.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix
        data_width: Width of TDATA field
        enable_wakeup: Enable TWAKEUP signaling
        enable_parity: Enable TPARITY generation
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        AXIS5Master instance
    """
    field_config = AXIS5FieldConfigs.create_simple_axis5_config(
        data_width=data_width,
        enable_wakeup=enable_wakeup,
        enable_parity=enable_parity
    )

    master = AXIS5Master(
        dut=dut,
        title=f"Simple_AXIS5_Master_{prefix}",
        prefix=prefix,
        clock=clock,
        field_config=field_config,
        enable_wakeup=enable_wakeup,
        enable_parity=enable_parity,
        log=log,
        **kwargs
    )

    return master


def create_simple_axis5_slave(dut, clock, prefix="", data_width=32,
                              enable_wakeup=True, enable_parity=False,
                              log=None, **kwargs):
    """
    Create simple AXIS5 slave with minimal sideband signals.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix
        data_width: Width of TDATA field
        enable_wakeup: Enable TWAKEUP detection
        enable_parity: Enable TPARITY checking
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        AXIS5Slave instance
    """
    field_config = AXIS5FieldConfigs.create_simple_axis5_config(
        data_width=data_width,
        enable_wakeup=enable_wakeup,
        enable_parity=enable_parity
    )

    slave = AXIS5Slave(
        dut=dut,
        title=f"Simple_AXIS5_Slave_{prefix}",
        prefix=prefix,
        clock=clock,
        field_config=field_config,
        enable_wakeup=enable_wakeup,
        enable_parity=enable_parity,
        log=log,
        **kwargs
    )

    return slave


# Utility functions for signal mapping
def get_axis5_signal_map(prefix="", direction="master"):
    """
    Get standard AXIS5 signal mapping for manual override.

    Args:
        prefix: Signal prefix (e.g., "m_axis5_", "s_axis5_")
        direction: "master" or "slave" for signal direction

    Returns:
        Dictionary mapping simplified names to DUT signal names
    """
    base_map = {
        'valid': f'{prefix}tvalid',
        'ready': f'{prefix}tready',
        'data': f'{prefix}tdata',
        'strb': f'{prefix}tstrb',
        'last': f'{prefix}tlast',
        'id': f'{prefix}tid',
        'dest': f'{prefix}tdest',
        'user': f'{prefix}tuser',
        # AXIS5 extensions
        'wakeup': f'{prefix}twakeup',
        'parity': f'{prefix}tparity'
    }

    return base_map


def print_axis5_stats_to_log(components, log):
    """
    Print AXIS5 statistics to log file.

    Args:
        components: Dictionary of AXIS5 components from factory functions
        log: Logger instance
    """
    if not log:
        return

    log.info("=== AXIS5 Component Statistics ===")

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


def get_axis5_stats_summary(components):
    """
    Get summary of statistics from all AXIS5 components.

    Args:
        components: Dictionary of AXIS5 components from factory functions

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
        'axis5_protocol_violations': 0,
        'timeouts': 0,
        'errors': 0,
        # AXIS5-specific
        'wakeup_events': 0,
        'parity_errors': 0,
        'parity_checks_passed': 0
    }

    for name, component_dict in components.items():
        if isinstance(component_dict, dict) and 'interface' in component_dict:
            interface = component_dict['interface']
            if hasattr(interface, 'get_stats'):
                stats = interface.get_stats()

                # Aggregate standard statistics
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

                # AXIS5-specific statistics
                summary['axis5_protocol_violations'] += stats.get('axis5_protocol_violations', 0)
                summary['wakeup_events'] += stats.get('wakeup_events', 0)

                if 'parity_stats' in stats:
                    summary['parity_errors'] += stats['parity_stats'].get('parity_errors', 0)
                    summary['parity_checks_passed'] += stats['parity_stats'].get('parity_passed', 0)
                elif 'wakeup_stats' in stats:
                    summary['wakeup_events'] += stats['wakeup_stats'].get('wakeup_events', 0)

    return summary
