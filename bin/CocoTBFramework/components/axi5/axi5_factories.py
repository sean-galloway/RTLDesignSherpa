# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axi5_factories
# Purpose: AXI5 Factory Functions for creating interface components.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-15

"""
AXI5 Factory Functions - Create AXI5 interface components.

This module provides factory functions for creating AXI5 master and slave
interfaces with all AXI5-specific features.

Key Features:
- Factory functions return component dictionaries for easy access
- Support for all AXI5 signals (ATOP, MTE, MPAM, MECID, etc.)
- Out-of-order response configuration
- Memory model integration
"""

from typing import Dict, Any, Optional, Tuple
from .axi5_interfaces import AXI5MasterRead, AXI5MasterWrite, AXI5SlaveRead, AXI5SlaveWrite


def create_axi5_master_rd(
    dut,
    clock,
    prefix: str = "",
    log=None,
    ifc_name: str = "",
    **kwargs
) -> Dict[str, Any]:
    """
    Create AXI5 Master Read interface.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix ("fub_axi_", "m_axi_", etc.)
        log: Logger instance
        ifc_name: Interface name for debug (e.g., "rdeng", "descr")
        **kwargs: Additional configuration:
            - data_width: Data bus width (default 32)
            - id_width: ID field width (default 8)
            - addr_width: Address bus width (default 32)
            - user_width: User signal width (default 1)
            - nsaid_width: NSAID field width (default 4)
            - mpam_width: MPAM field width (default 11)
            - mecid_width: MECID field width (default 16)
            - tagop_width: TAGOP field width (default 2)
            - tag_width: Single tag width (default 4)
            - chunknum_width: Chunk number width (default 4)
            - multi_sig: Use individual signals (default True)
            - timeout_cycles: Transaction timeout (default 5000)

    Returns:
        Dictionary containing AXI5 read master components:
            - 'AR': AR channel master component
            - 'R': R channel slave component
            - 'interface': High-level AXI5MasterRead interface
    """
    master_read = AXI5MasterRead(dut, clock, prefix, log=log, ifc_name=ifc_name, **kwargs)

    return {
        'AR': master_read.ar_channel,
        'R': master_read.r_channel,
        'interface': master_read,
    }


def create_axi5_master_wr(
    dut,
    clock,
    prefix: str = "",
    log=None,
    ifc_name: str = "",
    **kwargs
) -> Dict[str, Any]:
    """
    Create AXI5 Master Write interface.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix ("fub_axi_", "m_axi_", etc.)
        log: Logger instance
        ifc_name: Interface name for debug
        **kwargs: Additional configuration (see create_axi5_master_rd) plus:
            - atop_width: ATOP field width (default 6)

    Returns:
        Dictionary containing AXI5 write master components:
            - 'AW': AW channel master component
            - 'W': W channel master component
            - 'B': B channel slave component
            - 'interface': High-level AXI5MasterWrite interface
    """
    master_write = AXI5MasterWrite(dut, clock, prefix, log=log, ifc_name=ifc_name, **kwargs)

    return {
        'AW': master_write.aw_channel,
        'W': master_write.w_channel,
        'B': master_write.b_channel,
        'interface': master_write,
    }


def create_axi5_slave_rd(
    dut,
    clock,
    prefix: str = "",
    log=None,
    ifc_name: str = "",
    **kwargs
) -> Dict[str, Any]:
    """
    Create AXI5 Slave Read interface.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix ("m_axi_", "s_axi_", etc.)
        log: Logger instance
        ifc_name: Interface name for debug
        **kwargs: Additional configuration (see create_axi5_master_rd) plus:
            - memory_model: Memory model for data generation
            - base_addr: Base address offset (default 0)
            - response_delay: Response delay cycles (default 1)
            - enable_ooo: Enable out-of-order responses (default False)
            - ooo_config: OOO configuration dict:
                {
                    'mode': 'random' or 'deterministic',
                    'reorder_probability': 0.3,
                    'min_delay_cycles': 1,
                    'max_delay_cycles': 50,
                    'pattern': [sequence_order] for deterministic mode
                }

    Returns:
        Dictionary containing AXI5 read slave components:
            - 'AR': AR channel slave component
            - 'R': R channel master component
            - 'interface': High-level AXI5SlaveRead interface
    """
    slave_read = AXI5SlaveRead(dut, clock, prefix, log=log, ifc_name=ifc_name, **kwargs)

    return {
        'AR': slave_read.ar_channel,
        'R': slave_read.r_channel,
        'interface': slave_read,
    }


def create_axi5_slave_wr(
    dut,
    clock,
    prefix: str = "",
    log=None,
    ifc_name: str = "",
    **kwargs
) -> Dict[str, Any]:
    """
    Create AXI5 Slave Write interface.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix ("m_axi_", "s_axi_", etc.)
        log: Logger instance
        ifc_name: Interface name for debug
        **kwargs: Additional configuration (see create_axi5_slave_rd) plus:
            - atop_width: ATOP field width (default 6)

    Returns:
        Dictionary containing AXI5 write slave components:
            - 'AW': AW channel slave component
            - 'W': W channel slave component
            - 'B': B channel master component
            - 'interface': High-level AXI5SlaveWrite interface
    """
    slave_write = AXI5SlaveWrite(dut, clock, prefix, log=log, ifc_name=ifc_name, **kwargs)

    return {
        'AW': slave_write.aw_channel,
        'W': slave_write.w_channel,
        'B': slave_write.b_channel,
        'interface': slave_write,
    }


def create_axi5_master_interface(
    dut,
    clock,
    prefix: str = "",
    log=None,
    **kwargs
) -> Tuple[AXI5MasterWrite, AXI5MasterRead]:
    """
    Create both read and write master interfaces.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        Tuple of (write_interface, read_interface)
    """
    write_if = AXI5MasterWrite(dut, clock, prefix, log=log, **kwargs)
    read_if = AXI5MasterRead(dut, clock, prefix, log=log, **kwargs)
    return write_if, read_if


def create_axi5_slave_interface(
    dut,
    clock,
    prefix: str = "",
    log=None,
    **kwargs
) -> Tuple[AXI5SlaveWrite, AXI5SlaveRead]:
    """
    Create both read and write slave interfaces.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        Tuple of (write_interface, read_interface)
    """
    write_if = AXI5SlaveWrite(dut, clock, prefix, log=log, **kwargs)
    read_if = AXI5SlaveRead(dut, clock, prefix, log=log, **kwargs)
    return write_if, read_if


def create_complete_axi5_testbench_components(
    dut,
    clock,
    master_prefix: str = "m_axi_",
    slave_prefix: str = "s_axi_",
    log=None,
    **kwargs
) -> Dict[str, Any]:
    """
    Create a complete set of AXI5 components for testbench.

    Args:
        dut: Device under test
        clock: Clock signal
        master_prefix: Prefix for master signals
        slave_prefix: Prefix for slave signals
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        Dictionary with all AXI5 components:
            - 'master_write': Master write components (if signals exist)
            - 'master_read': Master read components (if signals exist)
            - 'slave_write': Slave write components (if signals exist)
            - 'slave_read': Slave read components (if signals exist)
    """
    components = {}

    # Create master interfaces if signals exist
    try:
        if hasattr(dut, f'{master_prefix}awvalid'):
            components['master_write'] = create_axi5_master_wr(
                dut, clock, master_prefix, log=log, **kwargs
            )

        if hasattr(dut, f'{master_prefix}arvalid'):
            components['master_read'] = create_axi5_master_rd(
                dut, clock, master_prefix, log=log, **kwargs
            )
    except Exception as e:
        if log:
            log.debug(f"Master interface creation: {e}")

    # Create slave interfaces if signals exist
    try:
        if hasattr(dut, f'{slave_prefix}awready'):
            components['slave_write'] = create_axi5_slave_wr(
                dut, clock, slave_prefix, log=log, **kwargs
            )

        if hasattr(dut, f'{slave_prefix}arready'):
            components['slave_read'] = create_axi5_slave_rd(
                dut, clock, slave_prefix, log=log, **kwargs
            )
    except Exception as e:
        if log:
            log.debug(f"Slave interface creation: {e}")

    return components


# AXI5-specific factory helper functions

def create_axi5_with_mte(
    dut,
    clock,
    prefix: str = "",
    log=None,
    tag_width: int = 4,
    **kwargs
) -> Dict[str, Any]:
    """
    Create AXI5 interfaces configured for Memory Tagging Extension (MTE).

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix
        log: Logger instance
        tag_width: Width of memory tags (default 4)
        **kwargs: Additional configuration

    Returns:
        Dictionary with 'master_write', 'master_read', 'slave_write', 'slave_read'
    """
    mte_kwargs = {
        'tag_width': tag_width,
        'tagop_width': 2,
        **kwargs
    }

    return create_complete_axi5_testbench_components(
        dut, clock, prefix, prefix, log, **mte_kwargs
    )


def create_axi5_with_atomic(
    dut,
    clock,
    prefix: str = "",
    log=None,
    atop_width: int = 6,
    **kwargs
) -> Dict[str, Any]:
    """
    Create AXI5 interfaces configured for atomic operations.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix
        log: Logger instance
        atop_width: Width of ATOP field (default 6)
        **kwargs: Additional configuration

    Returns:
        Dictionary with 'master_write', 'slave_write' for atomic operations
    """
    atomic_kwargs = {
        'atop_width': atop_width,
        **kwargs
    }

    components = {}
    components['master_write'] = create_axi5_master_wr(
        dut, clock, prefix, log=log, **atomic_kwargs
    )
    components['slave_write'] = create_axi5_slave_wr(
        dut, clock, prefix, log=log, **atomic_kwargs
    )

    return components


def create_axi5_with_security(
    dut,
    clock,
    prefix: str = "",
    log=None,
    nsaid_width: int = 4,
    mpam_width: int = 11,
    mecid_width: int = 16,
    **kwargs
) -> Dict[str, Any]:
    """
    Create AXI5 interfaces configured for security features (NSAID, MPAM, MECID).

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix
        log: Logger instance
        nsaid_width: NSAID field width (default 4)
        mpam_width: MPAM field width (default 11)
        mecid_width: MECID field width (default 16)
        **kwargs: Additional configuration

    Returns:
        Complete AXI5 testbench components with security features enabled
    """
    security_kwargs = {
        'nsaid_width': nsaid_width,
        'mpam_width': mpam_width,
        'mecid_width': mecid_width,
        **kwargs
    }

    return create_complete_axi5_testbench_components(
        dut, clock, prefix, prefix, log, **security_kwargs
    )
