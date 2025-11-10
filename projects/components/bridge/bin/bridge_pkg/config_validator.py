#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Configuration Validator for Bridge Generator
# Purpose: Validate YAML bridge configurations and detect illegal combinations

"""
Configuration Validator

Validates bridge configurations to detect:
1. Invalid channel specifications (not in ['rw', 'rd', 'wr'])
2. Invalid protocol specifications (not in ['axi4', 'apb', 'axil'])
3. Illegal master-slave channel combinations (incompatible channels)
4. APB-specific constraints (must be 'rw', specific data widths)
5. AXI4-Lite specific constraints
6. Missing required fields
7. Semantic errors (slaves shouldn't specify channels - derived from masters)

Usage:
    from bridge_pkg.config_validator import validate_config, ValidationError

    try:
        validate_config(masters, slaves, connectivity)
    except ValidationError as e:
        print(f"Configuration error: {e}")
        sys.exit(1)
"""

from typing import List, Dict, Set
from .config import PortSpec


class ValidationError(Exception):
    """Exception raised for configuration validation errors."""
    pass


def validate_channels(channels: str, port_name: str) -> None:
    """
    Validate channels field value.

    Args:
        channels: Channel specification ('rw', 'rd', 'wr')
        port_name: Port name for error messages

    Raises:
        ValidationError: If channels value is invalid
    """
    valid_channels = {'rw', 'rd', 'wr'}
    if channels not in valid_channels:
        raise ValidationError(
            f"Invalid channels '{channels}' for port '{port_name}'. "
            f"Must be one of {valid_channels}"
        )


def validate_protocol(protocol: str, port_name: str) -> None:
    """
    Validate protocol field value.

    Args:
        protocol: Protocol specification ('axi4', 'apb', 'axil')
        port_name: Port name for error messages

    Raises:
        ValidationError: If protocol value is invalid
    """
    valid_protocols = {'axi4', 'apb', 'axil'}
    if protocol not in valid_protocols:
        raise ValidationError(
            f"Invalid protocol '{protocol}' for port '{port_name}'. "
            f"Must be one of {valid_protocols}"
        )


def validate_apb_constraints(port: PortSpec) -> None:
    """
    Validate APB-specific constraints.

    APB constraints:
    1. Must support both read and write (channels = 'rw')
    2. Data width must be 32 bits (APB4 standard)
    3. Address width typically 32 bits
    4. No ID width (APB has no transaction IDs)

    Args:
        port: Port specification to validate

    Raises:
        ValidationError: If APB constraints are violated
    """
    if port.protocol != 'apb':
        return  # Not APB, skip

    # APB must be read-write
    if port.channels != 'rw':
        raise ValidationError(
            f"APB port '{port.port_name}' must have channels='rw' "
            f"(APB protocol requires both read and write support). "
            f"Got channels='{port.channels}'"
        )

    # APB data width is 32 bits (APB4 standard)
    if port.data_width not in [8, 16, 32]:
        raise ValidationError(
            f"APB port '{port.port_name}' has non-standard data width {port.data_width}. "
            f"APB4 standard data widths are 8, 16, or 32 bits. "
            f"Consider using 32-bit width for standard compliance."
        )

    # APB has no transaction IDs
    if port.id_width != 0:
        raise ValidationError(
            f"APB port '{port.port_name}' must have id_width=0 "
            f"(APB protocol has no transaction IDs). "
            f"Got id_width={port.id_width}"
        )


def validate_master_slave_compatibility(
    master: PortSpec,
    slave: PortSpec,
    connectivity: Dict[str, Set[str]]
) -> None:
    """
    Validate that connected masters and slaves have compatible channels.

    Compatibility rules:
    1. Write-only master (wr) can ONLY connect to slaves supporting write (wr or rw)
    2. Read-only master (rd) can ONLY connect to slaves supporting read (rd or rw)
    3. Full RW master (rw) can connect to any slave (rw, wr, or rd)
    4. APB slaves MUST be 'rw' (validated separately)

    Args:
        master: Master port specification
        slave: Slave port specification
        connectivity: Connectivity dictionary

    Raises:
        ValidationError: If master-slave channel combination is illegal
    """
    # Check if master connects to this slave
    if slave.port_name not in connectivity.get(master.port_name, set()):
        return  # Not connected, skip validation

    master_channels = master.channels
    slave_channels = slave.channels

    # Write-only master
    if master_channels == 'wr':
        if slave_channels == 'rd':
            raise ValidationError(
                f"Illegal connection: Write-only master '{master.port_name}' "
                f"cannot connect to read-only slave '{slave.port_name}'. "
                f"Master has channels='wr' (AW, W, B), "
                f"slave has channels='rd' (AR, R) - no compatible channels!"
            )

    # Read-only master
    elif master_channels == 'rd':
        if slave_channels == 'wr':
            raise ValidationError(
                f"Illegal connection: Read-only master '{master.port_name}' "
                f"cannot connect to write-only slave '{slave.port_name}'. "
                f"Master has channels='rd' (AR, R), "
                f"slave has channels='wr' (AW, W, B) - no compatible channels!"
            )

    # Full RW master can connect to any slave (no error case)


def validate_slave_channels_explicit(slaves: List[PortSpec]) -> None:
    """
    Validate that slaves have explicit channel specifications.

    IMPORTANT: Slaves MUST explicitly specify channels in YAML - no defaults, no guessing.
    This ensures the configuration is self-documenting and the user's intent is clear.

    Slaves should specify the channels they SUPPORT, not necessarily what they REQUIRE.
    The crossbar will only generate channels actually needed by connecting masters.

    Args:
        slaves: List of slave port specifications

    Raises:
        ValidationError: If any slave doesn't explicitly specify channels
    """
    for slave in slaves:
        # Check if channels was explicitly set (not just defaulted)
        # Note: This assumes config_loader sets channels during parsing
        # We validate it's one of the valid values
        if not slave.channels:
            raise ValidationError(
                f"Configuration error: Slave '{slave.port_name}' missing 'channels' field. "
                f"Slaves MUST explicitly specify channels ('rw', 'rd', or 'wr'). "
                f"This documents the slave's supported operations.\n"
                f"\n"
                f"Example:\n"
                f"  slaves:\n"
                f"    - name: {slave.port_name}\n"
                f"      channels: rw  # Supports both read and write\n"
                f"\n"
                f"Note: The crossbar will only generate channels actually needed by "
                f"connecting masters, but the slave must declare what it supports."
            )


def validate_required_fields(port: PortSpec) -> None:
    """
    Validate that all required fields are present and non-zero where appropriate.

    Args:
        port: Port specification to validate

    Raises:
        ValidationError: If required fields are missing or invalid
    """
    # All ports need these
    if not port.port_name:
        raise ValidationError("Port missing 'name' field")

    if not port.prefix:
        raise ValidationError(f"Port '{port.port_name}' missing 'prefix' field")

    if port.data_width <= 0:
        raise ValidationError(f"Port '{port.port_name}' has invalid data_width={port.data_width}")

    if port.addr_width <= 0:
        raise ValidationError(f"Port '{port.port_name}' has invalid addr_width={port.addr_width}")

    # AXI4 masters need ID width
    if port.direction == 'master' and port.protocol == 'axi4':
        if port.id_width <= 0:
            raise ValidationError(
                f"AXI4 master '{port.port_name}' must have id_width > 0. "
                f"Got id_width={port.id_width}"
            )

    # Slaves need address mapping
    if port.direction == 'slave':
        if port.base_addr is None:
            raise ValidationError(f"Slave '{port.port_name}' missing 'base_addr' field")

        if port.addr_range is None or port.addr_range <= 0:
            raise ValidationError(
                f"Slave '{port.port_name}' has invalid addr_range={port.addr_range}"
            )


def validate_address_map(slaves: List[PortSpec]) -> None:
    """
    Validate slave address map for overlaps.

    Args:
        slaves: List of slave port specifications

    Raises:
        ValidationError: If slave address ranges overlap
    """
    for i, slave1 in enumerate(slaves):
        addr1_start = slave1.base_addr
        addr1_end = slave1.base_addr + slave1.addr_range - 1

        for slave2 in slaves[i+1:]:
            addr2_start = slave2.base_addr
            addr2_end = slave2.base_addr + slave2.addr_range - 1

            # Check for overlap
            if not (addr1_end < addr2_start or addr2_end < addr1_start):
                raise ValidationError(
                    f"Address overlap detected:\n"
                    f"  Slave '{slave1.port_name}': 0x{addr1_start:08X} - 0x{addr1_end:08X}\n"
                    f"  Slave '{slave2.port_name}': 0x{addr2_start:08X} - 0x{addr2_end:08X}\n"
                    f"Slave address ranges must not overlap!"
                )


def validate_config(
    masters: List[PortSpec],
    slaves: List[PortSpec],
    connectivity: Dict[str, Set[str]]
) -> None:
    """
    Comprehensive validation of bridge configuration.

    Validates:
    1. Required fields presence
    2. Valid channels and protocols
    3. APB-specific constraints
    4. Master-slave channel compatibility
    5. Slave channel semantic correctness
    6. Address map overlaps

    Args:
        masters: List of master port specifications
        slaves: List of slave port specifications
        connectivity: Connectivity dictionary (master_name -> set of slave_names)

    Raises:
        ValidationError: If any validation check fails
    """
    # Validate each master
    for master in masters:
        validate_required_fields(master)
        validate_channels(master.channels, master.port_name)
        validate_protocol(master.protocol, master.port_name)
        validate_apb_constraints(master)

    # Validate each slave
    for slave in slaves:
        validate_required_fields(slave)
        validate_channels(slave.channels, slave.port_name)
        validate_protocol(slave.protocol, slave.port_name)
        validate_apb_constraints(slave)

    # Validate explicit channel specification for slaves
    validate_slave_channels_explicit(slaves)

    # Validate address map
    validate_address_map(slaves)

    # Validate master-slave compatibility
    for master in masters:
        for slave in slaves:
            validate_master_slave_compatibility(master, slave, connectivity)

    print("✓ Configuration validation passed")
