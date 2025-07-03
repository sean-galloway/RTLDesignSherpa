"""
AXI4 Clean Factory Functions - Complete Master/Slave Creation

This module provides the complete set of clean factory functions for creating
AXI4 masters and slaves with proper channel configurations.

Required Factory Functions:
- create_axi4_master (all channels)
- create_axi4_read_master (AR, R channels only)
- create_axi4_write_master (AW, W, B channels only)
- create_axi4_slave (all channels)
- create_axi4_read_slave (AR, R channels only)
- create_axi4_write_slave (AW, W, B channels only)

Key Design Principles:
1. Clean, simple interfaces that hide complexity
2. Leverage working GAXI foundation through composition
3. Sensible defaults for common use cases
4. Easy to extend and maintain
5. Minimal complexity while preserving functionality
"""

from typing import Dict, List, Optional, Any
from .axi4_channel import create_axi4_channel, AXI4Channel
from .axi4_master import AXI4Master
from .axi4_slave import AXI4Slave
from .axi4_signal_mapper import AXI4SignalMapper
from .axi4_field_configs import AXI4FieldConfigHelper


# ============================================================================
# MASTER FACTORY FUNCTIONS
# ============================================================================

def create_axi4_master(dut, clock, prefix: str = 'm_axi',
                        channels: List[str] = ['AW', 'W', 'B', 'AR', 'R'],
                        id_width: int = 8, addr_width: int = 32, data_width: int = 32, user_width: int = 1,
                        memory_model=None, timing_config=None, log=None, **kwargs) -> AXI4Master:
    """
    Create a complete AXI4 Master using the ground-up design approach.

    This is the main factory function that provides a clean, simple interface
    for creating AXI4 masters while hiding the underlying complexity.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: AXI4 signal prefix (e.g., 'm_axi', 's_axi')
        channels: List of AXI4 channels to create (['AW', 'W', 'B', 'AR', 'R'])
        id_width: Width of ID fields (1-16 bits)
        addr_width: Width of address fields (32-64 bits typically)
        data_width: Width of data fields (8, 16, 32, 64, 128, 256, 512, 1024)
        user_width: Width of user fields (0-32 bits, 0 to disable)
        memory_model: Optional memory model for transactions
        timing_config: Optional timing configuration/randomizer
        log: Logger instance
        **kwargs: Additional arguments passed to underlying GAXI components

    Returns:
        AXI4Master instance ready for use

    Example:
        # Full AXI4 master creation
        master = create_axi4_master(
            dut=dut,
            clock=dut.aclk,
            prefix='m_axi',
            id_width=8,
            addr_width=32,
            data_width=32
        )

        # Use the master
        await master.write_single(addr=0x1000, data=0xDEADBEEF)
        await master.read_single(addr=0x1000)
    """
    # Validate inputs
    if not channels:
        raise ValueError("At least one channel must be specified")

    for channel in channels:
        if not AXI4SignalMapper.validate_axi4_channel(channel):
            raise ValueError(f"Invalid AXI4 channel: {channel}")

    is_valid, errors = AXI4FieldConfigHelper.validate_axi4_widths(id_width, addr_width, data_width, user_width)
    if not is_valid:
        raise ValueError(f"Invalid field widths: {', '.join(errors)}")

    if log:
        log.info(f"Creating AXI4Master: prefix='{prefix}', channels={channels}")
        log.debug(f"Field widths: id={id_width}, addr={addr_width}, data={data_width}, user={user_width}")

    # Create individual AXI4 channels
    axi4_channels = {}

    for channel_name in channels:
        try:
            if log:
                log.debug(f"Creating channel {channel_name}")

            channel = create_axi4_channel(
                dut=dut,
                clock=clock,
                prefix=prefix,
                channel_name=channel_name,
                id_width=id_width,
                addr_width=addr_width,
                data_width=data_width,
                user_width=user_width,
                memory_model=memory_model,
                timing_config=timing_config,
                log=log,
                **kwargs
            )

            axi4_channels[channel_name] = channel

            if log:
                expected_signals = channel.get_expected_signals()
                log.debug(f"Channel {channel_name} created with signals: {list(expected_signals.values())}")

        except Exception as e:
            error_msg = f"Failed to create channel {channel_name}: {e}"
            if log:
                log.error(error_msg)
            raise RuntimeError(error_msg) from e

    # Create coordinated master
    try:
        master = AXI4Master(
            channels=axi4_channels,
            prefix=prefix,
            memory_model=memory_model,
            log=log
        )

        if log:
            log.info(f"AXI4Master created successfully with {len(axi4_channels)} channels")
            debug_info = master.get_debug_info()
            log.debug(f"Master debug info: {debug_info}")

        return master

    except Exception as e:
        error_msg = f"Failed to create AXI4Master: {e}"
        if log:
            log.error(error_msg)
        raise RuntimeError(error_msg) from e


def create_axi4_read_master(dut, clock, prefix: str = 'm_axi',
                          id_width: int = 8, addr_width: int = 32, data_width: int = 32, user_width: int = 1,
                          memory_model=None, timing_config=None, log=None, **kwargs) -> AXI4Master:
    """
    Create an AXI4 Master configured for read operations only.

    This creates a master with only the channels needed for read operations: AR, R.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: AXI4 signal prefix
        id_width: Width of ID fields
        addr_width: Width of address fields
        data_width: Width of data fields
        user_width: Width of user fields
        memory_model: Optional memory model
        timing_config: Optional timing configuration
        log: Logger instance
        **kwargs: Additional arguments

    Returns:
        AXI4Master configured for read operations

    Example:
        # Read-only master
        read_master = create_axi4_read_master(
            dut=dut,
            clock=dut.aclk,
            prefix='m_axi'
        )
        await read_master.read_single(addr=0x1000)
    """
    return create_axi4_master(
        dut=dut,
        clock=clock,
        prefix=prefix,
        channels=['AR', 'R'],  # Read-only channels
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        memory_model=memory_model,
        timing_config=timing_config,
        log=log,
        **kwargs
    )


def create_axi4_write_master(dut, clock, prefix: str = 'm_axi',
                           id_width: int = 8, addr_width: int = 32, data_width: int = 32, user_width: int = 1,
                           memory_model=None, timing_config=None, log=None, **kwargs) -> AXI4Master:
    """
    Create an AXI4 Master configured for write operations only.

    This creates a master with only the channels needed for write operations: AW, W, B.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: AXI4 signal prefix
        id_width: Width of ID fields
        addr_width: Width of address fields
        data_width: Width of data fields
        user_width: Width of user fields
        memory_model: Optional memory model
        timing_config: Optional timing configuration
        log: Logger instance
        **kwargs: Additional arguments

    Returns:
        AXI4Master configured for write operations

    Example:
        # Write-only master
        write_master = create_axi4_write_master(
            dut=dut,
            clock=dut.aclk,
            prefix='m_axi'
        )
        await write_master.write_single(addr=0x1000, data=0xDEADBEEF)
    """
    return create_axi4_master(
        dut=dut,
        clock=clock,
        prefix=prefix,
        channels=['AW', 'W', 'B'],  # Write-only channels
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        memory_model=memory_model,
        timing_config=timing_config,
        log=log,
        **kwargs
    )


# ============================================================================
# SLAVE FACTORY FUNCTIONS
# ============================================================================

def create_axi4_slave(dut, clock, prefix: str = 's_axi',
                     channels: List[str] = ['AW', 'W', 'B', 'AR', 'R'],
                     id_width: int = 8, addr_width: int = 32, data_width: int = 32, user_width: int = 1,
                     memory_model=None, timing_config=None, log=None, **kwargs) -> AXI4Slave:
    """
    Create a complete AXI4 Slave using the ground-up design approach.

    This is the main factory function for creating AXI4 slaves that can handle
    both read and write transactions with proper channel coordination.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: AXI4 signal prefix (e.g., 's_axi', 'm_axi')
        channels: List of AXI4 channels to create (['AW', 'W', 'B', 'AR', 'R'])
        id_width: Width of ID fields (1-16 bits)
        addr_width: Width of address fields (32-64 bits typically)
        data_width: Width of data fields (8, 16, 32, 64, 128, 256, 512, 1024)
        user_width: Width of user fields (0-32 bits, 0 to disable)
        memory_model: Optional memory model for data storage
        timing_config: Optional timing configuration/randomizer
        log: Logger instance
        **kwargs: Additional arguments passed to underlying GAXI components

    Returns:
        AXI4Slave instance ready for use

    Example:
        # Full AXI4 slave creation
        slave = create_axi4_slave(
            dut=dut,
            clock=dut.aclk,
            prefix='s_axi',
            id_width=8,
            addr_width=32,
            data_width=32
        )

        # Slave automatically responds to transactions
        await slave.start()
    """
    # Validate inputs
    if not channels:
        raise ValueError("At least one channel must be specified")

    for channel in channels:
        if not AXI4SignalMapper.validate_axi4_channel(channel):
            raise ValueError(f"Invalid AXI4 channel: {channel}")

    is_valid, errors = AXI4FieldConfigHelper.validate_axi4_widths(id_width, addr_width, data_width, user_width)
    if not is_valid:
        raise ValueError(f"Invalid field widths: {', '.join(errors)}")

    if log:
        log.info(f"Creating AXI4Slave: prefix='{prefix}', channels={channels}")
        log.debug(f"Field widths: id={id_width}, addr={addr_width}, data={data_width}, user={user_width}")

    # Create individual AXI4 channels
    axi4_channels = {}

    for channel_name in channels:
        try:
            if log:
                log.debug(f"Creating slave channel {channel_name}")

            channel = create_axi4_channel(
                dut=dut,
                clock=clock,
                prefix=prefix,
                channel_name=channel_name,
                id_width=id_width,
                addr_width=addr_width,
                data_width=data_width,
                user_width=user_width,
                memory_model=memory_model,
                timing_config=timing_config,
                log=log,
                **kwargs
            )

            axi4_channels[channel_name] = channel

            if log:
                expected_signals = channel.get_expected_signals()
                log.debug(f"Slave channel {channel_name} created with signals: {list(expected_signals.values())}")

        except Exception as e:
            error_msg = f"Failed to create slave channel {channel_name}: {e}"
            if log:
                log.error(error_msg)
            raise RuntimeError(error_msg) from e

    # Create coordinated slave
    try:
        slave = AXI4Slave(
            channel_components=axi4_channels,
            timing_config=timing_config,
            memory_model=memory_model,
            log=log,
            **kwargs
        )

        if log:
            log.info(f"AXI4Slave created successfully with {len(axi4_channels)} channels")

        return slave

    except Exception as e:
        error_msg = f"Failed to create AXI4Slave: {e}"
        if log:
            log.error(error_msg)
        raise RuntimeError(error_msg) from e


def create_axi4_read_slave(dut, clock, prefix: str = 's_axi',
                          id_width: int = 8, addr_width: int = 32, data_width: int = 32, user_width: int = 1,
                          memory_model=None, timing_config=None, log=None, **kwargs) -> AXI4Slave:
    """
    Create an AXI4 Slave configured for read operations only.

    This creates a slave with only the channels needed for read operations: AR, R.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: AXI4 signal prefix
        id_width: Width of ID fields
        addr_width: Width of address fields
        data_width: Width of data fields
        user_width: Width of user fields
        memory_model: Optional memory model
        timing_config: Optional timing configuration
        log: Logger instance
        **kwargs: Additional arguments

    Returns:
        AXI4Slave configured for read operations

    Example:
        # Read-only slave
        read_slave = create_axi4_read_slave(
            dut=dut,
            clock=dut.aclk,
            prefix='s_axi'
        )
        await read_slave.start()  # Automatically responds to read requests
    """
    return create_axi4_slave(
        dut=dut,
        clock=clock,
        prefix=prefix,
        channels=['AR', 'R'],  # Read-only channels
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        memory_model=memory_model,
        timing_config=timing_config,
        log=log,
        **kwargs
    )


def create_axi4_write_slave(dut, clock, prefix: str = 's_axi',
                           id_width: int = 8, addr_width: int = 32, data_width: int = 32, user_width: int = 1,
                           memory_model=None, timing_config=None, log=None, **kwargs) -> AXI4Slave:
    """
    Create an AXI4 Slave configured for write operations only.

    This creates a slave with only the channels needed for write operations: AW, W, B.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: AXI4 signal prefix
        id_width: Width of ID fields
        addr_width: Width of address fields
        data_width: Width of data fields
        user_width: Width of user fields
        memory_model: Optional memory model
        timing_config: Optional timing configuration
        log: Logger instance
        **kwargs: Additional arguments

    Returns:
        AXI4Slave configured for write operations

    Example:
        # Write-only slave
        write_slave = create_axi4_write_slave(
            dut=dut,
            clock=dut.aclk,
            prefix='s_axi'
        )
        await write_slave.start()  # Automatically responds to write requests
    """
    return create_axi4_slave(
        dut=dut,
        clock=clock,
        prefix=prefix,
        channels=['AW', 'W', 'B'],  # Write-only channels
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        memory_model=memory_model,
        timing_config=timing_config,
        log=log,
        **kwargs
    )


# ============================================================================
# UTILITY FUNCTIONS (PRESERVED)
# ============================================================================

def preview_axi4_signals(prefix: str, channels: List[str] = ['AW', 'W', 'B', 'AR', 'R'],
                        bus_name: str = "") -> None:
    """
    Preview what AXI4 signals will be created before actually creating components.

    This function helps with debugging signal connectivity issues by showing
    exactly what signal names the factory functions will expect.

    Args:
        prefix: AXI4 signal prefix
        channels: List of channels to preview
        bus_name: Optional bus identifier

    Example:
        preview_axi4_signals('m_axi', ['AW', 'W'])
        # Prints expected signal names and GAXI parameter mappings
    """
    AXI4SignalMapper.preview_signal_mapping(prefix, channels, bus_name)


def preview_axi4_field_configs(id_width: int = 8, addr_width: int = 32, data_width: int = 32, user_width: int = 1,
                              channels: List[str] = ['AW', 'W', 'B', 'AR', 'R']) -> None:
    """
    Preview what field configurations will be created.

    This function helps with understanding what packet fields will be available
    and their properties before creating the actual components.

    Args:
        id_width: Width of ID fields
        addr_width: Width of address fields
        data_width: Width of data fields
        user_width: Width of user fields
        channels: List of channels to preview

    Example:
        preview_axi4_field_configs(data_width=64)
        # Prints field configurations for all channels
    """
    AXI4FieldConfigHelper.preview_field_configs(id_width, addr_width, data_width, user_width, channels)


def validate_axi4_parameters(prefix: str, channels: List[str],
                           id_width: int, addr_width: int, data_width: int, user_width: int) -> Dict[str, Any]:
    """
    Validate AXI4 parameters before creating components.

    Args:
        prefix: AXI4 signal prefix
        channels: List of channels
        id_width: Width of ID fields
        addr_width: Width of address fields
        data_width: Width of data fields
        user_width: Width of user fields

    Returns:
        Dictionary with validation results
    """
    results = {
        'is_valid': True,
        'errors': [],
        'warnings': []
    }

    # Validate channels
    for channel in channels:
        if not AXI4SignalMapper.validate_axi4_channel(channel):
            results['errors'].append(f"Invalid channel: {channel}")
            results['is_valid'] = False

    # Validate field widths
    width_valid, width_errors = AXI4FieldConfigHelper.validate_axi4_widths(id_width, addr_width, data_width, user_width)
    if not width_valid:
        results['errors'].extend(width_errors)
        results['is_valid'] = False

    # Check for functional completeness
    if 'AW' in channels and 'W' in channels and 'B' not in channels:
        results['warnings'].append("Write channels (AW, W) present but no write response channel (B)")

    if 'AR' in channels and 'R' not in channels:
        results['warnings'].append("Read address channel (AR) present but no read response channel (R)")

    # Check signal prefix format
    if not prefix:
        results['errors'].append("AXI4 prefix cannot be empty")
        results['is_valid'] = False
    elif not prefix.replace('_', '').replace('-', '').isalnum():
        results['warnings'].append(f"AXI4 prefix '{prefix}' contains special characters")

    return results


# ============================================================================
# DOCUMENTATION AND EXAMPLES
# ============================================================================

def example_usage():
    """
    Show how the complete AXI4 factory functions are used.

    This demonstrates the clean, simple interface for both masters and slaves.
    """
    print("AXI4 Complete Factory Functions - Usage Examples")
    print("=" * 60)

    # Example 1: Complete Master/Slave pair
    print("\n1. Complete Master/Slave Pair:")
    print("master = create_axi4_master(dut, clock, 'm_axi')")
    print("slave = create_axi4_slave(dut, clock, 's_axi')")

    # Example 2: Read-only components
    print("\n2. Read-only Components:")
    print("read_master = create_axi4_read_master(dut, clock, 'm_axi')")
    print("read_slave = create_axi4_read_slave(dut, clock, 's_axi')")

    # Example 3: Write-only components
    print("\n3. Write-only Components:")
    print("write_master = create_axi4_write_master(dut, clock, 'm_axi')")
    print("write_slave = create_axi4_write_slave(dut, clock, 's_axi')")

    # Example 4: Custom configurations
    print("\n4. Custom Configurations:")
    print("master = create_axi4_master(")
    print("    dut=dut, clock=dut.aclk, prefix='m_axi',")
    print("    id_width=12, addr_width=64, data_width=128")
    print(")")

    # Example 5: Transaction usage
    print("\n5. Transaction Usage:")
    print("# Master operations")
    print("await master.write_single(addr=0x1000, data=0xDEADBEEF)")
    print("data = await master.read_single(addr=0x1000)")
    print("")
    print("# Slave operations (automatic)")
    print("await slave.start()  # Responds to incoming transactions")

    # Example 6: Signal preview
    print("\n6. Signal Preview for Debugging:")
    print("preview_axi4_signals('m_axi', ['AW', 'W', 'B'])")

    # Example 7: Parameter validation
    print("\n7. Parameter Validation:")
    print("results = validate_axi4_parameters('m_axi', ['AW', 'W', 'B'], 8, 32, 32, 1)")
    print("if not results['is_valid']:")
    print("    print(f\"Errors: {results['errors']}\")")


def get_factory_info() -> Dict[str, Any]:
    """
    Get information about available factory functions.

    Returns:
        Dictionary with factory function documentation
    """
    return {
        'master_factories': {
            'create_axi4_master': {
                'description': 'Create complete AXI4 master with all specified channels',
                'use_case': 'General purpose AXI4 master creation',
                'channels': 'Configurable (default: AW, W, B, AR, R)'
            },
            'create_axi4_read_master': {
                'description': 'Create AXI4 master for read operations only',
                'use_case': 'Read-only testing scenarios',
                'channels': 'AR, R'
            },
            'create_axi4_write_master': {
                'description': 'Create AXI4 master for write operations only',
                'use_case': 'Write-only testing scenarios',
                'channels': 'AW, W, B'
            }
        },
        'slave_factories': {
            'create_axi4_slave': {
                'description': 'Create complete AXI4 slave with all specified channels',
                'use_case': 'General purpose AXI4 slave creation',
                'channels': 'Configurable (default: AW, W, B, AR, R)'
            },
            'create_axi4_read_slave': {
                'description': 'Create AXI4 slave for read operations only',
                'use_case': 'Read-only response scenarios',
                'channels': 'AR, R'
            },
            'create_axi4_write_slave': {
                'description': 'Create AXI4 slave for write operations only',
                'use_case': 'Write-only response scenarios',
                'channels': 'AW, W, B'
            }
        },
        'utility_functions': {
            'preview_axi4_signals': 'Preview expected signal names',
            'preview_axi4_field_configs': 'Preview field configurations',
            'validate_axi4_parameters': 'Validate parameters before creation'
        },
        'design_principles': [
            'Clean, simple interfaces that hide complexity',
            'Complete master/slave factory function coverage',
            'Leverage working GAXI foundation through composition',
            'Sensible defaults for common use cases',
            'Specialized factories for read-only and write-only scenarios'
        ]
    }

