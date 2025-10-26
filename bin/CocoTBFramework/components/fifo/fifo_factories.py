# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: fifo_factories
# Purpose: FIFO Component Factory Functions
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
FIFO Component Factory Functions

Simplified factory functions for creating FIFO components with improved
type safety, error handling, and reduced code duplication.

Key improvements:
- Added comprehensive type hints
- Consolidated duplicate logic
- Better error handling and validation
- Cleaner parameter handling
- Leverages existing infrastructure (SignalResolver, FieldConfig, etc.)
"""
from typing import Optional, Dict, Any, Union, List

from ..shared.memory_model import MemoryModel
from ..shared.field_config import FieldConfig
from ..shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.scoreboards.fifo_scoreboard import FIFOScoreboard
from .fifo_master import FIFOMaster
from .fifo_slave import FIFOSlave
from .fifo_monitor import FIFOMonitor
from .fifo_command_handler import FIFOCommandHandler


def create_default_field_config(data_width: int = 32,
                                addr_width: int = 0,
                                ctrl_width: int = 0) -> FieldConfig:
    """
    Create default field configuration for FIFO packets.

    Args:
        data_width: Data width in bits
        addr_width: Address width in bits (0 to exclude)
        ctrl_width: Control width in bits (0 to exclude)

    Returns:
        FieldConfig object with specified fields

    Raises:
        ValueError: If any width is negative
    """
    if data_width <= 0:
        raise ValueError(f"data_width must be positive, got {data_width}")
    if addr_width < 0:
        raise ValueError(f"addr_width must be non-negative, got {addr_width}")
    if ctrl_width < 0:
        raise ValueError(f"ctrl_width must be non-negative, got {ctrl_width}")

    if addr_width > 0 and ctrl_width > 0:
        return FieldConfig.create_multi_data(
            addr_width=addr_width,
            ctrl_width=ctrl_width,
            data_width=data_width,
            num_data=1
        )
    elif addr_width > 0:
        return FieldConfig.create_standard(addr_width, data_width)
    else:
        return FieldConfig.create_data_only(data_width)


def _normalize_field_config(field_config: Optional[Union[FieldConfig, Dict[str, Any]]]) -> FieldConfig:
    """
    Internal helper to normalize field configuration parameter.

    Args:
        field_config: Field configuration (FieldConfig, dict, or None)

    Returns:
        FieldConfig object

    Raises:
        TypeError: If field_config is not a supported type
    """
    if field_config is None:
        return create_default_field_config()
    elif isinstance(field_config, dict):
        return FieldConfig.validate_and_create(field_config)
    elif isinstance(field_config, FieldConfig):
        return field_config
    else:
        raise TypeError(f"field_config must be FieldConfig, dict, or None, got {type(field_config)}")


def _get_logger(component_dut, provided_log):
    """Internal helper to get logger from DUT or provided source."""
    return provided_log or getattr(component_dut, '_log', None)


def _validate_mode(mode: str) -> None:
    """Internal helper to validate FIFO mode parameter."""
    if mode not in ['fifo_mux', 'fifo_flop']:
        raise ValueError(f"mode must be 'fifo_mux' or 'fifo_flop', got '{mode}'")


def create_fifo_master(dut,
                        title: str,
                        clock,
                        field_config: Optional[Union[FieldConfig, Dict[str, Any]]] = None,
                        randomizer: Optional[FlexRandomizer] = None,
                        memory_model: Optional[MemoryModel] = None,
                        log=None,
                        **kwargs) -> FIFOMaster:
    """
    Create a FIFO Master component with clean parameter handling.

    Args:
        dut: Device under test
        title: Component title
        clock: Clock signal
        field_config: Field configuration (default: 32-bit data field)
        randomizer: Timing randomizer (optional)
        memory_model: Memory model for data storage (optional)
        log: Logger instance (optional, uses DUT logger if None)
        **kwargs: Additional arguments passed to FIFOMaster

    Returns:
        FIFOMaster instance

    Raises:
        TypeError: If field_config is not a supported type
        ValueError: If title is empty
    """
    if not title or not isinstance(title, str):
        raise ValueError(f"title must be a non-empty string, got {repr(title)}")

    field_config = _normalize_field_config(field_config)
    log = _get_logger(dut, log)

    master = FIFOMaster(
        dut=dut,
        title=title,
        prefix="",  # SignalResolver handles signal discovery
        clock=clock,
        field_config=field_config,
        randomizer=randomizer,
        log=log,
        **kwargs
    )

    if memory_model:
        master.memory_model = memory_model

    return master


def create_fifo_slave(dut,
                        title: str,
                        clock,
                        field_config: Optional[Union[FieldConfig, Dict[str, Any]]] = None,
                        randomizer: Optional[FlexRandomizer] = None,
                        memory_model: Optional[MemoryModel] = None,
                        log=None,
                        mode: str = 'fifo_mux',
                        **kwargs) -> FIFOSlave:
    """
    Create a FIFO Slave component with clean parameter handling.

    Args:
        dut: Device under test
        title: Component title
        clock: Clock signal
        field_config: Field configuration (default: 32-bit data field)
        randomizer: Timing randomizer (optional)
        memory_model: Memory model for data storage (optional)
        log: Logger instance (optional, uses DUT logger if None)
        mode: Operating mode ('fifo_mux', 'fifo_flop')
        **kwargs: Additional arguments passed to FIFOSlave

    Returns:
        FIFOSlave instance

    Raises:
        TypeError: If field_config is not a supported type
        ValueError: If mode is not valid or title is empty
    """
    if not title or not isinstance(title, str):
        raise ValueError(f"title must be a non-empty string, got {repr(title)}")
    _validate_mode(mode)

    field_config = _normalize_field_config(field_config)
    log = _get_logger(dut, log)

    slave = FIFOSlave(
        dut=dut,
        title=title,
        prefix="",  # SignalResolver handles signal discovery
        clock=clock,
        field_config=field_config,
        randomizer=randomizer,
        log=log,
        mode=mode,
        **kwargs
    )

    if memory_model:
        slave.memory_model = memory_model

    return slave


def create_fifo_monitor(dut,
                        title: str,
                        clock,
                        field_config: Optional[Union[FieldConfig, Dict[str, Any]]] = None,
                        is_slave: bool = False,
                        log=None,
                        mode: str = 'fifo_mux',
                        **kwargs) -> FIFOMonitor:
    """
    Create a FIFO Monitor component with clean parameter handling.

    Args:
        dut: Device under test
        title: Component title
        clock: Clock signal
        field_config: Field configuration (default: 32-bit data field)
        is_slave: If True, monitor read side; if False, monitor write side
        log: Logger instance (optional, uses DUT logger if None)
        mode: Operating mode ('fifo_mux', 'fifo_flop')
        **kwargs: Additional arguments passed to FIFOMonitor

    Returns:
        FIFOMonitor instance

    Raises:
        TypeError: If field_config is not a supported type
        ValueError: If mode is not valid or title is empty
    """
    if not title or not isinstance(title, str):
        raise ValueError(f"title must be a non-empty string, got {repr(title)}")
    _validate_mode(mode)

    field_config = _normalize_field_config(field_config)
    log = _get_logger(dut, log)

    return FIFOMonitor(
        dut=dut,
        title=title,
        prefix="",  # SignalResolver handles signal discovery
        clock=clock,
        field_config=field_config,
        is_slave=is_slave,
        log=log,
        mode=mode,
        **kwargs
    )


def create_fifo_scoreboard(name: str,
                            field_config: Optional[Union[FieldConfig, Dict[str, Any]]] = None,
                            log=None) -> FIFOScoreboard:
    """
    Create a FIFO Scoreboard with configuration.

    Args:
        name: Scoreboard name
        field_config: Field configuration (default: 32-bit data field)
        log: Logger instance

    Returns:
        FIFOScoreboard instance

    Raises:
        TypeError: If field_config is not a supported type
        ValueError: If name is empty
    """
    if not name or not isinstance(name, str):
        raise ValueError(f"name must be a non-empty string, got {repr(name)}")

    field_config = _normalize_field_config(field_config)
    return FIFOScoreboard(name, field_config, log=log)


def create_fifo_command_handler(master: FIFOMaster,
                                slave: FIFOSlave,
                                log=None) -> FIFOCommandHandler:
    """
    Create a FIFO Command Handler for managing sequences.

    Args:
        master: FIFOMaster instance
        slave: FIFOSlave instance
        log: Logger instance (uses master's or slave's logger if None)

    Returns:
        FIFOCommandHandler instance

    Raises:
        TypeError: If master or slave are not the correct types
    """
    if not isinstance(master, FIFOMaster):
        raise TypeError(f"master must be FIFOMaster instance, got {type(master)}")
    if not isinstance(slave, FIFOSlave):
        raise TypeError(f"slave must be FIFOSlave instance, got {type(slave)}")

    log = log or getattr(master, 'log', None) or getattr(slave, 'log', None)
    return FIFOCommandHandler(master, slave, log=log)


def create_memory_model(num_lines: int,
                        bytes_per_line: int = 4,
                        log=None,
                        preset_values: Optional[List[int]] = None,
                        debug: bool = False) -> MemoryModel:
    """
    Create a memory model using existing MemoryModel infrastructure.

    Args:
        num_lines: Number of memory lines
        bytes_per_line: Bytes per memory line
        log: Logger instance
        preset_values: Optional initial values for memory
        debug: Enable detailed debug logging

    Returns:
        MemoryModel instance

    Raises:
        ValueError: If parameters are invalid
    """
    if num_lines <= 0:
        raise ValueError(f"num_lines must be positive, got {num_lines}")
    if bytes_per_line <= 0:
        raise ValueError(f"bytes_per_line must be positive, got {bytes_per_line}")

    return MemoryModel(
        num_lines=num_lines,
        bytes_per_line=bytes_per_line,
        log=log,
        preset_values=preset_values,
        debug=debug
    )


def create_fifo_components(dut,
                            clock,
                            title_prefix: str = "",
                            field_config: Optional[Union[FieldConfig, Dict[str, Any]]] = None,
                            memory_model: Optional[MemoryModel] = None,
                            log=None,
                            mode: str = 'fifo_mux',
                            fifo_capacity: int = 8) -> Dict[str, Any]:
    """
    Create a complete set of FIFO components.

    Args:
        dut: Device under test
        clock: Clock signal
        title_prefix: Prefix for component titles
        field_config: Field configuration (default: 32-bit data field)
        memory_model: Memory model for data storage (created if None)
        log: Logger instance (uses DUT logger if None)
        mode: Operating mode for slave/monitor
        fifo_capacity: FIFO capacity in entries for memory model

    Returns:
        Dictionary containing all created components:
        - master: FIFOMaster
        - slave: FIFOSlave
        - master_monitor: FIFOMonitor
        - slave_monitor: FIFOMonitor
        - scoreboard: FIFOScoreboard
        - command_handler: FIFOCommandHandler
        - memory_model: MemoryModel

    Raises:
        TypeError: If field_config is not a supported type
        ValueError: If mode or parameters are invalid
    """
    _validate_mode(mode)
    if fifo_capacity <= 0:
        raise ValueError(f"fifo_capacity must be positive, got {fifo_capacity}")

    field_config = _normalize_field_config(field_config)
    log = _get_logger(dut, log)

    # Create memory model if needed
    if memory_model is None:
        memory_model = create_memory_model(
            num_lines=fifo_capacity,
            bytes_per_line=4,  # 32-bit default
            log=log
        )

    # Create all components using the individual factory functions
    master = create_fifo_master(
        dut, f"{title_prefix}Master", clock,
        field_config=field_config,
        memory_model=memory_model,
        log=log
    )

    slave = create_fifo_slave(
        dut, f"{title_prefix}Slave", clock,
        field_config=field_config,
        memory_model=memory_model,
        log=log,
        mode=mode
    )

    master_monitor = create_fifo_monitor(
        dut, f"{title_prefix}MasterMonitor", clock,
        field_config=field_config,
        is_slave=False,
        log=log,
        mode=mode
    )

    slave_monitor = create_fifo_monitor(
        dut, f"{title_prefix}SlaveMonitor", clock,
        field_config=field_config,
        is_slave=True,
        log=log,
        mode=mode
    )

    scoreboard = create_fifo_scoreboard(
        f"{title_prefix}Scoreboard",
        field_config=field_config,
        log=log
    )

    command_handler = create_fifo_command_handler(
        master,
        slave,
        log=log
    )

    return {
        'master': master,
        'slave': slave,
        'master_monitor': master_monitor,
        'slave_monitor': slave_monitor,
        'scoreboard': scoreboard,
        'command_handler': command_handler,
        'memory_model': memory_model
    }


# Convenience functions for common configurations
def create_simple_fifo_test(dut,
                            clock,
                            data_width: int = 32) -> Dict[str, Any]:
    """
    Create a simple FIFO test setup with standard components.

    Args:
        dut: Device under test
        clock: Clock signal
        data_width: Data width in bits

    Returns:
        Dictionary with master, slave, and command_handler

    Raises:
        ValueError: If data_width is invalid
    """
    if data_width <= 0:
        raise ValueError(f"data_width must be positive, got {data_width}")

    field_config = create_default_field_config(data_width=data_width)

    master = create_fifo_master(dut, "Master", clock, field_config=field_config)
    slave = create_fifo_slave(dut, "Slave", clock, field_config=field_config)
    command_handler = create_fifo_command_handler(master, slave)

    return {
        'master': master,
        'slave': slave,
        'command_handler': command_handler
    }


def create_fifo_with_monitors(dut,
                                clock,
                                data_width: int = 32,
                                mode: str = 'fifo_mux') -> Dict[str, Any]:
    """
    Create FIFO components with monitors for comprehensive observation.

    Args:
        dut: Device under test
        clock: Clock signal
        data_width: Data width in bits
        mode: Operating mode

    Returns:
        Dictionary with all components including monitors

    Raises:
        ValueError: If parameters are invalid
    """
    if data_width <= 0:
        raise ValueError(f"data_width must be positive, got {data_width}")
    _validate_mode(mode)

    return create_fifo_components(
        dut=dut,
        clock=clock,
        field_config=create_default_field_config(data_width=data_width),
        mode=mode
    )


def create_fifo_test_environment(dut,
                                clock,
                                data_width: int = 32,
                                addr_width: int = 0,
                                mode: str = 'fifo_mux',
                                fifo_capacity: int = 8,
                                include_monitors: bool = True,
                                title_prefix: str = "") -> Dict[str, Any]:
    """
    Create a complete FIFO test environment with all components.

    Args:
        dut: Device under test
        clock: Clock signal
        data_width: Data width in bits
        addr_width: Address width in bits (0 for data-only)
        mode: Operating mode
        fifo_capacity: FIFO capacity for memory model
        include_monitors: Whether to include monitor components
        title_prefix: Prefix for component names

    Returns:
        Dictionary with all test environment components

    Raises:
        ValueError: If parameters are invalid
    """
    if data_width <= 0:
        raise ValueError(f"data_width must be positive, got {data_width}")
    if addr_width < 0:
        raise ValueError(f"addr_width must be non-negative, got {addr_width}")
    _validate_mode(mode)
    if fifo_capacity <= 0:
        raise ValueError(f"fifo_capacity must be positive, got {fifo_capacity}")

    # Create field configuration
    field_config = create_default_field_config(
        data_width=data_width,
        addr_width=addr_width
    )

    if include_monitors:
        # Create full environment with monitors
        return create_fifo_components(
            dut=dut,
            clock=clock,
            title_prefix=title_prefix,
            field_config=field_config,
            mode=mode,
            fifo_capacity=fifo_capacity
        )
    else:
        # Create minimal environment without monitors
        log = _get_logger(dut, None)

        memory_model = create_memory_model(
            num_lines=fifo_capacity,
            bytes_per_line=4,
            log=log
        )

        master = create_fifo_master(
            dut, f"{title_prefix}Master", clock,
            field_config=field_config,
            memory_model=memory_model,
            log=log
        )

        slave = create_fifo_slave(
            dut, f"{title_prefix}Slave", clock,
            field_config=field_config,
            memory_model=memory_model,
            log=log,
            mode=mode
        )

        command_handler = create_fifo_command_handler(master, slave, log=log)

        return {
            'master': master,
            'slave': slave,
            'command_handler': command_handler,
            'memory_model': memory_model
        }
