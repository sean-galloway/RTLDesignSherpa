# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: coverage_hooks
# Purpose: Coverage hook integration for GAXI BFMs
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-01-10

"""
Coverage Hooks for GAXI BFMs

Provides automatic coverage sampling when GAXI transactions complete.
This module provides a generic hook that can work with any coverage
collector that implements the expected interface.

Usage:
    # Create coverage hook
    hook = GaxiCoverageHook(coverage_helper)

    # Register with BFMs
    for bfm in [master, slave, monitor]:
        bfm.add_coverage_hook(hook)

    # Or use convenience function
    register_coverage_hooks([master, slave, monitor], coverage_helper)
"""

import logging
from typing import Callable, List, Any, Optional, Protocol


class CoverageProtocol(Protocol):
    """Protocol for coverage helpers that can receive GAXI transaction data."""

    def sample_axi_read(self, burst_type: int, burst_size: int, burst_len: int,
                       address: int = 0, response: int = 0, interface: str = None) -> None:
        """Sample an AXI read transaction."""
        ...

    def sample_axi_write(self, burst_type: int, burst_size: int, burst_len: int,
                        address: int = 0, response: int = 0, interface: str = None) -> None:
        """Sample an AXI write transaction."""
        ...

    def sample_handshake(self, handshake_name: str) -> None:
        """Sample a valid/ready handshake event."""
        ...


class GaxiCoverageHook:
    """
    Coverage hook that extracts transaction information from GAXI packets
    and samples coverage using a coverage helper.

    This hook is designed to work with the CoverageHelper class from
    stream_coverage, but can work with any object that implements the
    CoverageProtocol interface.
    """

    def __init__(self, coverage_helper: Any, log: Optional[logging.Logger] = None):
        """
        Initialize the coverage hook.

        Args:
            coverage_helper: Object with sample_axi_read/sample_axi_write methods
            log: Optional logger for debugging
        """
        self.coverage = coverage_helper
        self.log = log or logging.getLogger("gaxi.coverage_hook")
        self._transaction_count = 0

    def __call__(self, component: Any, transaction: Any, direction: str, interface: str):
        """
        Handle a completed transaction.

        This method is called by the GAXI BFM when a transaction completes.

        Args:
            component: The GAXI component (Master/Slave/Monitor)
            transaction: The completed GAXIPacket
            direction: 'tx' for transmit, 'rx' for receive
            interface: Interface name (from bus_name or title)
        """
        self._transaction_count += 1

        # Extract AXI transaction parameters from the packet
        burst_type = self._get_field(transaction, ['burst', 'arburst', 'awburst'], default=1)
        burst_size = self._get_field(transaction, ['size', 'arsize', 'awsize'], default=6)
        burst_len = self._get_field(transaction, ['len', 'arlen', 'awlen'], default=0)
        address = self._get_field(transaction, ['addr', 'araddr', 'awaddr'], default=0)
        response = self._get_field(transaction, ['resp', 'rresp', 'bresp'], default=0)

        # Determine if this is a read or write based on component type and direction
        is_read = self._is_read_transaction(component, direction)

        # Sample coverage
        if self.coverage is not None:
            if is_read:
                self.coverage.sample_axi_read(
                    burst_type=burst_type,
                    burst_size=burst_size,
                    burst_len=burst_len,
                    address=address,
                    response=response,
                    interface=interface
                )
            else:
                self.coverage.sample_axi_write(
                    burst_type=burst_type,
                    burst_size=burst_size,
                    burst_len=burst_len,
                    address=address,
                    response=response,
                    interface=interface
                )

            # Sample handshake coverage
            handshake_name = f"{interface}_{direction}_handshake"
            if hasattr(self.coverage, 'sample_handshake'):
                self.coverage.sample_handshake(handshake_name)

        if self.log.isEnabledFor(logging.DEBUG):
            self.log.debug(
                f"Coverage sampled: {interface} {direction} "
                f"burst_type={burst_type} size={burst_size} len={burst_len} "
                f"addr=0x{address:X} resp={response}"
            )

    def _get_field(self, transaction: Any, field_names: List[str], default: int = 0) -> int:
        """
        Get a field value from the transaction, trying multiple possible names.

        Args:
            transaction: The transaction packet
            field_names: List of possible field names to try
            default: Default value if field not found

        Returns:
            Field value or default
        """
        for name in field_names:
            if hasattr(transaction, name):
                value = getattr(transaction, name)
                if value is not None:
                    return int(value)
        return default

    def _is_read_transaction(self, component: Any, direction: str) -> bool:
        """
        Determine if this is a read transaction based on component and direction.

        Args:
            component: The GAXI component
            direction: 'tx' or 'rx'

        Returns:
            True if this is a read transaction
        """
        # Check component protocol type if available
        if hasattr(component, 'protocol_type'):
            protocol = component.protocol_type
            if '_ar_' in protocol or '_r_' in protocol:
                return True
            if '_aw_' in protocol or '_w_' in protocol or '_b_' in protocol:
                return False

        # Check component title for hints
        if hasattr(component, 'title'):
            title = component.title.lower()
            if 'read' in title or '_rd' in title or '_ar' in title:
                return True
            if 'write' in title or '_wr' in title or '_aw' in title:
                return False

        # Default based on direction
        # tx from master typically indicates a command (could be read or write)
        # rx typically indicates data/response
        return direction == 'rx'

    @property
    def transaction_count(self) -> int:
        """Get the number of transactions processed by this hook."""
        return self._transaction_count


def extract_gaxi_components(component: Any) -> List[Any]:
    """
    Extract all GAXI sub-components from a component.

    This handles AXI4 interfaces that contain multiple GAXI channels internally.
    For example, AXI4MasterRead contains ar_channel (GAXIMaster) and r_channel (GAXISlave).

    Args:
        component: A GAXI component or an AXI4 interface

    Returns:
        List of GAXI components that support coverage hooks
    """
    gaxi_components = []

    # Check if this component directly supports coverage hooks
    if hasattr(component, 'add_coverage_hook'):
        gaxi_components.append(component)

    # Check for AXI4 interface channel attributes
    # AXI4MasterRead/Write and AXI4SlaveRead/Write have these
    channel_attrs = [
        'ar_channel',  # Address Read channel
        'aw_channel',  # Address Write channel
        'r_channel',   # Read data channel
        'w_channel',   # Write data channel
        'b_channel',   # Write response channel
    ]

    for attr in channel_attrs:
        if hasattr(component, attr):
            channel = getattr(component, attr)
            if channel is not None and hasattr(channel, 'add_coverage_hook'):
                gaxi_components.append(channel)

    # Check for nested components in compliance checkers or other wrappers
    if hasattr(component, 'monitors') and isinstance(component.monitors, dict):
        for monitor in component.monitors.values():
            if hasattr(monitor, 'add_coverage_hook'):
                gaxi_components.append(monitor)

    return gaxi_components


def register_coverage_hooks(components: List[Any], coverage_helper: Any,
                           log: Optional[logging.Logger] = None) -> GaxiCoverageHook:
    """
    Convenience function to register coverage hooks on multiple components.

    Automatically extracts GAXI sub-components from AXI4 interfaces.
    For example, passing an AXI4MasterRead will register hooks on both
    the ar_channel and r_channel.

    Args:
        components: List of GAXI components, AXI4 interfaces, or any
                   component containing GAXI sub-components
        coverage_helper: Coverage helper object
        log: Optional logger

    Returns:
        The created GaxiCoverageHook instance

    Example:
        # Works with GAXI components directly
        hook = register_coverage_hooks(
            [gaxi_master, gaxi_slave],
            coverage_helper
        )

        # Also works with AXI4 interfaces (extracts channels automatically)
        hook = register_coverage_hooks(
            [axi4_master_read, axi4_slave_write],
            coverage_helper
        )
    """
    hook = GaxiCoverageHook(coverage_helper, log=log)
    registered_count = 0

    for component in components:
        # Extract all GAXI sub-components
        gaxi_components = extract_gaxi_components(component)

        if not gaxi_components:
            if log:
                log.warning(f"Component {component} has no GAXI sub-components for coverage")
            continue

        for gaxi_comp in gaxi_components:
            gaxi_comp.add_coverage_hook(hook)
            registered_count += 1

    if log:
        log.info(f"Registered coverage hooks on {registered_count} GAXI components")

    return hook


def create_coverage_hook_from_env(log: Optional[logging.Logger] = None) -> Optional[Callable]:
    """
    Create a coverage hook if coverage is enabled via environment variable.

    This is a convenience function for testbenches that want to automatically
    enable coverage when COVERAGE=1 is set.

    Args:
        log: Optional logger

    Returns:
        GaxiCoverageHook if coverage is enabled, None otherwise
    """
    import os

    if os.environ.get('COVERAGE', '0') != '1':
        return None

    # Try to import the stream coverage helper
    try:
        from projects.components.stream.dv.stream_coverage import CoverageHelper
        test_name = os.environ.get('COVERAGE_TEST_NAME', 'unknown_test')
        coverage_helper = CoverageHelper(test_name, log=log)
        return GaxiCoverageHook(coverage_helper, log=log)
    except ImportError:
        if log:
            log.warning("Could not import stream_coverage, coverage hooks disabled")
        return None
