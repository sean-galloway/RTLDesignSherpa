# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FIFOComponentBase
# Purpose: FIFOComponentBase - Unified base class for all FIFO components
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
FIFOComponentBase - Unified base class for all FIFO components

This base class consolidates common functionality across FIFOMaster, FIFOMonitor,
and FIFOSlave, eliminating code duplication while preserving exact APIs and timing.

All existing parameters are preserved and used exactly as before.

FIXED: Now passes resolved signals directly to DataStrategies, eliminating guesswork.
ADDED: Optional signal_map parameter for manual signal mapping override.
"""

from ..shared.field_config import FieldConfig
from ..shared.signal_mapping_helper import SignalResolver
from ..shared.data_strategies import DataCollectionStrategy, DataDrivingStrategy
from ..shared.flex_randomizer import FlexRandomizer


class FIFOComponentBase:
    """
    Unified base class for all FIFO components (Master, Monitor, Slave).

    Consolidates common initialization, signal resolution, data handling,
    and packet management while preserving component-specific functionality.

    FIXED: Data strategies now receive resolved signals directly from SignalResolver
    instead of doing their own signal discovery.
    
    ADDED: Optional signal_map parameter for manual signal override.
    """

    def __init__(self, dut, title, prefix, clock, field_config,
                    protocol_type,  # Must be specified by subclass
                    mode='fifo_mux',
                    bus_name='',
                    pkt_prefix='',
                    multi_sig=False,
                    randomizer=None,
                    memory_model=None,
                    log=None,
                    super_debug=False,
                    signal_map=None,  # NEW: Optional manual signal mapping
                    **kwargs):
        """
        Initialize common FIFO component functionality.

        Args:
            dut: Device under test
            title: Component title/name
            prefix: Bus prefix
            clock: Clock signal
            field_config: Field configuration (FieldConfig or dict)
            protocol_type: Protocol type ('fifo_master' or 'fifo_slave')
            mode: FIFO mode ('fifo_mux', 'fifo_flop')
            bus_name: Bus/channel name
            pkt_prefix: Packet field prefix
            multi_sig: Whether using multi-signal mode
            randomizer: Optional randomizer for timing
            memory_model: Optional memory model for transactions
            log: Logger instance
            super_debug: Enable detailed debugging
            signal_map: Optional dict mapping simplified signal names to DUT signal names.
                        Keys: 'write', 'full', 'read', 'empty', 'data' (or field names for multi_sig=True)
                        Values: DUT signal name strings
                        If provided, bypasses automatic signal discovery.
            **kwargs: Additional arguments for specific component types
        """
        # Store all parameters exactly as provided - no changes to APIs
        self.title = title
        self.clock = clock
        self.mode = mode
        self.super_debug = super_debug
        self.bus_name = bus_name
        self.pkt_prefix = pkt_prefix
        self.use_multi_signal = multi_sig
        self.memory_model = memory_model
        self.signal_map = signal_map  # NEW: Store signal map

        # Validate protocol_type
        if protocol_type not in ['fifo_master', 'fifo_slave']:
            raise ValueError(f"protocol_type must be 'fifo_master' or 'fifo_slave', got: {protocol_type}")
        self.protocol_type = protocol_type

        # Normalize field_config - handle dict conversion uniformly
        self.field_config = self._normalize_field_config(field_config)

        # Set up logging early (will be overridden by cocotb parent if None)
        self.log = log

        # Set up randomizer with defaults if needed
        self.randomizer = self._setup_randomizer(randomizer, protocol_type)

        # Modern infrastructure - signal resolution
        self.signal_resolver = SignalResolver(
            protocol_type=protocol_type,
            dut=dut,
            bus=None,  # Set after cocotb parent class init
            log=self.log,
            component_name=title,
            prefix=prefix,
            field_config=self.field_config,
            multi_sig=self.use_multi_signal,
            bus_name=self.bus_name,
            pkt_prefix=self.pkt_prefix,
            mode=mode,
            super_debug=super_debug,
            signal_map=signal_map  # NEW: Pass signal map to resolver
        )

        # Get signal lists for cocotb Bus initialization
        self._signals, self._optional_signals = self.signal_resolver.get_signal_lists()

        # Data strategies - will be set up after signal resolution is complete
        self.data_collector = None
        self.data_driver = None

        # Store additional kwargs for subclass use
        self._component_kwargs = kwargs

    def _normalize_field_config(self, field_config):
        """
        Standardize field_config handling across all components.

        Args:
            field_config: FieldConfig object, dict, or None

        Returns:
            FieldConfig object
        """
        if isinstance(field_config, dict):
            return FieldConfig.validate_and_create(field_config)
        elif field_config is None:
            return FieldConfig.create_data_only()
        elif isinstance(field_config, FieldConfig):
            return field_config
        else:
            raise TypeError(f"field_config must be FieldConfig, dict, or None, got {type(field_config)}")

    def _setup_randomizer(self, randomizer, protocol_type):
        """
        Set up randomizer with appropriate defaults for component type.

        Args:
            randomizer: Provided randomizer or None
            protocol_type: Component protocol type

        Returns:
            FlexRandomizer instance
        """
        if randomizer is not None:
            return randomizer

        # Default constraints based on component type
        if protocol_type == 'fifo_master':
            default_constraints = {
                'write_delay': ([(0, 0), (1, 8), (9, 20)], [5, 2, 1])
            }
        else:  # fifo_slave
            default_constraints = {
                'read_delay': ([(0, 1), (2, 8), (9, 30)], [5, 2, 1])
            }

        return FlexRandomizer(default_constraints)

    def complete_base_initialization(self, bus=None):
        """
        Complete initialization after cocotb parent class setup.

        This must be called by subclasses after their cocotb parent class
        (BusDriver/BusMonitor) initialization is complete.

        Args:
            bus: Bus object from cocotb parent class
        """
        # Apply signal mappings now that bus is available
        if bus is not None:
            self.signal_resolver.bus = bus
            self.signal_resolver.apply_to_component(self)

        # Set up data strategies now that signals are resolved
        self._setup_data_strategies()

        # Log successful initialization
        side_description = "slave" if self.protocol_type == 'fifo_slave' else "master"
        signal_source = "manual signal_map" if self.signal_map else "automatic discovery"
        if self.log:
            self.log.info(f"FIFOComponentBase '{self.title}' initialized: {side_description} side, "
                        f"mode={self.mode}, multi_sig={self.use_multi_signal}, signals={signal_source}")

    def _setup_data_strategies(self):
        """
        Set up data collection and driving strategies based on component needs.

        FIXED: Now passes resolved signals directly to DataStrategies instead of
        letting them do their own signal discovery.
        """
        # Get the resolved signals from SignalResolver
        resolved_signals = self.signal_resolver.resolved_signals

        # Data collection strategy - used by all components for monitoring
        self.data_collector = DataCollectionStrategy(
            component=self,
            field_config=self.field_config,
            use_multi_signal=self.use_multi_signal,
            log=self.log,
            resolved_signals=resolved_signals  # FIXED: Pass resolved signals directly
        )

        # Data driving strategy - used by masters and slaves that drive signals
        self.data_driver = DataDrivingStrategy(
            component=self,
            field_config=self.field_config,
            use_multi_signal=self.use_multi_signal,
            log=self.log,
            resolved_signals=resolved_signals  # FIXED: Pass resolved signals directly
        )

    def get_data_dict_unified(self):
        """
        Get current data from signals with automatic field unpacking.

        Uses unified DataCollectionStrategy for consistent behavior.

        Returns:
            Dictionary of field values, properly unpacked
        """
        if self.data_collector:
            return self.data_collector.collect_and_unpack_data()
        return {}

    def drive_transaction_unified(self, transaction):
        """
        Drive transaction data using unified DataDrivingStrategy.

        Args:
            transaction: Transaction to drive

        Returns:
            True if successful, False otherwise
        """
        if self.data_driver:
            return self.data_driver.drive_transaction(transaction)
        return False

    def clear_signals_unified(self):
        """Clear all data signals using unified strategy."""
        if self.data_driver:
            self.data_driver.clear_signals()

    def write_to_memory_unified(self, transaction):
        """
        Write transaction to memory using base MemoryModel directly.

        Args:
            transaction: Transaction to write

        Returns:
            (success, error_message) tuple
        """
        if self.memory_model:
            return self.memory_model.write_transaction(
                transaction,
                component_name=self.title
            )
        return False, "No memory model available"

    def read_from_memory_unified(self, transaction, update_transaction=True):
        """
        Read data from memory using base MemoryModel directly.

        Args:
            transaction: Transaction with address to read
            update_transaction: Whether to update transaction with read data

        Returns:
            (success, data, error_message) tuple
        """
        if self.memory_model:
            return self.memory_model.read_transaction(
                transaction,
                update_transaction=update_transaction,
                component_name=self.title
            )
        return False, None, "No memory model available"

    def get_base_stats_unified(self):
        """
        Get comprehensive base statistics common to all components.

        Returns:
            Dictionary containing base statistics
        """
        base_stats = {
            'component_type': self.protocol_type,
            'mode': self.mode,
            'multi_signal': self.use_multi_signal,
            'field_count': len(self.field_config) if self.field_config else 0,
            'title': self.title,
            'signal_mapping_source': 'manual' if self.signal_map else 'automatic'  # NEW
        }

        # Add signal resolver stats
        if self.signal_resolver:
            base_stats['signal_resolver_stats'] = self.signal_resolver.get_stats()

        # Add data strategy stats
        if self.data_collector:
            base_stats['data_collector_stats'] = self.data_collector.get_stats()
        if self.data_driver:
            base_stats['data_driver_stats'] = self.data_driver.get_stats()

        # Add memory stats if available
        if self.memory_model:
            base_stats['memory_stats'] = self.memory_model.get_stats()

        return base_stats

    def set_randomizer(self, randomizer):
        """
        Set new randomizer for timing control.

        Args:
            randomizer: FlexRandomizer instance
        """
        self.randomizer = randomizer
        if self.log:
            self.log.info(f"FIFOComponentBase '{self.title}': Set new randomizer")