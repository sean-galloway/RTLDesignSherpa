# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: WavedromSignalBinder
# Purpose: Wavedrom Signal Binding using SignalResolver Methodology
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Wavedrom Signal Binding using SignalResolver Methodology

Automatically discovers and binds signals for wavedrom temporal constraint matching
using the proven SignalResolver pattern-matching infrastructure.

This provides a thin wavedrom-specific layer that translates between SignalResolver
results and TemporalConstraintSolver's signal binding format.
"""

from ..shared.signal_mapping_helper import SignalResolver
from ..shared.field_config import FieldConfig
from typing import Optional, Dict, TYPE_CHECKING

if TYPE_CHECKING:
    from .constraint_solver import TemporalConstraintSolver


class WavedromSignalBinder:
    """
    Automatically bind signals for wavedrom using SignalResolver.

    This class provides automatic signal discovery with manual override capability
    for wavedrom temporal constraint matching. It handles:

    - Pattern-based automatic signal discovery
    - Manual signal_map override
    - Rich table visualization of discovered signals
    - Comprehensive error reporting with troubleshooting guidance
    - Integration with TemporalConstraintSolver

    Usage:
        binder = WavedromSignalBinder(
            dut=dut,
            log=log,
            protocol_type='gaxi',
            signal_prefix='wr_',
            field_config=field_config
        )
        num_bound = binder.bind_to_solver(wave_solver)
    """

    def __init__(self, dut, log, protocol_type: str,
                 signal_prefix: str = '',
                 bus_name: str = '',
                 pkt_prefix: str = '',
                 field_config: Optional[FieldConfig] = None,
                 signal_map: Optional[Dict[str, str]] = None,
                 super_debug: bool = False):
        """
        Initialize wavedrom signal binder.

        Args:
            dut: CocoTB DUT handle
            log: Logger instance
            protocol_type: Protocol type ('gaxi', 'apb', 'axis', 'axi4_read', 'axi4_write')
            signal_prefix: Prefix for all signals (e.g., 's_', 'wr_', 'm_axi_')
            bus_name: Bus/channel name for additional prefix handling
            pkt_prefix: Packet field prefix for multi-field protocols
            field_config: FieldConfig for multi-signal modes (required if multi_sig=True)
            signal_map: Manual override dict. Keys: simplified signal names ('valid', 'ready', 'data', etc.)
                       Values: actual DUT signal names. If provided, bypasses automatic discovery.
            super_debug: Enable detailed signal resolution debugging
        """
        self.dut = dut
        self.log = log
        self.protocol_type = protocol_type
        self.signal_prefix = signal_prefix
        self.bus_name = bus_name
        self.pkt_prefix = pkt_prefix
        self.field_config = field_config
        self.signal_map = signal_map
        self.super_debug = super_debug

        # Construct wavedrom protocol type for SignalResolver
        wavedrom_protocol = f"{protocol_type}_wavedrom"

        # Determine multi_sig mode: Only True if field_config has multiple fields
        # For single-field protocols (like GAXI with 1 data field), use multi_sig=False
        multi_sig_mode = False
        if field_config is not None:
            # Check if field_config has more than 1 field
            num_fields = len(list(field_config.fields()))
            multi_sig_mode = (num_fields > 1)

        # Create SignalResolver with wavedrom protocol configuration
        self.resolver = SignalResolver(
            protocol_type=wavedrom_protocol,
            dut=dut,
            bus=None,  # Not needed for wavedrom (monitoring only)
            log=log,
            component_name=f"{protocol_type.upper()} WaveDrom",
            prefix=signal_prefix,
            field_config=field_config,
            multi_sig=multi_sig_mode,
            bus_name=bus_name,
            pkt_prefix=pkt_prefix,
            signal_map=signal_map,
            super_debug=super_debug
        )

        # Resolve all signals - this displays Rich table and validates
        self.resolver.get_signal_lists()

        self.log.info(f"WavedromSignalBinder initialized for {protocol_type}")

    def bind_to_solver(self, solver: 'TemporalConstraintSolver') -> int:
        """
        Bind all resolved signals to TemporalConstraintSolver.

        This method iterates through all signals discovered by SignalResolver
        and binds them to the solver using add_signal_binding().

        Args:
            solver: TemporalConstraintSolver instance to bind signals to

        Returns:
            Number of signals successfully bound
        """
        bound_count = 0

        for logical_name, signal_obj in self.resolver.resolved_signals.items():
            if signal_obj is None:
                continue

            # Get actual signal name from DUT
            signal_name = self.resolver._find_signal_name(signal_obj)

            # Get FieldDefinition if available
            field_def = self._get_field_definition(logical_name)

            # Bind to solver using actual signal name
            solver.add_signal_binding(signal_name, signal_name, field_def)
            bound_count += 1

            if self.super_debug:
                self.log.debug(f"Bound signal '{signal_name}' (logical: '{logical_name}')")

        self.log.info(f"✓ Auto-bound {bound_count} signals for {self.protocol_type} wavedrom")
        return bound_count

    def _get_field_definition(self, logical_name: str):
        """
        Extract FieldDefinition from logical name if available.

        For multi-signal protocols, SignalResolver creates logical names like
        'field_XXX_sig' where XXX is the field name. This method extracts
        the FieldDefinition for that field from the FieldConfig.

        Args:
            logical_name: Logical signal name from SignalResolver

        Returns:
            FieldDefinition if found and available, None otherwise
        """
        if not self.field_config:
            return None

        # Handle field signals (field_XXX_sig format from SignalResolver)
        if logical_name.startswith('field_') and logical_name.endswith('_sig'):
            field_name = logical_name.replace('field_', '').replace('_sig', '')
            if self.field_config.has_field(field_name):
                return self.field_config.get_field(field_name)

        # Handle protocol-specific signal names that map to fields
        # For protocols like APB where signal names are actual field names
        if self.field_config.has_field(logical_name):
            return self.field_config.get_field(logical_name)

        return None

    def get_stats(self) -> Dict:
        """
        Get signal resolution statistics.

        Returns:
            Dictionary with resolution statistics from SignalResolver
        """
        return self.resolver.get_stats()
