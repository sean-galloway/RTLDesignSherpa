"""
Simplified FIFO Signal Mapping - Pattern Matching Against Top-Level Ports

Uses pattern matching against actual DUT ports with parameter combinations
to find the correct signal mappings automatically.
"""
from typing import Dict, List, Optional, Any, Union
from itertools import product
from rich.console import Console
from rich.table import Table


# Standard FIFO modes (kept for parameter passing to RTL)
FIFO_VALID_MODES = ['fifo_mux', 'fifo_flop']

# Simplified base signal patterns
FIFO_BASE_PATTERNS = {
    # Write-side patterns (for masters and write monitors)
    'write_base': [
        '{in_prefix}{bus_name}write',
    ],
    'wr_data_base': [
        '{in_prefix}{bus_name}wr_data',
        '{in_prefix}{bus_name}data',
    ],
    'wr_field_base': [
        '{in_prefix}{bus_name}{pkt_prefix}{field_name}',
        '{in_prefix}{bus_name}{pkt_prefix}wr_{field_name}',
    ],
    'full_base': [
        '{out_prefix}{bus_name}wr_full',
        '{out_prefix}{bus_name}full'
    ],

    # Read-side patterns (for slaves and read monitors)
    'read_base': [
        '{in_prefix}{bus_name}read'
    ],
    'rd_data_base': [
        '{out_prefix}{bus_name}rd_data',
        '{out_prefix}{bus_name}data'
    ],
    'rd_field_base': [
        '{out_prefix}{bus_name}{pkt_prefix}{field_name}',
        '{out_prefix}{bus_name}{pkt_prefix}rd_{field_name}'
    ],
    'empty_base': [
        '{out_prefix}{bus_name}rd_empty',
        '{out_prefix}{bus_name}empty'
    ]
}

PROTOCOL_SIGNAL_CONFIGS = {
    'fifo_master': {
        'signal_map': {
            'i_write':   FIFO_BASE_PATTERNS['write_base'],
            'o_wr_full': FIFO_BASE_PATTERNS['full_base']
        },
        'optional_signal_map': {
            # No mode-aware patterns needed - RTL handles timing internally
            'multi_sig_false': FIFO_BASE_PATTERNS['wr_data_base'],
            'multi_sig_true':  FIFO_BASE_PATTERNS['wr_field_base']
        }
    },

    'fifo_slave': {
        'signal_map': {
            'i_read':     FIFO_BASE_PATTERNS['read_base'],
            'o_rd_empty': FIFO_BASE_PATTERNS['empty_base']
        },
        'optional_signal_map': {
            # Single read data pattern - no more mux vs flop complexity!
            'multi_sig_false': FIFO_BASE_PATTERNS['rd_data_base'],
            'multi_sig_true':  FIFO_BASE_PATTERNS['rd_field_base']
        }
    }

    # Note: No special monitor configurations needed!
    # Write monitors use 'fifo_master', read monitors use 'fifo_slave'
}


def get_top_level_ports(dut):
    """Get all top-level input/output/inout ports of the DUT"""
    ports = {}

    print("="*80)
    for port_name in dir(dut):
        if not port_name.startswith('_'):  # Skip private attributes
            try:
                port = getattr(dut, port_name)
                if hasattr(port, 'value'):  # Only include signals with values
                    ports[port_name] = port
                    print(f"Port-->:{port_name}:")
            except (AttributeError, TypeError):
                continue
    print("="*80)

    return ports


class SignalResolver:
    """
    Signal resolver using pattern matching against actual top-level DUT ports.

    Uses parameter combinations to generate all possible signal name patterns
    and matches them against the actual DUT ports.
    """

    def __init__(self, protocol_type: str, dut, bus, log, component_name: str,
                field_config=None, multi_sig: bool = False,
                in_prefix: str = 'i_', out_prefix: str = 'o_',
                bus_name: str = '', pkt_prefix: str = '', mode: str = None,
                super_debug: bool = False):
        """
        Initialize signal resolver with pattern matching.

        Args:
            protocol_type: Protocol type ('fifo_master', 'fifo_slave')
            dut: Device under test
            bus: Bus object from BusDriver/BusMonitor (can be None initially)
            log: Logger instance (can be None)
            component_name: Component name for error messages
            field_config: Field configuration (required for multi_sig=True)
            multi_sig: Whether using multi-signal mode
            in_prefix: Input signal prefix
            out_prefix: Output signal prefix
            bus_name: Bus/channel name
            pkt_prefix: Packet field prefix
            mode: FIFO mode (kept for RTL parameter)
            super_debug: Enable detailed signal resolution debugging
        """
        self.protocol_type = protocol_type
        self.dut = dut
        self.bus = bus
        self.log = log
        self.component_name = component_name
        self.field_config = field_config
        self.multi_sig = multi_sig
        self.mode = mode
        self.super_debug = super_debug

        # Storage for log messages (in case log is None)
        self.log_messages = []

        # Validate protocol type
        if protocol_type not in PROTOCOL_SIGNAL_CONFIGS:
            available = list(PROTOCOL_SIGNAL_CONFIGS.keys())
            raise ValueError(f"Unknown protocol type '{protocol_type}'. Available: {available}")

        # Get protocol configuration
        self.config = PROTOCOL_SIGNAL_CONFIGS[protocol_type]

        # Validate field_config for multi_sig mode
        if multi_sig and not field_config:
            raise ValueError(f"field_config is required when multi_sig=True for {component_name}")

        # Get top-level ports from DUT
        self.top_level_ports = get_top_level_ports(dut)
        self._log_info(f"Found {len(self.top_level_ports)} top-level ports")
        if len(self.top_level_ports) > 0:
            for port_name in sorted(self.top_level_ports.keys()):
                self._log_debug(f"Available port: {port_name}")

        # Generate parameter combinations
        self.param_combinations = self._generate_parameter_combinations(
            in_prefix, out_prefix, bus_name, pkt_prefix
        )
        self._log_debug(f"Generated {len(self.param_combinations)} parameter combinations")

        # Storage for resolved signals
        self.resolved_signals = {}
        self.signal_conflicts = {}  # Track multiple matches
        self.missing_signals = []

        # Resolve all signals immediately
        self._resolve_all_signals()

        # Display results and validate
        self._display_signal_mapping()
        self._validate_required_signals()

        # Prepare signal lists for cocotb Bus initialization
        self._signals, self._optional_signals = self._prepare_signal_lists()

    def _log_debug(self, message: str):
        """Log debug message with fallback storage."""
        full_msg = f"{self.component_name}: {message}"
        self.log_messages.append(('DEBUG', full_msg))
        if self.log:
            self.log.debug(full_msg)

    def _log_info(self, message: str):
        """Log info message with fallback storage."""
        full_msg = f"{self.component_name}: {message}"
        self.log_messages.append(('INFO', full_msg))
        if self.log:
            self.log.info(full_msg)
        else:
            print(f"INFO: {full_msg}")

    def _log_warning(self, message: str):
        """Log warning message with fallback storage."""
        full_msg = f"{self.component_name}: {message}"
        self.log_messages.append(('WARNING', full_msg))
        if self.log:
            self.log.warning(full_msg)
        else:
            print(f"WARNING: {full_msg}")

    def _log_error(self, message: str):
        """Log error message with fallback storage."""
        full_msg = f"{self.component_name}: {message}"
        self.log_messages.append(('ERROR', full_msg))
        if self.log:
            self.log.error(full_msg)
        else:
            print(f"ERROR: {full_msg}")

    def dump_log_messages(self):
        """Dump all stored log messages."""
        print(f"\n=== SignalResolver Log Messages for {self.component_name} ===")
        for level, message in self.log_messages:
            print(f"{level}: {message}")
        print("=== End Log Messages ===\n")

    def _generate_parameter_combinations(self, in_prefix: str, out_prefix: str,
                                        bus_name: str, pkt_prefix: str) -> List[Dict[str, str]]:
        """Generate all parameter combinations with and without underscores."""

        # Create parameter lists - empty string if parameter is empty
        in_prefix_variants = [in_prefix] if in_prefix else ['']
        out_prefix_variants = [out_prefix] if out_prefix else ['']

        # For bus_name and pkt_prefix, create variants with and without trailing underscore
        bus_name_variants = [''] if not bus_name else [bus_name, bus_name + '_']
        pkt_prefix_variants = [''] if not pkt_prefix else [pkt_prefix, pkt_prefix + '_']

        # Generate all combinations
        combinations = []
        for in_p, out_p, bus_n, pkt_p in product(
            in_prefix_variants, out_prefix_variants, bus_name_variants, pkt_prefix_variants
        ):
            combinations.append({
                'in_prefix': in_p,
                'out_prefix': out_p,
                'bus_name': bus_n,
                'pkt_prefix': pkt_p
            })

        if self.super_debug:
            self._log_info(f"Parameter combinations: {combinations}")

        return combinations

    def _resolve_all_signals(self):
        """Resolve all signals using pattern matching."""
        self._log_debug(f"Resolving signals for protocol '{self.protocol_type}', multi_sig={self.multi_sig}")

        # Resolve required signals
        self._resolve_signal_group(self.config['signal_map'], required=True)

        # Resolve optional signals
        self._resolve_optional_signals()

        # Log summary
        total_signals = len(self.resolved_signals)
        found_signals = sum(1 for sig in self.resolved_signals.values() if sig is not None)
        self._log_debug(f"Resolved {found_signals}/{total_signals} signals")

    def _resolve_signal_group(self, signal_group: Dict[str, List[str]], required: bool = True):
        """Resolve a group of signals (either required or optional)."""
        for logical_name, patterns in signal_group.items():
            signal_obj = self._find_signal_match(logical_name, patterns, required)
            self.resolved_signals[logical_name] = signal_obj

    def _resolve_optional_signals(self):
        """Resolve optional signals based on multi_sig mode."""
        optional_map = self.config.get('optional_signal_map', {})
        mode_key = 'multi_sig_true' if self.multi_sig else 'multi_sig_false'

        if mode_key in optional_map:
            patterns = optional_map[mode_key]

            if self.multi_sig:
                # Multi-signal mode: resolve individual field signals
                for field_name in self.field_config.field_names():
                    logical_name = f'field_{field_name}_sig'
                    signal_obj = self._find_signal_match(logical_name, patterns,
                                                        required=False, field_name=field_name)
                    self.resolved_signals[logical_name] = signal_obj
            else:
                # Single signal mode: resolve data signal
                signal_obj = self._find_signal_match('data_sig', patterns, required=False)
                self.resolved_signals['data_sig'] = signal_obj

    def _find_signal_match(self, logical_name: str, patterns: List[str],
                            required: bool = True, field_name: str = None) -> Optional[Any]:
        """Find a signal match using pattern combinations."""
        matches = []
        tried_names = set()

        # Try each pattern with each parameter combination
        for pattern in patterns:
            for param_combo in self.param_combinations:
                # Add field_name to parameters if provided
                format_params = param_combo.copy()
                if field_name:
                    format_params['field_name'] = field_name

                try:
                    signal_name = pattern.format(**format_params)
                    tried_names.add(signal_name)

                    if self.super_debug:
                        self._log_info(f"Trying '{signal_name}' for {logical_name}")

                    # Check if this signal exists in top-level ports
                    if signal_name in self.top_level_ports:
                        matches.append((signal_name, self.top_level_ports[signal_name]))
                        self._log_debug(f"Found match '{signal_name}' for {logical_name}")

                except KeyError as e:
                    # Pattern contains a parameter we don't have
                    if self.super_debug:
                        self._log_warning(f"Pattern '{pattern}' missing parameter: {e}")
                    continue

        # Handle results
        if len(matches) == 0:
            # No matches found
            self.missing_signals.append((logical_name, list(tried_names), required))
            if required:
                return None  # Will be caught in validation
            else:
                self._log_warning(f"Optional signal '{logical_name}' not found. "
                                f"Tried: {', '.join(sorted(tried_names))}")
                return None

        elif len(matches) == 1:
            # Exactly one match - perfect!
            signal_name, signal_obj = matches[0]
            self._log_debug(f"Matched '{signal_name}' for {logical_name}")
            return signal_obj

        else:
            # Multiple matches - conflict!
            match_names = [name for name, _ in matches]
            self.signal_conflicts[logical_name] = match_names
            self._log_error(f"Multiple matches for '{logical_name}': {match_names}")
            return matches[0][1]  # Return first match but will error in validation

    def _display_signal_mapping(self):
        """Display signal mapping results in a Rich table."""
        console = Console()
        table = Table(title=f"Signal Mapping for {self.component_name} ({self.protocol_type})")

        table.add_column("Logical Signal", style="cyan")
        table.add_column("Matched Signal", style="green")
        table.add_column("Status", style="bold")

        # Add required signals
        for logical_name in self.config['signal_map'].keys():
            signal_obj = self.resolved_signals.get(logical_name)
            if signal_obj is not None:
                # Find the actual signal name
                matched_name = self._find_signal_name(signal_obj)
                status = "✓ Found"
                if logical_name in self.signal_conflicts:
                    status = f"⚠ Conflict ({len(self.signal_conflicts[logical_name])} matches)"
            else:
                matched_name = "X"
                status = "✗ Missing (Required)"

            table.add_row(logical_name, matched_name, status)

        # Add optional signals
        optional_signals = [name for name in self.resolved_signals.keys()
                            if name not in self.config['signal_map']]

        for logical_name in sorted(optional_signals):
            signal_obj = self.resolved_signals[logical_name]
            if signal_obj is not None:
                matched_name = self._find_signal_name(signal_obj)
                status = "✓ Found (Optional)"
                if logical_name in self.signal_conflicts:
                    status = f"⚠ Conflict ({len(self.signal_conflicts[logical_name])} matches)"
            else:
                matched_name = "X"
                status = "- Missing (Optional)"

            table.add_row(logical_name, matched_name, status)

        console.print(table)

    def _find_signal_name(self, signal_obj) -> str:
        """Find the signal name that corresponds to a signal object."""
        for name, obj in self.top_level_ports.items():
            if obj is signal_obj:
                return name
        return "Unknown"

    def _validate_required_signals(self):
        """Validate that all required signals were found and no conflicts exist."""
        errors = []

        # Check for missing required signals
        missing_required = [(name, tried, req) for name, tried, req in self.missing_signals if req]
        if missing_required:
            error_details = []
            for logical_name, tried_names, _ in missing_required:
                error_details.append(f"  - {logical_name}: tried {', '.join(sorted(tried_names))}")

            available_ports = ', '.join(sorted(self.top_level_ports.keys()))
            errors.append(
                f"Missing required signals for {self.component_name}:\n" +
                '\n'.join(error_details) +
                f"\nAvailable ports: {available_ports}"
            )

        # Check for signal conflicts
        if self.signal_conflicts:
            conflict_details = []
            for logical_name, matches in self.signal_conflicts.items():
                conflict_details.append(f"  - {logical_name}: matches {', '.join(matches)}")

            errors.append(
                f"Signal conflicts for {self.component_name}:\n" +
                '\n'.join(conflict_details)
            )

        # Raise combined error if any issues
        if errors:
            raise ValueError('\n\n'.join(errors))

    def _prepare_signal_lists(self):
        """Prepare _signals and _optional_signals lists for cocotb Bus initialization."""
        _signals = []
        _optional_signals = []

        # Add required signals that were found
        for logical_name in self.config['signal_map'].keys():
            if self.resolved_signals.get(logical_name) is not None:
                signal_name = self._find_signal_name(self.resolved_signals[logical_name])
                _signals.append(signal_name)

        # Add optional signals that were found
        optional_signals = [name for name in self.resolved_signals.keys()
                            if name not in self.config['signal_map']]

        for logical_name in optional_signals:
            if self.resolved_signals.get(logical_name) is not None:
                signal_name = self._find_signal_name(self.resolved_signals[logical_name])
                _optional_signals.append(signal_name)

        if self.super_debug:
            self._log_info(f"Prepared signal lists - "
                            f"_signals: {_signals}, _optional_signals: {_optional_signals}")

        return _signals, _optional_signals

    def get_signal_lists(self):
        """Get the _signals and _optional_signals lists for cocotb Bus initialization."""
        return self._signals, self._optional_signals

    def _derive_attribute_name(self, logical_name: str) -> str:
        """Derive attribute name from logical signal name."""
        # Handle field signals
        if logical_name.startswith('field_') and logical_name.endswith('_sig'):
            return logical_name  # field_{field_name}_sig stays as-is

        # Handle data signal
        if logical_name == 'data_sig':
            return 'data_sig'

        # Handle control signals
        signal_to_attr = {
            'i_write': 'write_sig',
            'o_wr_full': 'full_sig',
            'i_read': 'read_sig',
            'o_rd_empty': 'empty_sig'
        }

        return signal_to_attr.get(logical_name, logical_name)

    def apply_to_component(self, component):
        """Apply resolved signals to component as attributes."""
        if self.bus is None:
            raise ValueError(f"{self.component_name}: Bus must be set before applying signals")

        # Apply signal mappings
        for logical_name, signal_obj in self.resolved_signals.items():
            attr_name = self._derive_attribute_name(logical_name)

            if signal_obj is not None:
                # Get the signal from the bus using the actual signal name
                signal_name = self._find_signal_name(signal_obj)
                bus_signal = getattr(self.bus, signal_name, None)
                setattr(component, attr_name, bus_signal)
                self._log_debug(f"Set {attr_name} = bus.{signal_name}")
            else:
                setattr(component, attr_name, None)
                self._log_debug(f"Set {attr_name} = None (missing signal)")

    def get_signal(self, logical_name: str):
        """Get a resolved signal by logical name."""
        return self.resolved_signals.get(logical_name)

    def has_signal(self, logical_name: str) -> bool:
        """Check if a signal was found and is not None."""
        return self.resolved_signals.get(logical_name) is not None

    def get_stats(self) -> Dict[str, Any]:
        """Get statistics about signal resolution."""
        total_signals = len(self.resolved_signals)
        resolved_signals = sum(1 for sig in self.resolved_signals.values() if sig is not None)
        missing_required = sum(1 for _, _, required in self.missing_signals if required)
        missing_optional = sum(1 for _, _, required in self.missing_signals if not required)

        stats = {
            'protocol_type': self.protocol_type,
            'multi_sig_mode': self.multi_sig,
            'mode': self.mode,
            'total_ports_found': len(self.top_level_ports),
            'parameter_combinations': len(self.param_combinations),
            'total_signals': total_signals,
            'resolved_signals': resolved_signals,
            'missing_required': missing_required,
            'missing_optional': missing_optional,
            'conflicts': len(self.signal_conflicts),
            'resolution_rate': (resolved_signals / total_signals * 100) if total_signals > 0 else 100
        }

        # Add conflict details
        if self.signal_conflicts:
            stats['conflict_details'] = self.signal_conflicts.copy()

        return stats
