"""
Simplified GAXI/FIFO Signal Mapping - Pattern Matching Against Top-Level Ports

Uses pattern matching against actual DUT ports with parameter combinations
to find the correct signal mappings automatically.

FIXED: Corrected GAXI master/slave signal directions - masters drive valid/read ready,
slaves read valid/drive ready.
"""
from typing import Dict, List, Optional, Any, Union
from itertools import product
from rich.console import Console
from rich.table import Table


# Standard FIFO modes (kept for parameter passing to RTL)
FIFO_VALID_MODES = ['fifo_mux', 'fifo_flop']

# Standard GAXI modes (kept for parameter passing to RTL)
GAXI_VALID_MODES = ['skid', 'fifo_mux', 'fifo_flop']

# GAXI base signal patterns
GAXI_BASE_PATTERNS = {
    # Master-side patterns (for masters and write monitors)
    'valid_base': [
        '{in_prefix}{bus_name}wr_valid',
        '{in_prefix}{bus_name}valid',
        '{in_prefix}{bus_name}m2s_valid',
    ],
    'ready_base': [
        '{out_prefix}{bus_name}wr_ready',
        '{out_prefix}{bus_name}ready',
        '{out_prefix}{bus_name}s2m_ready',
    ],
    'pkt_base': [
        '{in_prefix}{bus_name}wr_data',
        '{in_prefix}{bus_name}data',
        '{in_prefix}{bus_name}m2s_pkt',
    ],
    'field_base': [
        '{in_prefix}{bus_name}{pkt_prefix}{field_name}',
        '{in_prefix}{bus_name}{pkt_prefix}wr_{field_name}',
        '{in_prefix}{bus_name}m2s_pkt_{field_name}',
    ],

    # Slave-side patterns (for slaves and read monitors)
    'slave_valid_base': [
        '{out_prefix}{bus_name}rd_valid',
        '{out_prefix}{bus_name}valid',
        '{out_prefix}{bus_name}m2s_valid',
    ],
    'slave_ready_base': [
        '{in_prefix}{bus_name}rd_ready',
        '{in_prefix}{bus_name}ready',
        '{in_prefix}{bus_name}s2m_ready',
    ],
    'slave_pkt_base': [
        '{out_prefix}{bus_name}rd_data',
        '{out_prefix}{bus_name}data',
        '{out_prefix}{bus_name}m2s_pkt',
    ],
    'slave_field_base': [
        '{out_prefix}{bus_name}{pkt_prefix}{field_name}',
        '{out_prefix}{bus_name}{pkt_prefix}rd_{field_name}',
        '{out_prefix}{bus_name}m2s_pkt_{field_name}',
    ]
}

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
    },

    # GAXI protocol configurations - FIXED SIGNAL DIRECTIONS
    'gaxi_master': {
        'signal_map': {
            'o_valid':    GAXI_BASE_PATTERNS['valid_base'],      # ✅ FIXED: Master DRIVES valid
            'i_ready':    GAXI_BASE_PATTERNS['ready_base']       # ✅ FIXED: Master READS ready
        },
        'optional_signal_map': {
            'multi_sig_false': GAXI_BASE_PATTERNS['pkt_base'],
            'multi_sig_true':  GAXI_BASE_PATTERNS['field_base']
        }
    },

    'gaxi_slave': {
        'signal_map': {
            'i_valid':    GAXI_BASE_PATTERNS['slave_valid_base'], # ✅ FIXED: Slave READS valid
            'o_ready':    GAXI_BASE_PATTERNS['slave_ready_base']  # ✅ FIXED: Slave DRIVES ready
        },
        'optional_signal_map': {
            'multi_sig_false': GAXI_BASE_PATTERNS['slave_pkt_base'],
            'multi_sig_true':  GAXI_BASE_PATTERNS['slave_field_base']
        }
    }

    # Note: No special monitor configurations needed!
    # Write monitors use 'gaxi_master', read monitors use 'gaxi_slave'
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
                prefix='', field_config=None, multi_sig: bool = False,
                in_prefix: str = 'i_', out_prefix: str = 'o_',
                bus_name: str = '', pkt_prefix: str = '', mode: str = None,
                super_debug: bool = False):
        """
        Initialize signal resolver with pattern matching.

        Args:
            protocol_type: Protocol type ('fifo_master', 'fifo_slave', 'gaxi_master', 'gaxi_slave')
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
            mode: Protocol mode (kept for RTL parameter)
            super_debug: Enable detailed signal resolution debugging
        """
        # Get caller information for better error reporting
        caller_info = _get_caller_info()

        if not isinstance(protocol_type, str):
            raise TypeError(
                f"Protocol type must be a string\n"
                f"Called from: {caller_info['filename']}:{caller_info['line_number']} in {caller_info['function']}()\n"
                f"Code: {caller_info['code_line']}"
            )

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
                self._log_debug(f"Available port:{port_name}:")

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

        # Handle FIFO control signals
        if logical_name in ['i_write', 'o_wr_full', 'i_read', 'o_rd_empty']:
            fifo_signal_to_attr = {
                'i_write': 'write_sig',
                'o_wr_full': 'full_sig',
                'i_read': 'read_sig',
                'o_rd_empty': 'empty_sig'
            }
            return fifo_signal_to_attr.get(logical_name, logical_name)

        # Handle GAXI control signals - FIXED MAPPING
        if logical_name in ['i_valid', 'o_ready', 'o_valid', 'i_ready']:
            gaxi_signal_to_attr = {
                'i_valid': 'valid_sig',     # Slave reads valid
                'o_ready': 'ready_sig',     # Slave drives ready
                'o_valid': 'valid_sig',     # Master drives valid ✅ FIXED
                'i_ready': 'ready_sig'      # Master reads ready ✅ FIXED
            }
            return gaxi_signal_to_attr.get(logical_name, logical_name)

        return logical_name

    def apply_to_component(self, component):
        """Apply resolved signals to component as attributes with hard fail validation."""
        if self.bus is None:
            raise ValueError(f"{self.component_name}: Bus must be set before applying signals")

        # DEBUG: Check bus object
        self._log_debug(f"Bus object: {self.bus}")
        self._log_debug(f"Bus type: {type(self.bus)}")

        # DEBUG: List all available signals on the bus
        if hasattr(self.bus, '__dict__'):
            bus_attrs = [attr for attr in dir(self.bus) if not attr.startswith('_')]
            self._log_debug(f"Available bus attributes: {bus_attrs}")

        # Track ALL failed signal linkages for comprehensive error reporting
        failed_signals = []
        successful_linkages = []

        # Apply signal mappings and track failures
        for logical_name, signal_obj in self.resolved_signals.items():
            attr_name = self._derive_attribute_name(logical_name)

            # Determine signal type for reporting
            is_required = logical_name in self.config['signal_map']
            signal_type = "REQUIRED" if is_required else "DATA/OPTIONAL"

            if signal_obj is not None:
                # Get the signal from the bus using the actual signal name
                signal_name = self._find_signal_name(signal_obj)
                self._log_debug(f"{self.component_name} Signal Resolver: {signal_name}")

                # Try to get the signal from the bus
                bus_signal = getattr(self.bus, signal_name, None)

                # DEBUG: Check the bus_signal result
                self._log_debug(f"bus_signal for '{signal_name}': {bus_signal}")
                self._log_debug(f"bus_signal type: {type(bus_signal)}")

                if bus_signal is None:
                    # Track the failure with detailed information
                    failure_info = {
                        'logical_name': logical_name,
                        'signal_name': signal_name,
                        'attr_name': attr_name,
                        'signal_type': signal_type,
                        'has_attr': hasattr(self.bus, signal_name),
                        'bus_attr_type': type(getattr(self.bus, signal_name, 'NOT_FOUND'))
                    }

                    failed_signals.append(failure_info)
                    self._log_error(f"❌ CRITICAL: {signal_type} signal '{logical_name}' -> '{signal_name}' cannot be linked to Bus!")
                else:
                    # Success!
                    successful_linkages.append({
                        'logical_name': logical_name,
                        'signal_name': signal_name,
                        'attr_name': attr_name,
                        'signal_type': signal_type
                    })
                    self._log_debug(f"✅ Linked {attr_name} = bus.{signal_name}")

                # Set the attribute regardless (None if failed)
                setattr(component, attr_name, bus_signal)
            else:
                # Signal was not resolved in the first place
                setattr(component, attr_name, None)
                self._log_debug(f"Set {attr_name} = None (signal not resolved)")

        # HARD FAIL: Generate comprehensive error report if ANY signals failed
        if failed_signals:
            error_lines = [
                f"\n🚨 CRITICAL SIGNAL LINKAGE FAILURE for {self.component_name} 🚨",
                f"SignalResolver found signals, but Bus linkage failed!",
                f""
            ]

            # Separate required vs data/optional failures for clarity
            required_failures = [f for f in failed_signals if f['signal_type'] == 'REQUIRED']
            data_failures = [f for f in failed_signals if f['signal_type'] == 'DATA/OPTIONAL']

            if required_failures:
                error_lines.append("❌ FAILED CONTROL SIGNALS:")
                for failure in required_failures:
                    error_lines.append(f"  • {failure['logical_name']} -> '{failure['signal_name']}'")
                    error_lines.append(f"    - Target attribute: component.{failure['attr_name']}")
                    error_lines.append(f"    - Bus has attribute: {failure['has_attr']}")
                    error_lines.append(f"    - Bus attribute type: {failure['bus_attr_type']}")

            if data_failures:
                error_lines.append(f"\n❌ FAILED DATA SIGNALS:")
                for failure in data_failures:
                    error_lines.append(f"  • {failure['logical_name']} -> '{failure['signal_name']}'")
                    error_lines.append(f"    - Target attribute: component.{failure['attr_name']}")
                    error_lines.append(f"    - Bus has attribute: {failure['has_attr']}")
                    error_lines.append(f"    - Bus attribute type: {failure['bus_attr_type']}")

            # Successful linkages (if any)
            if successful_linkages:
                error_lines.append(f"\n✅ SUCCESSFUL LINKAGES:")
                for success in successful_linkages:
                    error_lines.append(f"  • {success['logical_name']} -> '{success['signal_name']}' ({success['signal_type']})")

            # Bus diagnostic information
            bus_attrs = [attr for attr in dir(self.bus) if not attr.startswith('_')]
            bus_signals = [attr for attr in bus_attrs if hasattr(getattr(self.bus, attr, None), 'value')]

            error_lines.extend([
                f"\n🔍 BUS DIAGNOSTIC INFORMATION:",
                f"  Bus type: {type(self.bus)}",
                f"  Bus attributes: {bus_attrs}",
                f"  Bus signals (have .value): {bus_signals}",
                f""
            ])

            # Show what SignalResolver found vs what Bus has
            resolved_signal_names = [self._find_signal_name(sig) for sig in self.resolved_signals.values() if sig is not None]
            error_lines.extend([
                f"🔍 SIGNAL RESOLUTION vs BUS MISMATCH:",
                f"  SignalResolver found: {resolved_signal_names}",
                f"  Bus actually has: {bus_signals}",
                f"  Missing from Bus: {set(resolved_signal_names) - set(bus_signals)}",
                f""
            ])

            # Likely causes and solutions
            error_lines.extend([
                f"💡 LIKELY CAUSES:",
                f"  1. Double prefixing: Both 'prefix' and 'bus_name' are set",
                f"     - Current prefix: '{getattr(self, 'prefix', 'NOT_SET')}'",
                f"     - Current bus_name: '{getattr(self, 'bus_name', 'NOT_SET')}'",
                f"  2. _prepare_signal_lists() not stripping prefixes correctly",
                f"  3. Bus constructor received wrong signal lists",
                f"  4. SignalResolver vs Bus naming convention mismatch",
                f""
            ])

            # Show the actual signal lists passed to Bus
            error_lines.extend([
                f"🔍 SIGNAL LISTS PASSED TO BUS:",
                f"  _signals: {getattr(self, '_signals', 'NOT_SET')}",
                f"  _optional_signals: {getattr(self, '_optional_signals', 'NOT_SET')}",
                f""
            ])

            # Quick fixes
            error_lines.extend([
                f"🔧 IMMEDIATE FIXES:",
                f"  1. If using bus_name='{getattr(self, 'bus_name', '')}', set prefix=''",
                f"  2. If using prefix, set bus_name=''",
                f"  3. Check _prepare_signal_lists() calls _clean_signal_name_for_bus()",
                f"  4. Verify Bus constructor gets cleaned signal names",
                f""
            ])

            # Component impact - emphasize that ALL signals are critical
            error_lines.extend([
                f"⚠️  COMPONENT IMPACT:",
                f"  - {self.component_name} CANNOT FUNCTION without these signals!",
                f"  - Control signals: needed for valid/ready handshaking",
                f"  - Data signals: needed for actual data transfer",
                f"  - Component will fail at runtime when accessing these signals",
                f"  - NO SIGNALS ARE TRULY 'OPTIONAL' - all found signals must link!",
                f""
            ])

            # Debugging steps
            error_lines.extend([
                f"🐛 DEBUGGING STEPS:",
                f"  1. Check signal_mapping_helper._prepare_signal_lists()",
                f"  2. Verify _clean_signal_name_for_bus() is being called",
                f"  3. Compare resolved signals vs Bus constructor inputs",
                f"  4. Enable super_debug=True for detailed signal resolution",
                f"  5. Check cocotb Bus constructor logic for double prefixing",
                f""
            ])

            # Raise the comprehensive error - NO MERCY!
            raise RuntimeError('\n'.join(error_lines))

        # SUCCESS: Log successful initialization
        success_count = len(successful_linkages)
        total_resolved = len([s for s in self.resolved_signals.values() if s is not None])
        required_count = len([name for name in self.config['signal_map'].keys()
                            if self.resolved_signals.get(name) is not None])
        data_count = success_count - required_count

        self._log_info(f"✅ Signal linkage SUCCESS: {success_count}/{total_resolved} signals linked")
        self._log_info(f"✅ Control signals: {required_count}, Data signals: {data_count}")
        self._log_info(f"✅ {self.component_name} ready for operation!")

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


# Helper function to get caller info (referenced but not defined in the original)
def _get_caller_info():
    """Get information about where SignalResolver was called from."""
    import inspect
    try:
        # Walk up the stack to find the first frame outside this file
        for frame_info in inspect.stack():
            filename = frame_info.filename
            function_name = frame_info.function
            line_number = frame_info.lineno

            # Skip frames within this file (signal_mapping_helper.py)
            if 'signal_mapping_helper' not in filename:
                # Get some context around the line if possible
                try:
                    with open(filename, 'r') as f:
                        lines = f.readlines()
                        if 0 <= line_number - 1 < len(lines):
                            code_line = lines[line_number - 1].strip()
                        else:
                            code_line = "<line not available>"
                except:
                    code_line = "<unable to read file>"

                return {
                    'filename': filename,
                    'function': function_name,
                    'line_number': line_number,
                    'code_line': code_line
                }
    except:
        pass

    return {
        'filename': '<unknown>',
        'function': '<unknown>',
        'line_number': 0,
        'code_line': '<unknown>'
    }
