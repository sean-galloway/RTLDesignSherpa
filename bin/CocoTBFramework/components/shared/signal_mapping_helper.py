"""
Simplified GAXI/FIFO Signal Mapping - Pattern Matching Against Top-Level Ports

Uses pattern matching against actual DUT ports with parameter combinations
to find the correct signal mappings automatically.

UPDATED: Now properly handles 'prefix' parameter for both signal discovery and cocotb compatibility.
ADDED: Optional signal_map parameter for manual signal mapping override.
ADDED: Full FIFO protocol support for signal_map functionality.
FIXED: Missing comma in FIFO patterns and enhanced validation for critical data signals.
"""
from typing import Dict, List, Optional, Any, Union
from itertools import product
from rich.console import Console
from rich.table import Table


# Standard FIFO modes (kept for parameter passing to RTL)
FIFO_VALID_MODES = ['fifo_mux', 'fifo_flop']

# Standard GAXI modes (kept for parameter passing to RTL)
GAXI_VALID_MODES = ['skid', 'fifo_mux', 'fifo_flop']

# AXIS base signal patterns - NEW for AXIS protocol support
AXIS_BASE_PATTERNS = {
    # Master-side patterns (for AXIS masters)
    'valid_base': [
        '{prefix}{bus_name}tvalid',
        '{prefix}{bus_name}axis_tvalid',
        '{prefix}{bus_name}{pkt_prefix}tvalid',
    ],
    'ready_base': [
        '{prefix}{bus_name}tready',
        '{prefix}{bus_name}axis_tready',
        '{prefix}{bus_name}{pkt_prefix}tready',
    ],
    'data_base': [
        '{prefix}{bus_name}tdata',
        '{prefix}{bus_name}axis_tdata',
        '{prefix}{bus_name}{pkt_prefix}tdata',
    ],
    'strb_base': [
        '{prefix}{bus_name}tstrb',
        '{prefix}{bus_name}axis_tstrb',
        '{prefix}{bus_name}{pkt_prefix}tstrb',
    ],
    'last_base': [
        '{prefix}{bus_name}tlast',
        '{prefix}{bus_name}axis_tlast',
        '{prefix}{bus_name}{pkt_prefix}tlast',
    ],
    'id_base': [
        '{prefix}{bus_name}tid',
        '{prefix}{bus_name}axis_tid',
        '{prefix}{bus_name}{pkt_prefix}tid',
    ],
    'dest_base': [
        '{prefix}{bus_name}tdest',
        '{prefix}{bus_name}axis_tdest',
        '{prefix}{bus_name}{pkt_prefix}tdest',
    ],
    'user_base': [
        '{prefix}{bus_name}tuser',
        '{prefix}{bus_name}axis_tuser',
        '{prefix}{bus_name}{pkt_prefix}tuser',
    ],

    # Slave-side patterns (for AXIS slaves) - same patterns but different logical mapping
    'slave_valid_base': [
        '{prefix}{bus_name}tvalid',
        '{prefix}{bus_name}axis_tvalid',
        '{prefix}{bus_name}{pkt_prefix}tvalid',
    ],
    'slave_ready_base': [
        '{prefix}{bus_name}tready',
        '{prefix}{bus_name}axis_tready',
        '{prefix}{bus_name}{pkt_prefix}tready',
    ],
    'slave_data_base': [
        '{prefix}{bus_name}tdata',
        '{prefix}{bus_name}axis_tdata',
        '{prefix}{bus_name}{pkt_prefix}tdata',
    ],
}

# GAXI base signal patterns - UPDATED to include prefix
GAXI_BASE_PATTERNS = {
    # Master-side patterns (for masters and write monitors)
    'valid_base': [
        '{prefix}{bus_name}valid',
        '{prefix}{bus_name}wr_valid',
        '{prefix}{bus_name}m2s_valid',
        '{prefix}{bus_name}{pkt_prefix}valid',
        '{prefix}{bus_name}{pkt_prefix}wr_valid',
        '{prefix}{bus_name}{pkt_prefix}m2s_valid',
    ],
    'ready_base': [
        '{prefix}{bus_name}ready',
        '{prefix}{bus_name}wr_ready',
        '{prefix}{bus_name}s2m_ready',
        '{prefix}{bus_name}{pkt_prefix}ready',
        '{prefix}{bus_name}{pkt_prefix}wr_ready',
        '{prefix}{bus_name}{pkt_prefix}s2m_ready',
    ],
    'pkt_base': [
        '{prefix}{bus_name}data',
        '{prefix}{bus_name}pkt',
        '{prefix}{bus_name}packet',
        '{prefix}{bus_name}m2s_pkt',
        '{prefix}{bus_name}{pkt_prefix}_pkt',
        '{prefix}{bus_name}wr_data',
    ],
    'field_base': [
        '{prefix}{bus_name}{pkt_prefix}{field_name}',
        '{prefix}{bus_name}{pkt_prefix}wr_{field_name}',
        '{prefix}{bus_name}m2s_pkt_{field_name}',
    ],

    # Slave-side patterns (for slaves and read monitors)
    'slave_valid_base': [
        '{prefix}{bus_name}valid',
        '{prefix}{bus_name}rd_valid',
        '{prefix}{bus_name}m2s_valid',
        '{prefix}{bus_name}{pkt_prefix}valid',
        '{prefix}{bus_name}{pkt_prefix}rd_valid',
        '{prefix}{bus_name}{pkt_prefix}m2s_valid',
    ],
    'slave_ready_base': [
        '{prefix}{bus_name}ready',
        '{prefix}{bus_name}rd_ready',
        '{prefix}{bus_name}s2m_ready',
        '{prefix}{bus_name}{pkt_prefix}ready',
        '{prefix}{bus_name}{pkt_prefix}rd_ready',
        '{prefix}{bus_name}{pkt_prefix}s2m_ready',
    ],
    'slave_pkt_base': [
        '{prefix}{bus_name}data',
        '{prefix}{bus_name}rd_data',
        '{prefix}{bus_name}pkt',
        '{prefix}{bus_name}packet',
        '{prefix}{bus_name}m2s_pkt',
        '{prefix}{bus_name}{pkt_prefix}_pkt',
    ],
    'slave_field_base': [
        '{prefix}{bus_name}{pkt_prefix}{field_name}',
        '{prefix}{bus_name}{pkt_prefix}rd_{field_name}',
        '{prefix}{bus_name}m2s_pkt_{field_name}',
    ]
}

# FIFO base signal patterns - UPDATED to include prefix and FIXED missing comma
FIFO_BASE_PATTERNS = {
    # Write-side patterns (for masters and write monitors)
    'write_base': [
        '{prefix}{bus_name}write',
    ],
    'wr_data_base': [
        '{prefix}{bus_name}wr_data',
        '{prefix}{bus_name}data',
        '{prefix}{bus_name}packet',
    ],
    'wr_field_base': [
        '{prefix}{bus_name}{pkt_prefix}{field_name}',
        '{prefix}{bus_name}{pkt_prefix}wr_{field_name}',
    ],
    'full_base': [
        '{prefix}{bus_name}wr_full',
        '{prefix}{bus_name}full'
    ],

    # Read-side patterns (for slaves and read monitors)
    'read_base': [
        '{prefix}{bus_name}read'
    ],
    'rd_data_base': [
        '{prefix}{bus_name}rd_data',
        '{prefix}{bus_name}data',      # FIXED: Added missing comma
        '{prefix}{bus_name}packet'
    ],
    'rd_field_base': [
        '{prefix}{bus_name}{pkt_prefix}{field_name}',
        '{prefix}{bus_name}{pkt_prefix}rd_{field_name}'
    ],
    'empty_base': [
        '{prefix}{bus_name}rd_empty',
        '{prefix}{bus_name}empty'
    ]
}

PROTOCOL_SIGNAL_CONFIGS = {
    'axis_master': {
        'signal_map': {
            'o_valid':    AXIS_BASE_PATTERNS['valid_base'],   # Master drives tvalid
            'i_ready':    AXIS_BASE_PATTERNS['ready_base']    # Master reads tready
        },
        'optional_signal_map': {
            'multi_sig_false': AXIS_BASE_PATTERNS['data_base'],   # Single tdata signal
            'multi_sig_true':  [  # For field-based patterns
                '{prefix}{bus_name}{pkt_prefix}t{field_name}',
                '{prefix}{bus_name}axis_t{field_name}',
                '{prefix}{bus_name}t{field_name}',
            ]
        }
    },

    'axis_slave': {
        'signal_map': {
            'i_valid':    AXIS_BASE_PATTERNS['slave_valid_base'],  # Slave reads tvalid
            'o_ready':    AXIS_BASE_PATTERNS['slave_ready_base']   # Slave drives tready
        },
        'optional_signal_map': {
            'multi_sig_false': AXIS_BASE_PATTERNS['slave_data_base'],  # Single tdata signal
            'multi_sig_true':  [  # For field-based patterns
                '{prefix}{bus_name}{pkt_prefix}t{field_name}',
                '{prefix}{bus_name}axis_t{field_name}',
                '{prefix}{bus_name}t{field_name}',
            ]
        }
    },

    'fifo_master': {
        'signal_map': {
            'i_write':   FIFO_BASE_PATTERNS['write_base'],
            'o_wr_full': FIFO_BASE_PATTERNS['full_base']
        },
        'optional_signal_map': {
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
            'multi_sig_false': FIFO_BASE_PATTERNS['rd_data_base'],
            'multi_sig_true':  FIFO_BASE_PATTERNS['rd_field_base']
        }
    },

    'gaxi_master': {
        'signal_map': {
            'o_valid':    GAXI_BASE_PATTERNS['valid_base'],
            'i_ready':    GAXI_BASE_PATTERNS['ready_base']
        },
        'optional_signal_map': {
            'multi_sig_false': GAXI_BASE_PATTERNS['pkt_base'],
            'multi_sig_true':  GAXI_BASE_PATTERNS['field_base']
        }
    },

    'gaxi_slave': {
        'signal_map': {
            'i_valid':    GAXI_BASE_PATTERNS['slave_valid_base'],
            'o_ready':    GAXI_BASE_PATTERNS['slave_ready_base']
        },
        'optional_signal_map': {
            'multi_sig_false': GAXI_BASE_PATTERNS['slave_pkt_base'],
            'multi_sig_true':  GAXI_BASE_PATTERNS['slave_field_base']
        }
    }
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

    UPDATED: Now properly handles 'prefix' parameter for both signal discovery and cocotb compatibility.
    ADDED: Optional signal_map parameter for manual signal mapping override.
    ADDED: Full FIFO protocol support for signal_map functionality.
    FIXED: Enhanced validation for critical data signals with hard failure.
    """

    def __init__(self, protocol_type: str, dut, bus, log, component_name: str,
                prefix='', field_config=None, multi_sig: bool = False,
                bus_name: str = '', pkt_prefix: str = '', mode: str = None,
                super_debug: bool = False, signal_map: Optional[Dict[str, str]] = None):
        """
        Initialize signal resolver with pattern matching and prefix support.

        Args:
            protocol_type: Protocol type ('fifo_master', 'fifo_slave', 'gaxi_master', 'gaxi_slave')
            dut: Device under test
            bus: Bus object from BusDriver/BusMonitor (can be None initially)
            log: Logger instance (can be None)
            component_name: Component name for error messages
            prefix: Prefix that cocotb will prepend to signal names
            field_config: Field configuration (required for multi_sig=True)
            multi_sig: Whether using multi-signal mode
            bus_name: Bus/channel name
            pkt_prefix: Packet field prefix
            mode: Protocol mode (kept for RTL parameter)
            super_debug: Enable detailed signal resolution debugging
            signal_map: Optional manual signal mapping.
                Keys for GAXI: 'valid', 'ready', 'data' (or field names for multi_sig=True).
                Keys for FIFO Master: 'write', 'full', 'data' (or field names for multi_sig=True).
                Keys for FIFO Slave: 'read', 'empty', 'data' (or field names for multi_sig=True).
                Values: DUT signal name strings. If provided, bypasses automatic discovery.
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
        self.bus_name = bus_name
        self.pkt_prefix = pkt_prefix
        self.log = log
        self.component_name = component_name
        self.prefix = prefix  # ADDED: Store prefix for proper handling
        self.field_config = field_config
        self.multi_sig = multi_sig
        self.mode = mode
        self.super_debug = super_debug
        self.signal_map = signal_map  # NEW: Store manual signal mapping

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

        # Storage for resolved signals
        self.resolved_signals = {}

    def get_signal_lists(self):
        """Get signals for cocotb Bus initialization.

        Returns:
            Tuple of (required_signals, optional_signals) lists for cocotb Bus
        """
        self.signal_conflicts = {}  # Track multiple matches
        self.missing_signals = []

        # Choose resolution method based on signal_map
        if self.signal_map is not None:
            self._log_info(f"Using manual signal mapping with {len(self.signal_map)} signals")
            self._resolve_signals_from_map()
        else:
            # Generate parameter combinations (now includes prefix) - only for automatic discovery
            self.param_combinations = self._generate_parameter_combinations(
                self.prefix, self.bus_name, self.pkt_prefix
            )
            self._log_debug(f"Generated {len(self.param_combinations)} parameter combinations")

            # Resolve all signals using automatic discovery
            self._resolve_all_signals()

        # Display results and validate
        self._display_signal_mapping()
        self._validate_required_signals()

        # Prepare signal lists for cocotb Bus initialization (strips prefix)
        self._signals, self._optional_signals = self._prepare_signal_lists()

        # Return the signal lists
        return self._signals, self._optional_signals

    def _resolve_signals_from_map(self):
        """
        Resolve signals using the provided signal_map.

        Maps simplified keys ('valid', 'ready', 'data', field names) to internal logical names.
        """
        self._log_debug(f"Manual signal mapping: {self.signal_map}")

        # Validate signal_map contains required signals
        self._validate_signal_map()

        # Map simplified keys to internal logical names
        logical_mapping = self._create_logical_mapping()

        # Resolve each signal from the map
        for simple_key, dut_signal_name in self.signal_map.items():
            logical_name = logical_mapping.get(simple_key)
            if logical_name is None:
                raise ValueError(f"Unknown signal key '{simple_key}' in signal_map for {self.component_name}. "
                            f"Valid keys: {list(logical_mapping.keys())}")

            # Check if signal exists on DUT
            if dut_signal_name not in self.top_level_ports:
                raise ValueError(f"Signal '{dut_signal_name}' (for '{simple_key}') not found on DUT. "
                            f"Available ports: {list(self.top_level_ports.keys())}")

            # Store the resolved signal
            signal_obj = self.top_level_ports[dut_signal_name]
            self.resolved_signals[logical_name] = signal_obj
            self._log_debug(f"Mapped '{simple_key}' -> '{logical_name}' = '{dut_signal_name}'")

    def _validate_signal_map(self):
        """Validate that signal_map contains all required signals."""
        if self.protocol_type.startswith('axis') or self.protocol_type.startswith('gaxi'):
            required_keys = {'valid', 'ready'}

            if self.multi_sig:
                # Multi-sig mode: need field names
                if not self.field_config:
                    raise ValueError(f"field_config required for multi_sig=True with signal_map")
                required_keys.update(self.field_config.field_names())
            else:
                # Single-sig mode: need data signal
                required_keys.add('data')

        elif self.protocol_type.startswith('fifo'):
            # FIFO protocols support
            if self.protocol_type == 'fifo_master':
                required_keys = {'write', 'full'}
            elif self.protocol_type == 'fifo_slave':
                required_keys = {'read', 'empty'}
            else:
                raise ValueError(f"Unknown FIFO protocol type: {self.protocol_type}")

            if self.multi_sig:
                # Multi-sig mode: need field names
                if not self.field_config:
                    raise ValueError(f"field_config required for multi_sig=True with signal_map")
                required_keys.update(self.field_config.field_names())
            else:
                # Single-sig mode: need data signal
                required_keys.add('data')

        else:
            raise ValueError(f"Unknown protocol type: {self.protocol_type}")

        # Check all required keys are present
        missing_keys = required_keys - set(self.signal_map.keys())
        if missing_keys:
            raise ValueError(f"signal_map missing required keys: {missing_keys}. "
                        f"Required: {required_keys}, Provided: {list(self.signal_map.keys())}")

        # Check for unexpected keys
        unexpected_keys = set(self.signal_map.keys()) - required_keys
        if unexpected_keys:
            raise ValueError(f"signal_map contains unexpected keys: {unexpected_keys}. "
                        f"Valid keys: {required_keys}")

    def _create_logical_mapping(self):
        """Create mapping from simplified keys to internal logical names."""
        logical_mapping = {}

        if self.protocol_type == 'axis_master':
            logical_mapping['valid'] = 'o_valid'  # Master drives tvalid
            logical_mapping['ready'] = 'i_ready'  # Master reads tready
        elif self.protocol_type == 'axis_slave':
            logical_mapping['valid'] = 'i_valid'  # Slave reads tvalid
            logical_mapping['ready'] = 'o_ready'  # Slave drives tready
        elif self.protocol_type == 'gaxi_master':
            logical_mapping['valid'] = 'o_valid'  # Master drives valid
            logical_mapping['ready'] = 'i_ready'  # Master reads ready
        elif self.protocol_type == 'gaxi_slave':
            logical_mapping['valid'] = 'i_valid'  # Slave reads valid
            logical_mapping['ready'] = 'o_ready'  # Slave drives ready
        elif self.protocol_type == 'fifo_master':
            logical_mapping['write'] = 'i_write'  # Master drives write
            logical_mapping['full'] = 'o_wr_full'  # Master reads full
        elif self.protocol_type == 'fifo_slave':
            logical_mapping['read'] = 'i_read'    # Slave drives read
            logical_mapping['empty'] = 'o_rd_empty'  # Slave reads empty

        # Handle data signals based on multi_sig mode
        if self.multi_sig and self.field_config:
            # Multi-signal mode: map field names to field signal names
            for field_name in self.field_config.field_names():
                logical_mapping[field_name] = f'field_{field_name}_sig'
        else:
            # Single-signal mode: map 'data' to appropriate data signal
            if self.protocol_type in ['axis_master', 'axis_slave']:
                logical_mapping['data'] = 'data_sig'
            elif self.protocol_type in ['gaxi_master', 'gaxi_slave']:
                logical_mapping['data'] = 'data_sig'
            elif self.protocol_type == 'fifo_master':
                logical_mapping['data'] = 'data_sig'
            elif self.protocol_type == 'fifo_slave':
                logical_mapping['data'] = 'data_sig'

        return logical_mapping

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

    def _generate_parameter_combinations(self, prefix: str,
                                        bus_name: str, pkt_prefix: str) -> List[Dict[str, str]]:
        """Generate all parameter combinations including prefix variants."""

        # Create prefix variants with automatic underscore handling
        if prefix:
            # If prefix doesn't end with underscore, create both variants
            if prefix.endswith('_'):
                prefix_variants = [prefix]
            else:
                prefix_variants = [prefix, prefix + '_']
        else:
            prefix_variants = ['']

        # For bus_name and pkt_prefix, create variants with and without trailing underscore
        bus_name_variants = [''] if not bus_name else [bus_name, bus_name + '_']
        pkt_prefix_variants = [''] if not pkt_prefix else [pkt_prefix, pkt_prefix + '_']

        # Generate all combinations (now includes prefix)
        combinations = []
        for prefix_p, bus_n, pkt_p in product(
            prefix_variants, bus_name_variants, pkt_prefix_variants
        ):
            combinations.append({
                'prefix': prefix_p,      # ADDED: Include prefix in combinations
                'bus_name': bus_n,
                'pkt_prefix': pkt_p
            })

        if self.super_debug:
            self._log_info(f"Parameter combinations: {combinations}")

        return combinations

    def _resolve_all_signals(self):
        """Resolve all signals using pattern matching."""
        self._log_debug(f"Resolving signals for {self.component_name=}: protocol '{self.protocol_type}', multi_sig={self.multi_sig}")
        self._log_debug(f"bus='{self.bus}' prefix='{self.prefix}' pkt_prefix='{self.pkt_prefix}' ")
        self._log_debug(f"signal_map={self.signal_map}")

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
                if self.protocol_type in ['axis_master', 'axis_slave']:
                    signal_obj = self._find_signal_match('data_sig', patterns, required=False)
                    self.resolved_signals['data_sig'] = signal_obj
                elif self.protocol_type in ['gaxi_master', 'gaxi_slave']:
                    signal_obj = self._find_signal_match('data_sig', patterns, required=False)
                    self.resolved_signals['data_sig'] = signal_obj
                elif self.protocol_type == 'fifo_master':
                    signal_obj = self._find_signal_match('data_sig', patterns, required=False)
                    self.resolved_signals['data_sig'] = signal_obj
                elif self.protocol_type == 'fifo_slave':
                    signal_obj = self._find_signal_match('data_sig', patterns, required=False)
                    self.resolved_signals['data_sig'] = signal_obj

    def _find_signal_match(self, logical_name: str, patterns: List[str],
                            required: bool = True, field_name: str = None) -> Optional[Any]:
        """
        Find a signal match using pattern combinations.

        FIXED: Handles duplicate matches that resolve to the same signal object.
        This prevents false conflicts when multiple patterns find the same signal.
        """
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
            # Multiple matches - SURGICAL FIX: check if they're the same signal object
            unique_signals = set(signal_obj for _, signal_obj in matches)

            if len(unique_signals) == 1:
                # All matches point to same signal object - not a real conflict!
                signal_obj = next(iter(unique_signals))
                match_names = [name for name, _ in matches]
                self._log_debug(f"Multiple patterns matched same signal for '{logical_name}': {match_names}")
                return signal_obj
            else:
                # True conflict - different signal objects
                match_names = [name for name, _ in matches]
                self.signal_conflicts[logical_name] = match_names
                self._log_error(f"Multiple matches for '{logical_name}': {match_names}")
                return matches[0][1]  # Return first match but will error in validation

    def _strip_prefix_from_signal_name(self, signal_name: str) -> str:
        """
        Strip the prefix from a signal name for cocotb Bus compatibility.

        Args:
            signal_name: Full signal name including prefix

        Returns:
            Signal name with prefix removed
        """
        if self.prefix and signal_name.startswith(self.prefix):
            stripped = signal_name[len(self.prefix):]
            if self.super_debug:
                self._log_debug(f"Stripped prefix '{self.prefix}' from '{signal_name}' -> '{stripped}'")
            return stripped
        return signal_name

    def _display_signal_mapping(self):
        """Display signal mapping results in a Rich table."""
        console = Console()
        mapping_source = "Manual signal_map" if self.signal_map else "Automatic discovery"
        table = Table(title=f"Signal Mapping for {self.component_name} ({self.protocol_type}) - {mapping_source}")

        table.add_column("Logical Signal", style="cyan")
        table.add_column("Matched Signal", style="green")
        table.add_column("Cocotb Signal", style="yellow")  # ADDED: Show cocotb signal name
        table.add_column("Status", style="bold")

        # Add required signals
        for logical_name in self.config['signal_map'].keys():
            signal_obj = self.resolved_signals.get(logical_name)
            if signal_obj is not None:
                # Find the actual signal name
                matched_name = self._find_signal_name(signal_obj)
                cocotb_name = self._strip_prefix_from_signal_name(matched_name)  # ADDED
                status = "✓ Found"
                if logical_name in self.signal_conflicts:
                    status = f"⚠ Conflict ({len(self.signal_conflicts[logical_name])} matches)"
            else:
                matched_name = "X"
                cocotb_name = "X"  # ADDED
                status = "✗ Missing (Required)"

            table.add_row(logical_name, matched_name, cocotb_name, status)

        # Add optional signals
        optional_signals = [name for name in self.resolved_signals.keys()
                            if name not in self.config['signal_map']]

        for logical_name in sorted(optional_signals):
            signal_obj = self.resolved_signals[logical_name]
            if signal_obj is not None:
                matched_name = self._find_signal_name(signal_obj)
                cocotb_name = self._strip_prefix_from_signal_name(matched_name)  # ADDED
                status = "✓ Found (Optional)"
                if logical_name in self.signal_conflicts:
                    status = f"⚠ Conflict ({len(self.signal_conflicts[logical_name])} matches)"
            else:
                matched_name = "X"
                cocotb_name = "X"  # ADDED
                status = "- Missing (Optional)"

            table.add_row(logical_name, matched_name, cocotb_name, status)

        console.print(table)

    def _find_signal_name(self, signal_obj) -> str:
        """Find the signal name that corresponds to a signal object."""
        for name, obj in self.top_level_ports.items():
            if obj is signal_obj:
                return name
        return "Unknown"

    def _validate_required_signals(self):
        """
        Validate that all required signals were found and no conflicts exist.

        ENHANCED: Adds critical validation for data signals in single-signal mode.
        """
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

        # ENHANCED: Critical validation for data signals in single-signal mode
        if not self.multi_sig:
            data_signal_found = any(
                name.endswith('_sig') and 'data' in name
                for name, signal in self.resolved_signals.items()
                if signal is not None
            )

            if not data_signal_found:
                # Find available data-like signals for troubleshooting
                available_data_signals = [
                    name for name in self.top_level_ports.keys()
                    if 'data' in name.lower()
                ]

                # This should be a CRITICAL ERROR for single-signal mode
                critical_error = [
                    f"🚨 CRITICAL: No data signal found for {self.component_name} in single-signal mode!",
                    f"",
                    f"Component: {self.component_name}",
                    f"Protocol: {self.protocol_type}",
                    f"Mode: single-signal (multi_sig=False)",
                    f"Bus name: '{self.bus_name}' (empty means no bus prefix)",
                    f"",
                    f"This component REQUIRES a data signal for proper operation.",
                    f"Without it, the component cannot send/receive packet data.",
                    f"",
                    f"💡 TROUBLESHOOTING:",
                    f"1. Check signal naming - expected patterns:",
                    f"   - {self.bus_name}data (current bus_name + 'data')",
                    f"   - {self.bus_name}rd_data (for read-side)",
                    f"   - {self.bus_name}packet",
                ]

                if available_data_signals:
                    critical_error.extend([
                        f"",
                        f"2. Available data-like signals found on DUT:",
                        f"   {', '.join(available_data_signals)}",
                        f"",
                        f"3. Use manual signal_map to specify correct signal:",
                        f"   signal_map={{'data': '{available_data_signals[0] if available_data_signals else 'your_data_signal'}'}}",
                    ])
                else:
                    critical_error.extend([
                        f"",
                        f"2. No data-like signals found on DUT!",
                        f"   Available signals: {', '.join(sorted(self.top_level_ports.keys())[:10])}{'...' if len(self.top_level_ports) > 10 else ''}",
                        f"",
                        f"3. Verify your DUT has the expected data output signal",
                    ])

                critical_error.extend([
                    f"",
                    f"4. Check bus_name parameter - currently: '{self.bus_name}'",
                    f"   If your signals have a different prefix, update bus_name",
                    f"",
                    f"This error prevents component initialization to avoid runtime failures.",
                ])

                errors.append('\n'.join(critical_error))

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
        """
        Prepare _signals and _optional_signals lists for cocotb Bus initialization.
        """
        _signals = []
        _optional_signals = []

        # Add required signals that were found
        for logical_name in self.config['signal_map'].keys():
            if self.resolved_signals.get(logical_name) is not None:
                signal_name = self._find_signal_name(self.resolved_signals[logical_name])
                _signals.append(signal_name)  # Use full signal name

        # FIX: Define optional_signals before using it
        optional_signals = [name for name in self.resolved_signals.keys()
                            if name not in self.config['signal_map']]

        # Add optional signals that were found
        for logical_name in optional_signals:  # ← Now this works
            if self.resolved_signals.get(logical_name) is not None:
                signal_name = self._find_signal_name(self.resolved_signals[logical_name])
                _optional_signals.append(signal_name)  # Use full signal name

        if self.super_debug:
            self._log_info(f"Prepared signal lists - "
                            f"_signals: {_signals}, _optional_signals: {_optional_signals}")
            self._log_info(f"Using full signal names with prefix='' to cocotb")

        return _signals, _optional_signals


    def _derive_attribute_name(self, logical_name: str) -> str:
        """Derive attribute name from logical signal name."""
        # Handle field signals
        if logical_name.startswith('field_') and logical_name.endswith('_sig'):
            return logical_name  # field_{field_name}_sig stays as-is

        # Handle data signals
        if logical_name in ['data_sig']:
            return logical_name

        # Handle FIFO control signals
        if logical_name in ['i_write', 'o_wr_full', 'i_read', 'o_rd_empty']:
            fifo_signal_to_attr = {
                'i_write': 'write_sig',
                'o_wr_full': 'full_sig',
                'i_read': 'read_sig',
                'o_rd_empty': 'empty_sig'
            }
            return fifo_signal_to_attr.get(logical_name, logical_name)

        # Handle GAXI control signals
        if logical_name in ['i_valid', 'o_ready', 'o_valid', 'i_ready']:
            gaxi_signal_to_attr = {
                'i_valid': 'valid_sig',     # Slave reads valid
                'o_ready': 'ready_sig',     # Slave drives ready
                'o_valid': 'valid_sig',     # Master drives valid
                'i_ready': 'ready_sig'      # Master reads ready
            }
            return gaxi_signal_to_attr.get(logical_name, logical_name)

        return logical_name

    def apply_to_component(self, component):
        for logical_name, signal_obj in self.resolved_signals.items():
            if signal_obj is not None:
                attr_name = self._derive_attribute_name(logical_name)
                signal_name = self._find_signal_name(signal_obj)
                # Use the full signal name directly
                bus_signal = getattr(self.bus, signal_name)
                setattr(component, attr_name, bus_signal)

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
            'prefix': self.prefix,  # ADDED
            'signal_mapping_source': 'manual' if self.signal_map else 'automatic',  # NEW
            'total_ports_found': len(self.top_level_ports),
            'parameter_combinations': len(getattr(self, 'param_combinations', [])),  # May not exist for manual mapping
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

        # Add signal map info
        if self.signal_map:
            stats['signal_map'] = self.signal_map.copy()

        return stats


# Helper function to get caller info
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
