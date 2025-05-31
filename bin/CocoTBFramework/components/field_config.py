"""
Field Configuration Classes for GAXI Validation Framework

This module provides classes for defining field configurations in a robust and type-safe way,
replacing the dictionary-based approach with proper class structures.
"""
from dataclasses import dataclass
from typing import Dict, Tuple, List, Optional, Union, Any
from rich.console import Console
from rich.table import Table


@dataclass
class FieldDefinition:
    """
    Definition of a single field within a packet.

    Attributes:
        name: Field name
        bits: Width of the field in bits
        default: Default value for the field
        format: Display format ('hex', 'bin', 'dec')
        display_width: Width for display formatting
        active_bits: Tuple of (msb, lsb) defining active bit range
        description: Human-readable description of the field
        encoding: Optional dictionary mapping values to state names
    """
    name: str
    bits: int
    default: int = 0
    format: str = "hex"
    display_width: int = 0
    active_bits: Optional[Tuple[int, int]] = None
    description: Optional[str] = None
    encoding: Optional[Dict[int, str]] = None

    def __post_init__(self):
        """Validate and set derived values after initialization"""
        # Set active_bits to full width if not specified
        if self.active_bits is None:
            self.active_bits = (self.bits - 1, 0)

        # Validate active_bits range
        msb, lsb = self.active_bits
        if msb >= self.bits or lsb < 0 or msb < lsb:
            raise ValueError(f"Invalid active_bits ({msb}:{lsb}) for field '{self.name}' with width {self.bits}")

        # Set default display width based on format if not specified
        if self.display_width <= 0:
            if self.format == "bin":
                self.display_width = self.bits
            elif self.format == "hex":
                self.display_width = (self.bits + 3) // 4  # Round up to nearest 4 bits
            else:
                self.display_width = len(str(2**self.bits - 1))  # Width based on max value

        # Set description to name if not provided
        if self.description is None:
            self.description = self.name.replace('_', ' ').capitalize()

        # Initialize encoding to empty dict if None
        if self.encoding is None:
            self.encoding = {}

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary format for backward compatibility"""
        result = {
            'bits': self.bits,
            'default': self.default,
            'format': self.format,
            'display_width': self.display_width,
            'active_bits': self.active_bits,
            'description': self.description
        }
        # Only include encoding if it's not empty
        if self.encoding:
            result['encoding'] = self.encoding
        return result

    @classmethod
    def from_dict(cls, name: str, field_dict: Dict[str, Any]) -> 'FieldDefinition':
        """Create a FieldDefinition from a dictionary representation"""
        return cls(
            name=name,
            bits=field_dict.get('bits', 32),
            default=field_dict.get('default', 0),
            format=field_dict.get('format', 'hex'),
            display_width=field_dict.get('display_width', 0),
            active_bits=field_dict.get('active_bits'),
            description=field_dict.get('description'),
            encoding=field_dict.get('encoding')
        )


class FieldConfig:
    """
    Configuration of all fields in a packet, maintaining field order and providing
    helper methods for field manipulation.

    This class replaces the dictionary-based approach with a more robust structure
    that maintains field order and provides validation.
    """
    def __init__(self):
        """Initialize an empty field configuration"""
        self._fields: Dict[str, FieldDefinition] = {}
        self._field_order: List[str] = []

    def add_field(self, field_def: FieldDefinition) -> 'FieldConfig':
        """
        Add a field to the configuration.

        Args:
            field_def: Field definition to add

        Returns:
            Self for method chaining
        """
        name = field_def.name
        if name in self._fields:
            raise ValueError(f"Field '{name}' already exists in configuration")

        self._fields[name] = field_def
        self._field_order.append(name)
        return self

    def add_field_dict(self, name: str, field_dict: Dict[str, Any]) -> 'FieldConfig':
        """
        Add a field from dictionary representation (for backward compatibility).

        Args:
            name: Field name
            field_dict: Dictionary containing field attributes

        Returns:
            Self for method chaining
        """
        field_def = FieldDefinition.from_dict(name, field_dict)
        return self.add_field(field_def)

    def remove_field(self, name: str) -> 'FieldConfig':
        """
        Remove a field from the configuration.

        Args:
            name: Name of the field to remove

        Returns:
            Self for method chaining
        """
        if name in self._fields:
            del self._fields[name]
            self._field_order.remove(name)
        return self

    def get_field(self, name: str) -> FieldDefinition:
        """
        Get a field definition by name.

        Args:
            name: Field name to retrieve

        Returns:
            FieldDefinition for the requested field

        Raises:
            KeyError if field doesn't exist
        """
        if name not in self._fields:
            raise KeyError(f"Field '{name}' not found in configuration")
        return self._fields[name]

    def has_field(self, name: str) -> bool:
        """
        Check if a field exists in the configuration.

        Args:
            name: Field name to check

        Returns:
            True if field exists, False otherwise
        """
        return name in self._fields

    def field_names(self) -> List[str]:
        """
        Get ordered list of field names.

        Returns:
            List of field names in definition order
        """
        return self._field_order.copy()

    def fields(self) -> List[FieldDefinition]:
        """
        Get ordered list of field definitions.

        Returns:
            List of field definitions in definition order
        """
        return [self._fields[name] for name in self._field_order]

    def items(self):
        """
        Get name/definition pairs in order, similar to dict.items().

        Returns:
            Iterator of (name, field_def) tuples
        """
        for name in self._field_order:
            yield name, self._fields[name]

    def __iter__(self):
        """Iterator over field names (like dict.__iter__)"""
        return iter(self._field_order)

    def __getitem__(self, name: str) -> FieldDefinition:
        """Dict-like access to fields"""
        return self.get_field(name)

    def __contains__(self, name: str) -> bool:
        """Support for 'in' operator"""
        return self.has_field(name)

    def __len__(self) -> int:
        """Number of fields in the configuration"""
        return len(self._field_order)

    def _get_encoding(self, field_name: str, value: int) -> str:
        """
        Get the encoded string for a field value.

        Args:
            field_name: Name of the field
            value: Numeric value to decode

        Returns:
            Encoded string if found, otherwise hex representation of the value
        """
        if field_name not in self._fields:
            return f"0x{value:X}"

        field_def = self._fields[field_name]
        if field_def.encoding and value in field_def.encoding:
            return field_def.encoding[value]
        else:
            return f"0x{value:X}"

    def to_dict(self) -> Dict[str, Dict[str, Any]]:
        """
        Convert to dictionary format for backward compatibility.

        Returns:
            Dictionary representation of all fields
        """
        return {name: field_def.to_dict() for name, field_def in self.items()}

    def create_packet(self):
        """
        Create a packet object compatible with the field configuration.

        This method creates a GAXIPacket using this field configuration,
        which is needed for the testbench code that calls field_config.create_packet().

        Returns:
            GAXIPacket instance initialized with this field configuration
        """
        # Import here to avoid circular dependency
        try:
            from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
            return GAXIPacket(self)
        except ImportError:
            # Fallback: create a simple packet-like object
            class SimplePacket:
                def __init__(self, field_config):
                    self._field_config = field_config
                    # Set default values for all fields
                    for field_name, field_def in field_config.items():
                        setattr(self, field_name, field_def.default)

            return SimplePacket(self)

    def debug_str(self, indent=0) -> str:
        """
        Return a formatted string representation of the field configuration using Rich.

        Args:
            indent: Number of spaces to indent the output

        Returns:
            Formatted string showing all fields and their properties
        """
        indent_str = ' ' * indent
        console = Console(record=True)

        if not self._field_order:
            return f"{indent_str}FieldConfig with 0 fields:\n{indent_str} (empty)"

        table = Table(title=f"FieldConfig with {len(self)} fields:")

        # Add columns
        table.add_column("Field Name", style="cyan")
        table.add_column("Bits", justify="right", style="green")
        table.add_column("Format", style="magenta")
        table.add_column("Active Bits", style="blue")
        table.add_column("Default", style="yellow")
        table.add_column("Encoding", style="bright_yellow")
        table.add_column("Description")

        # Add rows for each field
        for name, field_def in self.items():
            active_bits_str = f"({field_def.active_bits[0]}:{field_def.active_bits[1]})"
            default_str = f"0x{field_def.default:X}" if field_def.format == 'hex' else str(field_def.default)

            # Format encoding information
            if field_def.encoding:
                encoding_values = ", ".join(f"{k}:{v}" for k, v in field_def.encoding.items())
                encoding_str = f"{{{encoding_values}}}"
            else:
                encoding_str = ""

            table.add_row(
                name,
                str(field_def.bits),
                field_def.format,
                active_bits_str,
                default_str,
                encoding_str,
                field_def.description
            )

        # Add a footer row for total bits
        total_bits = self.get_total_bits()

        # Print the table to the console and capture the output
        console.print(table)
        console.print(f"{indent_str}Total bits: {total_bits}")

        # Return the captured output as a string
        return f"{indent_str}{console.export_text()}"

    def __str__(self) -> str:
        """String representation of the FieldConfig"""
        return self.debug_str()

    def __repr__(self) -> str:
        """Detailed representation of the FieldConfig"""
        return self.debug_str()

    def update_field_width(self, field_name: str, new_bits: int, update_active_bits: bool = True) -> 'FieldConfig':
        """
        Update a field's bit width and optionally its active bits.

        Args:
            field_name: Name of the field to update
            new_bits: New bit width
            update_active_bits: If True, also update active_bits to full range

        Returns:
            Self for method chaining
        """
        if field_name not in self._fields:
            raise KeyError(f"Field '{field_name}' not found in configuration")

        field_def = self._fields[field_name]
        field_def.bits = new_bits

        if update_active_bits:
            field_def.active_bits = (new_bits - 1, 0)

        # Update display width if using hex format
        if field_def.format == 'hex':
            field_def.display_width = (new_bits + 3) // 4

        return self

    def set_encoding(self, field_name: str, encoding: Dict[int, str]) -> 'FieldConfig':
        """
        Set an encoding dictionary for a field.

        Args:
            field_name: Name of the field
            encoding: Dictionary mapping values to state names

        Returns:
            Self for method chaining
        """
        if field_name not in self._fields:
            raise KeyError(f"Field '{field_name}' not found in configuration")

        self._fields[field_name].encoding = encoding
        return self

    def add_encoding_value(self, field_name: str, value: int, state_name: str) -> 'FieldConfig':
        """
        Add a single encoding value to a field.

        Args:
            field_name: Name of the field
            value: Value to encode
            state_name: Name for the state

        Returns:
            Self for method chaining
        """
        if field_name not in self._fields:
            raise KeyError(f"Field '{field_name}' not found in configuration")

        field_def = self._fields[field_name]
        if field_def.encoding is None:
            field_def.encoding = {}

        field_def.encoding[value] = state_name
        return self

    @classmethod
    def from_dict(cls, field_dict: Dict[str, Dict[str, Any]]) -> 'FieldConfig':
        """
        Create a FieldConfig from a dictionary representation.

        Args:
            field_dict: Dictionary mapping field names to field properties

        Returns:
            New FieldConfig instance
        """
        config = cls()
        # Process fields in order they appear in the dictionary
        for name, props in field_dict.items():
            config.add_field_dict(name, props)
        return config

    @classmethod
    def validate_and_create(cls, field_dict: Dict[str, Dict[str, Any]],
                            raise_errors: bool = False) -> 'FieldConfig':
        """
        Validate a dictionary-based field configuration and convert to FieldConfig object.

        This method performs quality checks on an existing dictionary-based field configuration
        and converts it to the new FieldConfig class. It will also correct common issues when
        possible.

        Args:
            field_dict: Dictionary mapping field names to field properties
            raise_errors: If True, raise exceptions for validation errors;
                            if False, attempt to correct or warn about issues

        Returns:
            New validated FieldConfig instance

        Raises:
            ValueError: If raise_errors is True and validation fails
        """
        config = cls()
        errors = []
        warnings = []

        # Empty configuration check
        if not field_dict:
            warnings.append("Empty field configuration provided")
            return config

        # Iterate through fields and validate
        for field_name, field_props in field_dict.items():
            # Field name validation
            if not isinstance(field_name, str):
                msg = f"Field name must be a string, got {type(field_name).__name__}"
                if raise_errors:
                    raise ValueError(msg)
                errors.append(msg)
                continue

            if not field_name:
                msg = "Empty field name provided"
                if raise_errors:
                    raise ValueError(msg)
                errors.append(msg)
                continue

            # Required field properties
            if 'bits' not in field_props:
                msg = f"Field '{field_name}' is missing required 'bits' property"
                if raise_errors:
                    raise ValueError(msg)
                warnings.append(msg)
                field_props['bits'] = 32  # Default to 32 bits

            # Type checking for critical properties
            if not isinstance(field_props.get('bits'), int):
                msg = f"Field '{field_name}' has non-integer 'bits' value: {field_props.get('bits')}"
                if raise_errors:
                    raise ValueError(msg)
                warnings.append(msg)
                # Try to convert to int if possible
                try:
                    field_props['bits'] = int(field_props['bits'])
                except (ValueError, TypeError):
                    field_props['bits'] = 32  # Default to 32 bits

            # Validate bits > 0
            if field_props.get('bits', 0) <= 0:
                msg = f"Field '{field_name}' has invalid 'bits' value: {field_props.get('bits')}"
                if raise_errors:
                    raise ValueError(msg)
                warnings.append(msg)
                field_props['bits'] = 32  # Default to 32 bits

            # Validate active_bits if present
            if 'active_bits' in field_props:
                active_bits = field_props['active_bits']
                if not isinstance(active_bits, tuple) or len(active_bits) != 2:
                    msg = f"Field '{field_name}' has invalid 'active_bits' format: {active_bits}"
                    if raise_errors:
                        raise ValueError(msg)
                    warnings.append(msg)
                    # Use full field width as default
                    field_props['active_bits'] = (field_props['bits'] - 1, 0)
                else:
                    msb, lsb = active_bits
                    bits = field_props['bits']

                    if msb >= bits or lsb < 0 or msb < lsb:
                        msg = f"Field '{field_name}' has invalid 'active_bits' range: {active_bits}"
                        if raise_errors:
                            raise ValueError(msg)
                        warnings.append(msg)
                        # Correct to valid range
                        field_props['active_bits'] = (min(bits - 1, max(0, msb)), max(0, min(bits - 1, lsb)))

            # Validate format if present
            if 'format' in field_props and field_props['format'] not in ['hex', 'bin', 'dec']:
                msg = f"Field '{field_name}' has invalid 'format': {field_props['format']}"
                if raise_errors:
                    raise ValueError(msg)
                warnings.append(msg)
                field_props['format'] = 'hex'  # Default to hex

            # Validate encoding if present
            if 'encoding' in field_props:
                encoding = field_props['encoding']
                if not isinstance(encoding, dict):
                    msg = f"Field '{field_name}' has invalid 'encoding' (not a dictionary): {encoding}"
                    if raise_errors:
                        raise ValueError(msg)
                    warnings.append(msg)
                    field_props['encoding'] = {}  # Default to empty dict
                else:
                    # Validate encoding keys and values
                    valid_encoding = {}
                    for k, v in encoding.items():
                        try:
                            key = k if isinstance(k, int) else int(k)
                            valid_encoding[key] = str(v)
                        except (ValueError, TypeError) as e:
                            msg = f"Field '{field_name}' has invalid encoding key/value: {k}:{v}"
                            if raise_errors:
                                raise ValueError(msg) from e
                            warnings.append(msg)
                    field_props['encoding'] = valid_encoding

            # Add the field to the configuration
            try:
                config.add_field_dict(field_name, field_props)
            except Exception as e:
                msg = f"Failed to add field '{field_name}': {str(e)}"
                if raise_errors:
                    raise ValueError(msg) from e
                errors.append(msg)

        # Log any warnings or errors
        for warning in warnings:
            print(f"WARNING: {warning}")

        for error in errors:
            print(f"ERROR: {error}")

        return config

    @classmethod
    def create_data_only(cls, data_width: int = 32) -> 'FieldConfig':
        """
        Create a simple data-only field configuration.

        Args:
            data_width: Width of the data field in bits

        Returns:
            FieldConfig with a single 'data' field
        """
        config = cls()
        config.add_field(FieldDefinition(
            name="data",
            bits=data_width,
            format="hex",
            description="Data value"
        ))
        return config

    @classmethod
    def create_standard(cls, addr_width: int = 32, data_width: int = 32) -> 'FieldConfig':
        """
        Create a standard address/data field configuration.

        Args:
            addr_width: Width of the address field in bits
            data_width: Width of the data field in bits

        Returns:
            FieldConfig with 'addr' and 'data' fields
        """
        config = cls()
        config.add_field(FieldDefinition(
            name="addr",
            bits=addr_width,
            format="hex",
            description="Address"
        ))
        config.add_field(FieldDefinition(
            name="data",
            bits=data_width,
            format="hex",
            description="Data value"
        ))
        return config

    @classmethod
    def create_multi_data(cls, addr_width: int = 4, ctrl_width: int = 4,
                            data_width: int = 8, num_data: int = 2) -> 'FieldConfig':
        """
        Create a multi-data field configuration with addr, ctrl, and multiple data fields.

        Args:
            addr_width: Width of the address field in bits
            ctrl_width: Width of the control field in bits
            data_width: Width of each data field in bits
            num_data: Number of data fields (data0, data1, etc.)

        Returns:
            FieldConfig with addr, ctrl, and multiple data fields
        """
        config = cls()

        # Add address field
        config.add_field(FieldDefinition(
            name="addr",
            bits=addr_width,
            format="hex",
            description="Address"
        ))

        # Add control field
        config.add_field(FieldDefinition(
            name="ctrl",
            bits=ctrl_width,
            format="hex",
            description="Control"
        ))

        # Add data fields
        for i in range(num_data):
            config.add_field(FieldDefinition(
                name=f"data{i}",
                bits=data_width,
                format="hex",
                description=f"Data {i}"
            ))

        return config

    def get_total_bits(self) -> int:
        """
        Calculate the total number of bits across all fields.

        Returns:
            Sum of all field widths
        """
        return sum(field.bits for field in self.fields())
