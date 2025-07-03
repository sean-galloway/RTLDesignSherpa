"""
SystemVerilog Struct Parser for CocoTB Framework

Core struct parsing functionality that integrates with the CocoTB test framework.
Handles extraction, validation, and generation of struct-related files.

This module provides:
- StructParser class for parsing SystemVerilog files
- Helper functions for generating include files and Python helpers
- Integration with the existing CocoTB test infrastructure
"""

import os
import re
import json
from pathlib import Path
from typing import Dict, Optional, Tuple, List


class StructParser:
    """
    SystemVerilog struct parser for the CocoTB framework.

    Parses SystemVerilog files looking for struct definitions marked with:
    // StructStart: structName
    typedef struct packed { ... } typedef_name;
    // StructEnd: structName
    """

    def __init__(self, file_path: str):
        """Initialize parser with a SystemVerilog file path."""
        self.file_path = Path(file_path)
        self.structs = {}
        self._parse_file()

    def _parse_file(self):
        """Parse the file and extract all marked struct definitions."""
        if not self.file_path.exists():
            raise FileNotFoundError(f"File not found: {self.file_path}")

        with open(self.file_path, 'r') as f:
            content = f.read()

        # Find all struct blocks using regex
        pattern = r'//\s*StructStart:\s*(\w+)\s*\n(.*?)//\s*StructEnd:\s*\1'
        matches = re.findall(pattern, content, re.DOTALL | re.MULTILINE)

        for struct_name, struct_content in matches:
            # Clean up the struct content
            cleaned_content = self._clean_struct_content(struct_content.strip())

            # Extract the typedef name from the struct
            typedef_name = self._extract_typedef_name(cleaned_content)

            self.structs[struct_name] = {
                'content': cleaned_content,
                'typedef_name': typedef_name,
                'full_definition': cleaned_content,
                'field_info': self._parse_struct_fields(cleaned_content)
            }

    def _clean_struct_content(self, content: str) -> str:
        """Clean up struct content by removing extra whitespace and comments."""
        lines = []
        for line in content.split('\n'):
            # Remove inline comments but preserve the struct definition
            if '//' in line and not line.strip().startswith('//'):
                line = line.split('//')[0].rstrip()

            # Skip empty lines and comment-only lines
            stripped = line.strip()
            if stripped and not stripped.startswith('//'):
                lines.append(line)

        return '\n'.join(lines)

    def _extract_typedef_name(self, struct_content: str) -> Optional[str]:
        """Extract the typedef name from the struct definition."""
        # Look for typedef struct ... } name_t;
        match = re.search(r'typedef\s+struct\s+packed\s*\{.*?\}\s*(\w+)\s*;',
                         struct_content, re.DOTALL)
        if match:
            return match.group(1)

        # Look for just struct ... } name_t;
        match = re.search(r'struct\s+packed\s*\{.*?\}\s*(\w+)\s*;',
                         struct_content, re.DOTALL)
        if match:
            return match.group(1)

        return None

    def _parse_struct_fields(self, struct_content: str) -> Dict:
        """Parse struct fields from SystemVerilog struct definition."""
        fields = {}

        # Find the struct body
        struct_match = re.search(r'struct\s+packed\s*\{(.*?)\}', struct_content, re.DOTALL)
        if not struct_match:
            return fields

        struct_body = struct_match.group(1)

        # Parse individual field lines - handle various SystemVerilog formats
        patterns = [
            r'logic\s*(?:\[(\d+)(?::(\d+))?\])?\s*(\w+)\s*;',  # logic [MSB:LSB] name;
            r'logic\s+signed\s*(?:\[(\d+)(?::(\d+))?\])?\s*(\w+)\s*;',  # logic signed [MSB:LSB] name;
        ]

        for line in struct_body.split('\n'):
            line = line.strip()
            if not line or line.startswith('//'):
                continue

            for pattern in patterns:
                match = re.search(pattern, line)
                if match:
                    msb, lsb, field_name = match.groups()

                    if msb is not None:
                        msb = int(msb)
                        lsb = int(lsb) if lsb is not None else 0
                        width = msb - lsb + 1
                    else:
                        width = 1  # Single bit logic
                        msb = 0
                        lsb = 0

                    fields[field_name] = {
                        "width": width,
                        "msb": msb,
                        "lsb": lsb
                    }
                    break  # Found a match, no need to try other patterns

        return fields

    def get_struct(self, struct_name: str) -> Optional[Dict[str, str]]:
        """Get a specific struct definition by name."""
        return self.structs.get(struct_name)

    def get_struct_content(self, struct_name: str) -> Optional[str]:
        """Get just the struct content string."""
        struct_info = self.get_struct(struct_name)
        return struct_info['content'] if struct_info else None

    def get_typedef_name(self, struct_name: str) -> Optional[str]:
        """Get the typedef name for a struct."""
        struct_info = self.get_struct(struct_name)
        return struct_info['typedef_name'] if struct_info else None

    def get_field_info(self, struct_name: str) -> Optional[Dict]:
        """Get field information for a struct."""
        struct_info = self.get_struct(struct_name)
        return struct_info['field_info'] if struct_info else None

    def list_structs(self) -> List[str]:
        """List all available struct names."""
        return list(self.structs.keys())

    def validate_struct_syntax(self, struct_name: str) -> Tuple[bool, str]:
        """Basic validation of struct syntax."""
        struct_info = self.get_struct(struct_name)
        if not struct_info:
            return False, f"Struct '{struct_name}' not found"

        content = struct_info['content']

        # Check for basic struct syntax
        if not re.search(r'typedef\s+struct\s+packed\s*\{', content):
            if not re.search(r'struct\s+packed\s*\{', content):
                return False, "Missing 'struct packed {' declaration"

        # Check for closing brace and semicolon
        if not re.search(r'\}\s*\w+\s*;', content):
            return False, "Missing closing '} typename;'"

        # Check for balanced braces
        open_braces = content.count('{')
        close_braces = content.count('}')
        if open_braces != close_braces:
            return False, f"Unbalanced braces: {open_braces} open, {close_braces} close"

        return True, "Valid struct syntax"

    def generate_include_file(self, struct_name: str, output_path: str) -> bool:
        """Generate a SystemVerilog include file with the specified struct."""
        struct_info = self.get_struct(struct_name)
        if not struct_info:
            return False

        include_content = f"""// Auto-generated struct include file
// Generated from: {self.file_path}
// Struct: {struct_name}
// Generated by CocoTB Framework

{struct_info['content']}
"""

        output_file = Path(output_path)
        output_file.parent.mkdir(parents=True, exist_ok=True)

        with open(output_file, 'w') as f:
            f.write(include_content)

        return True


class StructHelper:
    """Helper class for generating struct-related files and utilities."""

    @staticmethod
    def generate_python_helpers(struct_name: str, typedef_name: str, struct_content: str,
                               field_info: Dict, output_dir: str) -> str:
        """Generate Python helper file for cocotb testing."""

        # Calculate total bit width
        total_width = sum(field["width"] for field in field_info.values()) if field_info else 0

        helper_content = f'''"""
Auto-generated struct helpers for CocoTB testing
Generated from struct: {struct_name}
Typedef: {typedef_name}
Total bit width: {total_width}

This file is generated by the CocoTB Framework struct utilities.
"""

import random

# Struct metadata
STRUCT_NAME = "{struct_name}"
STRUCT_TYPEDEF_NAME = "{typedef_name}"
STRUCT_BIT_WIDTH = {total_width}

# Field definitions: {{field_name: {{width, msb, lsb}}}}
STRUCT_FIELDS = {repr(field_info)}

# Raw struct content for reference
STRUCT_CONTENT = """{struct_content}"""


def get_struct_bit_width():
    """Get total bit width of the struct"""
    return STRUCT_BIT_WIDTH


def get_field_names():
    """Get list of all field names in struct order"""
    return list(STRUCT_FIELDS.keys())


def get_field_info(field_name):
    """Get information about a specific field"""
    return STRUCT_FIELDS.get(field_name, None)


def pack_struct(**field_values):
    """
    Pack field values into a single integer representing the struct.

    Args:
        **field_values: Keyword arguments for field values

    Returns:
        int: Packed struct value

    Example:
        packed = pack_struct(addr=0x1000, id=5, data=0xDEADBEEF, valid_flag=1)
    """
    packed_value = 0
    bit_offset = 0

    # Pack fields in reverse order (LSB first for SystemVerilog packed structs)
    for field_name in reversed(list(STRUCT_FIELDS.keys())):
        field_info = STRUCT_FIELDS[field_name]
        field_width = field_info["width"]

        if field_name in field_values:
            field_value = field_values[field_name] & ((1 << field_width) - 1)  # Mask to field width
            packed_value |= (field_value << bit_offset)

        bit_offset += field_width

    return packed_value


def unpack_struct(packed_value):
    """
    Unpack a packed struct value into individual field values.

    Args:
        packed_value (int): Packed struct value

    Returns:
        dict: Dictionary with field names as keys and values as integers

    Example:
        fields = unpack_struct(0x12345678)
        addr = fields['addr']
        id_val = fields['id']
    """
    fields = {{}}
    bit_offset = 0

    # Unpack fields in reverse order (LSB first)
    for field_name in reversed(list(STRUCT_FIELDS.keys())):
        field_info = STRUCT_FIELDS[field_name]
        field_width = field_info["width"]

        # Extract field value
        mask = (1 << field_width) - 1
        field_value = (packed_value >> bit_offset) & mask
        fields[field_name] = field_value

        bit_offset += field_width

    return fields


def validate_field_value(field_name, value):
    """
    Validate that a field value fits within the field's bit width.

    Args:
        field_name (str): Name of the field
        value (int): Value to validate

    Returns:
        bool: True if value is valid for the field
    """
    if field_name not in STRUCT_FIELDS:
        return False

    field_width = STRUCT_FIELDS[field_name]["width"]
    max_value = (1 << field_width) - 1

    return 0 <= value <= max_value


def generate_random_struct(seed=None, **overrides):
    """
    Generate a random struct with reasonable values.

    Args:
        seed (int, optional): Random seed for reproducibility
        **overrides: Override specific field values

    Returns:
        int: Packed struct value with random field values
    """
    if seed is not None:
        random.seed(seed)

    field_values = {{}}

    for field_name, field_info in STRUCT_FIELDS.items():
        if field_name in overrides:
            field_values[field_name] = overrides[field_name]
        else:
            field_width = field_info["width"]
            max_value = (1 << field_width) - 1

            # Generate reasonable defaults based on field name patterns
            if field_name.endswith('_flag') or field_name in ['valid', 'last', 'error']:
                field_values[field_name] = random.choice([0, 1])
            elif field_name == 'addr':
                # Generate aligned addresses
                field_values[field_name] = random.randrange(0x1000, min(0x10000, max_value), 0x100)
            elif field_name == 'id':
                field_values[field_name] = random.randint(0, min(255, max_value))
            elif field_name == 'data':
                field_values[field_name] = random.randint(0, max_value)
            elif 'type' in field_name or 'size' in field_name:
                field_values[field_name] = random.randint(0, min(7, max_value))
            else:
                field_values[field_name] = random.randint(0, max_value)

    return pack_struct(**field_values)


def create_test_sequence(count=10, seed=None, pattern='random'):
    """
    Create a sequence of test struct values.

    Args:
        count (int): Number of struct values to generate
        seed (int, optional): Random seed for reproducibility
        pattern (str): Pattern type ('random', 'incremental', 'corner_cases')

    Returns:
        list: List of packed struct values
    """
    if seed is not None:
        random.seed(seed)

    sequence = []

    if pattern == 'incremental':
        for i in range(count):
            overrides = {{}}
            for field_name in STRUCT_FIELDS:
                if field_name == 'addr':
                    overrides[field_name] = 0x1000 + (i * 0x100)
                elif field_name == 'id':
                    overrides[field_name] = i % (1 << STRUCT_FIELDS[field_name]["width"])
                elif field_name == 'data':
                    overrides[field_name] = 0xDEADBEEF + i
                elif field_name in ['last', 'valid_flag', 'valid']:
                    overrides[field_name] = 1 if i == count - 1 else 0

            sequence.append(generate_random_struct(seed=seed+i, **overrides))

    elif pattern == 'corner_cases':
        # Generate corner case values
        for i in range(count):
            overrides = {{}}
            for field_name, field_info in STRUCT_FIELDS.items():
                field_width = field_info["width"]
                max_value = (1 << field_width) - 1

                if i == 0:
                    # All zeros
                    overrides[field_name] = 0
                elif i == 1:
                    # All ones (max values)
                    overrides[field_name] = max_value
                elif i == 2:
                    # Alternating bits
                    overrides[field_name] = 0x55555555 & max_value
                elif i == 3:
                    # Inverted alternating bits
                    overrides[field_name] = 0xAAAAAAAA & max_value
                else:
                    # Random for remaining
                    overrides[field_name] = random.randint(0, max_value)

            sequence.append(pack_struct(**overrides))

    else:  # random pattern
        for i in range(count):
            sequence.append(generate_random_struct(seed=seed+i if seed else None))

    return sequence


if __name__ == "__main__":
    # When run as script, print struct information
    print(f"Struct: {{STRUCT_NAME}} (typedef: {{STRUCT_TYPEDEF_NAME}})")
    print(f"Total bit width: {{STRUCT_BIT_WIDTH}}")
    print("Fields:")
    for field_name, field_info in STRUCT_FIELDS.items():
        width = field_info["width"]
        if width == 1:
            print(f"  {{field_name:15}} : 1 bit")
        else:
            msb = field_info["msb"]
            lsb = field_info["lsb"]
            print(f"  {{field_name:15}} : {{width:2}} bits [{{msb}}:{{lsb}}]")
'''

        info_file = os.path.join(output_dir, f"struct_helpers_{typedef_name}.py")
        os.makedirs(output_dir, exist_ok=True)

        with open(info_file, 'w') as f:
            f.write(helper_content)

        return info_file

    @staticmethod
    def generate_environment_file(struct_name: str, typedef_name: str, struct_content: str,
                                include_file: str, python_helpers_file: str, output_dir: str) -> str:
        """Generate shell environment file for easy variable setting."""

        env_content = f'''#!/bin/bash
# Auto-generated environment variables for struct: {struct_name}
# Generated by CocoTB Framework
# Source this file to set up environment for testing

export TEST_STRUCT_NAME="{struct_name}"
export TEST_TYPEDEF_NAME="{typedef_name}"
export TEST_STRUCT_FILE="{os.path.abspath(include_file)}"
export TEST_STRUCT_HELPERS="{os.path.abspath(python_helpers_file)}"
export TEST_STRUCT_CONTENT="{struct_content.replace('"', '\\"').replace('\\n', '\\\\n')}"

echo "CocoTB Framework: Set up environment for struct: {struct_name}"
echo "  TEST_STRUCT_NAME=$TEST_STRUCT_NAME"
echo "  TEST_TYPEDEF_NAME=$TEST_TYPEDEF_NAME"
echo "  TEST_STRUCT_FILE=$TEST_STRUCT_FILE"
echo "  TEST_STRUCT_HELPERS=$TEST_STRUCT_HELPERS"
'''

        env_file = os.path.join(output_dir, f"struct_env_{struct_name}.sh")
        os.makedirs(output_dir, exist_ok=True)

        with open(env_file, 'w') as f:
            f.write(env_content)

        # Make executable
        os.chmod(env_file, 0o755)

        return env_file


def validate_struct_setup(struct_file: str) -> Tuple[bool, str, List[str]]:
    """
    Validate that a struct file is readable and contains valid structs.

    Args:
        struct_file (str): Path to SystemVerilog file with struct definitions

    Returns:
        tuple: (success, message, list_of_available_structs)
    """
    try:
        if not os.path.exists(struct_file):
            return False, f"Struct file not found: {struct_file}", []

        parser = StructParser(struct_file)
        available_structs = parser.list_structs()

        if not available_structs:
            return False, f"No valid structs found in {struct_file}", []

        # Validate each struct
        invalid_structs = []
        for struct_name in available_structs:
            is_valid, validation_msg = parser.validate_struct_syntax(struct_name)
            if not is_valid:
                invalid_structs.append(f"{struct_name}: {validation_msg}")

        if invalid_structs:
            return False, f"Invalid structs found: {'; '.join(invalid_structs)}", available_structs

        return True, f"Found {len(available_structs)} valid structs", available_structs

    except Exception as e:
        return False, f"Error parsing struct file: {str(e)}", []

