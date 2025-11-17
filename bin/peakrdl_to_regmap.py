#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: peakrdl_to_regmap
# Purpose: Convert PeakRDL SystemRDL files to RegisterMap dict format
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-11-14

"""
PeakRDL to RegisterMap Dictionary Converter

This script parses SystemRDL (.rdl) files using the PeakRDL toolchain and 
generates Python dictionary files compatible with the RegisterMap class format.

The RegisterMap class expects a dictionary with this structure:
{
    'top_block': {
        'register_name': {
            'type': 'reg',
            'name': 'register_name',
            'offset': '0xNN',      # hex string
            'address': '0xNN',     # hex string (same as offset for flat maps)
            'size': 4,             # bytes
            'default': '0xNN',     # hex string
            'sw': 'rw',            # software access: ro, rw, wo, etc.
            'count': 1,            # optional, for register arrays
            'field_name': {
                'type': 'field',
                'offset': 'N:M' or 'N',  # bit range or single bit
                'default': '0xN',        # hex string
                'sw': 'rw'               # software access
            },
            # ... more fields
        },
        # ... more registers
    }
}

Usage:
    peakrdl_to_regmap.py <input.rdl> -o <output.py>
    
Example:
    peakrdl_to_regmap.py hpet_regs.rdl -o hpet_regmap.py
    
The output file will contain a Python dict named 'top_block' that can be 
imported by RegisterMap.

Author: RTL Design Sherpa Project
License: MIT
"""

import os
import sys
import argparse
from pathlib import Path
from typing import Dict, Any
import pprint

try:
    from systemrdl import RDLCompiler, node
except ImportError as e:
    print(f"ERROR: Missing PeakRDL dependencies: {e}")
    print("\nInstall with:")
    print("  pip install systemrdl-compiler")
    sys.exit(1)


def get_sw_access(node_obj) -> str:
    """
    Determine software access mode from SystemRDL node.
    Maps SystemRDL access properties to RegisterMap format.
    """
    # Check if node has get_property method
    if not hasattr(node_obj, 'get_property'):
        return 'rw'
    
    try:
        # Try to get the sw property
        sw_access = node_obj.get_property('sw', default=None)
        if sw_access is None:
            return 'rw'
        
        if sw_access == node.AccessType.r:
            return 'ro'
        elif sw_access == node.AccessType.w:
            return 'wo'
        elif sw_access == node.AccessType.rw:
            return 'rw'
        elif sw_access == node.AccessType.na:
            return 'na'
    except:
        # If property doesn't exist or can't be accessed, default to rw
        pass
    
    # Default to rw if not specified
    return 'rw'


def get_field_offset(field_node) -> str:
    """
    Get bit offset/range for a field.
    Returns single bit as 'N', range as 'HIGH:LOW'
    """
    low_bit = field_node.low
    high_bit = field_node.high
    
    if low_bit == high_bit:
        return str(low_bit)
    else:
        return f"{high_bit}:{low_bit}"


def get_default_value(node_obj) -> str:
    """
    Extract default/reset value from node.
    Returns hex string like '0x00000000'
    """
    try:
        # For fields, check if there's a reset value
        if hasattr(node_obj, 'get_property') and isinstance(node_obj, node.FieldNode):
            # Try to get the reset value - may be None if not specified
            try:
                reset_val = node_obj.get_property('reset', default=None)
            except:
                reset_val = None
            
            if reset_val is not None:
                # Determine width for proper formatting
                width = node_obj.width
                hex_digits = (width + 3) // 4
                return f"0x{reset_val:0{hex_digits}X}"
        
        # For registers, aggregate field reset values
        if isinstance(node_obj, node.RegNode):
            reg_reset = 0
            for field in node_obj.fields():
                try:
                    field_reset = field.get_property('reset', default=0)
                except:
                    field_reset = 0
                if field_reset:
                    reg_reset |= (field_reset << field.low)
            
            width = node_obj.size * 8
            hex_digits = (width + 3) // 4
            return f"0x{reg_reset:0{hex_digits}X}"
            
    except Exception as e:
        pass
    
    return '0x0'


def process_field(field_node) -> Dict[str, Any]:
    """
    Process a field node and return dict entry.
    """
    field_dict = {
        'type': 'field',
        'offset': get_field_offset(field_node),
        'default': get_default_value(field_node),
        'sw': get_sw_access(field_node)
    }
    
    return field_dict


def process_register(reg_node, base_address: int = 0) -> Dict[str, Any]:
    """
    Process a register node and return dict entry with all fields.
    """
    # Basic register info
    reg_dict = {
        'type': 'reg',
        'name': reg_node.inst_name,
        'offset': f"0x{reg_node.address_offset:03X}",
        'address': f"0x{(base_address + reg_node.address_offset):03X}",
        'size': reg_node.size,  # size in bytes
        'default': get_default_value(reg_node),
        'sw': get_sw_access(reg_node)
    }
    
    # Process all fields in this register
    for field_node in reg_node.fields():
        field_name = field_node.inst_name
        reg_dict[field_name] = process_field(field_node)
    
    return reg_dict


def process_regfile(regfile_node, base_address: int = 0) -> Dict[str, Any]:
    """
    Process a regfile node (nested register block).
    Returns a dict with all registers in the regfile.
    """
    regfile_dict = {}
    
    for child in regfile_node.children():
        if isinstance(child, node.RegNode):
            reg_name = child.inst_name
            regfile_dict[reg_name] = process_register(child, base_address)
    
    return regfile_dict


def process_addrmap(addrmap_node) -> Dict[str, Any]:
    """
    Process the top-level address map.
    Returns nested dict with all registers and register files.
    """
    result = {}
    
    for child in addrmap_node.children():
        if isinstance(child, node.RegNode):
            # Direct register in addrmap
            reg_name = child.inst_name
            result[reg_name] = process_register(child)
            
        elif isinstance(child, node.RegfileNode):
            # Nested register file
            if child.is_array:
                # Array of register files (like HPET timers)
                # For arrays, we need to flatten them into individual indexed registers
                array_suffix = child.inst_name.upper()
                num_elements = child.array_dimensions[0]
                
                # Get the stride information - this tells us spacing between array elements
                try:
                    # Try to get properties from the original node without indexing
                    # The stride property '@= value' in RDL becomes array_stride
                    base_offset = child.raw_address_offset if hasattr(child, 'raw_address_offset') else 0
                    stride = child.total_array_stride() if hasattr(child, 'total_array_stride') else 32
                except:
                    # If we can't get stride, examine first child register to infer regfile size
                    regfile_size = 0
                    for reg in child.children():
                        if isinstance(reg, node.RegNode):
                            regfile_size = max(regfile_size, reg.address_offset + reg.size)
                    stride = regfile_size if regfile_size > 0 else 32
                    base_offset = 0
                
                # Process each array element
                for idx in range(num_elements):
                    elem_address = base_offset + (idx * stride)
                    
                    # Process each register in the regfile template
                    for reg_child in child.children():
                        if isinstance(reg_child, node.RegNode):
                            # Get register info
                            reg_dict = process_register(reg_child, 0)
                            reg_offset = int(reg_dict['offset'], 16)
                            
                            # Create indexed name
                            indexed_name = f"{array_suffix}{idx}_{reg_child.inst_name}"
                            result[indexed_name] = reg_dict.copy()
                            
                            # Update addresses for this array element
                            abs_offset = elem_address + reg_offset
                            result[indexed_name]['offset'] = f"0x{abs_offset:03X}"
                            result[indexed_name]['address'] = f"0x{abs_offset:03X}"
                            result[indexed_name]['array_index'] = idx
                            result[indexed_name]['array_name'] = array_suffix
            else:
                # Single register file
                regfile_regs = process_regfile(child, child.address_offset)
                result.update(regfile_regs)
        
        elif isinstance(child, node.AddrmapNode):
            # Nested address map (recursive)
            nested_regs = process_addrmap(child)
            result.update(nested_regs)
    
    return result


def convert_rdl_to_regmap(rdl_file: Path) -> Dict[str, Any]:
    """
    Main conversion function.
    Parses RDL file and returns RegisterMap-compatible dictionary.
    """
    print(f"📖 Compiling SystemRDL: {rdl_file}")
    
    # Compile RDL file
    rdlc = RDLCompiler()
    
    try:
        rdlc.compile_file(str(rdl_file))
        root = rdlc.elaborate()
        top = root.top
        
        print(f"✓ Compilation successful")
        print(f"  Address map: {top.inst_name}")
        print(f"  Address range: 0x{top.absolute_address:X} - 0x{top.absolute_address + top.size - 1:X}")
        
    except Exception as e:
        print(f"✗ Compilation failed: {e}")
        raise
    
    # Process the address map
    print(f"\n🔨 Processing registers...")
    register_dict = process_addrmap(top)
    
    print(f"✓ Processed {len(register_dict)} registers")
    
    # Wrap in top_block key as expected by RegisterMap
    return {'top_block': register_dict}


def write_python_dict(output_file: Path, reg_dict: Dict[str, Any], rdl_file: Path):
    """
    Write the dictionary to a Python file with proper formatting.
    """
    print(f"\n📝 Writing output: {output_file}")
    
    with open(output_file, 'w') as f:
        # Write header
        f.write(f"""# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Auto-generated register map from: {rdl_file.name}
# Generated by: peakrdl_to_regmap.py
# DO NOT EDIT MANUALLY - Regenerate from .rdl source
#
# Compatible with: bin/CocoTBFramework/tbclasses/apb/register_map.py

\"\"\"
Register map dictionary for {rdl_file.stem}

This file contains the register definitions in a format compatible with
the RegisterMap class. It was auto-generated from the SystemRDL specification.

Usage:
    from {output_file.stem} import top_block
    reg_map = RegisterMap('{output_file.name}', apb_data_width=32, 
                          apb_addr_width=16, start_address=0x0, log=logger)
\"\"\"

""")
        
        # Write the dictionary with nice formatting
        f.write("top_block = ")
        f.write(pprint.pformat(reg_dict['top_block'], width=100, compact=False))
        f.write("\n")
    
    print(f"✓ Generated: {output_file}")


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="Convert PeakRDL SystemRDL files to RegisterMap dictionary format",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s hpet_regs.rdl -o hpet_regmap.py
  %(prog)s pit_regs.rdl -o pit_regmap.py
        """
    )
    
    parser.add_argument(
        "rdl_file",
        type=Path,
        help="Input SystemRDL file (.rdl)"
    )
    
    parser.add_argument(
        "-o", "--output",
        type=Path,
        required=True,
        help="Output Python file (.py)"
    )
    
    args = parser.parse_args()
    
    # Validate input
    if not args.rdl_file.exists():
        print(f"ERROR: Input file not found: {args.rdl_file}")
        sys.exit(1)
    
    if not args.rdl_file.suffix == '.rdl':
        print(f"WARNING: Input file doesn't have .rdl extension")
    
    # Convert
    print("=" * 80)
    print("PeakRDL to RegisterMap Converter")
    print("=" * 80)
    
    try:
        reg_dict = convert_rdl_to_regmap(args.rdl_file)
        write_python_dict(args.output, reg_dict, args.rdl_file)
        
        print("\n" + "=" * 80)
        print("✅ Conversion Complete!")
        print("=" * 80)
        print(f"\nGenerated: {args.output}")
        print(f"\nRegister Summary:")
        print(f"  Total registers: {len(reg_dict['top_block'])}")
        
        # Count fields
        total_fields = 0
        for reg_data in reg_dict['top_block'].values():
            if isinstance(reg_data, dict):
                total_fields += sum(1 for v in reg_data.values() 
                                   if isinstance(v, dict) and v.get('type') == 'field')
        print(f"  Total fields: {total_fields}")
        
        return 0
        
    except Exception as e:
        print(f"\n✗ Conversion failed: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
