#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: struct_test_script
# Purpose: Struct Utilities Test Script
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""
Struct Utilities Test Script

Tests all struct-related functions from CocoTB utilities.
Usage: python test_struct_utilities.py <struct_file_path> <struct_name>

Examples:
    python test_struct_utilities.py rtl/amba/testcode/include/buffer_field_struct.sv axi_narrow
    python test_struct_utilities.py /bad/path/file.sv axi_narrow  # Test bad path
    python test_struct_utilities.py rtl/amba/testcode/include/buffer_field_struct.sv bad_struct  # Test bad struct name
"""

import sys
import os
import tempfile
from pathlib import Path

# Add the CocoTB framework to path
sys.path.insert(0, '../../bin')

def print_header(title):
    """Print a formatted header"""
    print(f"\n{'='*80}")
    print(f" {title}")
    print(f"{'='*80}")

def print_section(title):
    """Print a formatted section"""
    print(f"\n{'-'*60}")
    print(f" {title}")
    print(f"{'-'*60}")

def test_struct_utilities(struct_file_path, struct_name):
    """Test all struct utilities functions"""
    
    print_header(f"Testing Struct Utilities")
    print(f"File: {struct_file_path}")
    print(f"Struct: {struct_name}")
    
    # Create temp directory for outputs
    temp_dir = tempfile.mkdtemp()
    print(f"Temp directory: {temp_dir}")
    
    # Test 1: Basic file existence
    print_section("1. File Existence Check")
    abs_path = os.path.abspath(struct_file_path)
    print(f"Absolute path: {abs_path}")
    print(f"File exists: {os.path.exists(abs_path)}")
    
    if os.path.exists(abs_path):
        print(f"File size: {os.path.getsize(abs_path)} bytes")
        with open(abs_path, 'r') as f:
            content = f.read()
            print(f"Content length: {len(content)} characters")
            print(f"Contains 'StructStart': {'StructStart' in content}")
            print(f"Contains '{struct_name}': {struct_name in content}")
    
    # Test 2: Try importing utilities
    print_section("2. Import CocoTB Utilities")
    try:
        from CocoTBFramework.tbclasses.misc.utilities import (
            extract_struct_for_test, 
            extract_struct_for_test_simple,
            setup_struct_environment,
            validate_struct_setup,
            list_available_structs,
            get_struct_info
        )
        print("✓ Successfully imported all struct utilities")
    except ImportError as e:
        print(f"✗ Failed to import utilities: {e}")
        return False
    
    # Test 3: validate_struct_setup
    print_section("3. Testing validate_struct_setup()")
    try:
        success, message, structs = validate_struct_setup(abs_path)
        print(f"Success: {success}")
        print(f"Message: {message}")
        print(f"Available structs: {structs}")
    except Exception as e:
        print(f"✗ validate_struct_setup failed: {e}")
    
    # Test 4: list_available_structs
    print_section("4. Testing list_available_structs()")
    try:
        available_structs = list_available_structs(abs_path)
        print(f"Available structs: {available_structs}")
        print(f"Target struct '{struct_name}' in list: {struct_name in available_structs}")
    except Exception as e:
        print(f"✗ list_available_structs failed: {e}")
    
    # Test 5: get_struct_info
    print_section("5. Testing get_struct_info()")
    try:
        struct_info = get_struct_info(abs_path, struct_name)
        if struct_info:
            print(f"✓ Found struct info for '{struct_name}':")
            print(f"  Typedef name: {struct_info.get('typedef_name', 'N/A')}")
            print(f"  Bit width: {struct_info.get('bit_width', 'N/A')}")
            if 'field_info' in struct_info:
                print(f"  Fields ({len(struct_info['field_info'])}):")
                for field_name, field_data in struct_info['field_info'].items():
                    width = field_data.get('width', 'N/A')
                    print(f"    {field_name}: {width} bits")
            if 'validation' in struct_info:
                valid = struct_info['validation']['valid']
                msg = struct_info['validation']['message']
                print(f"  Validation: {'✓' if valid else '✗'} {msg}")
        else:
            print(f"✗ No struct info found for '{struct_name}'")
    except Exception as e:
        print(f"✗ get_struct_info failed: {e}")
    
    # Test 6: extract_struct_for_test (direct)
    print_section("6. Testing extract_struct_for_test() (direct)")
    try:
        struct_info = extract_struct_for_test(abs_path, struct_name, temp_dir)
        print(f"✓ Direct extraction successful!")
        print(f"  Success: {struct_info.get('success', 'N/A')}")
        print(f"  Struct name: {struct_info.get('struct_name', 'N/A')}")
        print(f"  Typedef name: {struct_info.get('typedef_name', 'N/A')}")
        print(f"  Bit width: {struct_info.get('bit_width', 'N/A')}")
        print(f"  Field count: {len(struct_info.get('field_info', {}))}")
        
        if 'files_generated' in struct_info:
            print(f"  Generated files:")
            for file_type, file_path in struct_info['files_generated'].items():
                exists = os.path.exists(file_path) if file_path else False
                print(f"    {file_type}: {file_path} (exists: {exists})")
                
        # Save struct_info for next test
        global saved_struct_info
        saved_struct_info = struct_info
        
    except Exception as e:
        print(f"✗ extract_struct_for_test failed: {e}")
        saved_struct_info = None
    
    # Test 7: setup_struct_environment
    print_section("7. Testing setup_struct_environment()")
    try:
        if saved_struct_info:
            env_vars = setup_struct_environment(saved_struct_info)
            print(f"✓ Generated {len(env_vars)} environment variables:")
            for key, value in env_vars.items():
                print(f"  {key} = '{value}'")
        else:
            print("✗ Skipping - no struct_info from previous test")
    except Exception as e:
        print(f"✗ setup_struct_environment failed: {e}")
    
    # Test 8: extract_struct_for_test_simple (auto-find)
    print_section("8. Testing extract_struct_for_test_simple() (auto-find)")
    try:
        # This will try to auto-find the struct file
        repo_root = os.getcwd()
        print(f"Using repo_root: {repo_root}")
        
        struct_info = extract_struct_for_test_simple(struct_name, temp_dir, repo_root)
        print(f"✓ Auto-find extraction successful!")
        print(f"  Found and extracted: {struct_info.get('struct_name', 'N/A')}")
        print(f"  Typedef name: {struct_info.get('typedef_name', 'N/A')}")
        print(f"  Bit width: {struct_info.get('bit_width', 'N/A')}")
        
    except Exception as e:
        print(f"✗ extract_struct_for_test_simple failed: {e}")
        print(f"   This is expected if the file isn't in standard search locations")
    
    # Test 9: Check generated files
    print_section("9. Checking Generated Files")
    if saved_struct_info and 'files_generated' in saved_struct_info:
        for file_type, file_path in saved_struct_info['files_generated'].items():
            if file_path and os.path.exists(file_path):
                print(f"✓ {file_type}: {file_path}")
                if file_type == 'python_helpers':
                    # Try to import the generated Python helpers
                    try:
                        import importlib.util
                        spec = importlib.util.spec_from_file_location("struct_helpers", file_path)
                        helpers_module = importlib.util.module_from_spec(spec)
                        spec.loader.exec_module(helpers_module)
                        
                        print(f"  ✓ Successfully imported generated Python helpers")
                        if hasattr(helpers_module, 'STRUCT_FIELDS'):
                            print(f"  ✓ STRUCT_FIELDS available: {list(helpers_module.STRUCT_FIELDS.keys())}")
                        if hasattr(helpers_module, 'pack_struct'):
                            print(f"  ✓ pack_struct function available")
                        if hasattr(helpers_module, 'unpack_struct'):
                            print(f"  ✓ unpack_struct function available")
                    except Exception as e:
                        print(f"  ✗ Failed to import Python helpers: {e}")
            else:
                print(f"✗ {file_type}: {file_path} (does not exist)")
    
    print_header("Test Summary")
    print(f"Temp directory (preserved for inspection): {temp_dir}")
    print("Review the output above to see which functions work and which don't.")
    
    return True

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python test_struct_utilities.py <struct_file_path> <struct_name>")
        print()
        print("Examples:")
        print("  python test_struct_utilities.py rtl/amba/testcode/include/buffer_field_struct.sv axi_narrow")
        print("  python test_struct_utilities.py /bad/path/file.sv axi_narrow  # Test bad path")
        print("  python test_struct_utilities.py rtl/amba/testcode/include/buffer_field_struct.sv bad_struct  # Test bad struct")
        sys.exit(1)
    
    struct_file_path = sys.argv[1]
    struct_name = sys.argv[2]
    
    test_struct_utilities(struct_file_path, struct_name)
