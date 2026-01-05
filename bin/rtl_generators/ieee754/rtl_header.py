# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: RTL Header Generator for IEEE 754-2008
# Purpose: Generate standard RTL file headers for auto-generated FP32 modules
#
# Documentation: IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from datetime import datetime


def generate_rtl_header(module_name, purpose, generator_script, documentation='IEEE754_ARCHITECTURE.md'):
    """
    Generate a standard RTL file header for auto-generated IEEE 754-2008 modules.

    Args:
        module_name: Name of the SystemVerilog module
        purpose: Brief description of module purpose
        generator_script: Name of the generator script that created this file
        documentation: Path to documentation file

    Returns:
        String containing the complete header
    """
    date_str = datetime.now().strftime('%Y-%m-%d')

    header = f'''// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: {module_name}
// Purpose: {purpose}
//
// Documentation: {documentation}
// Subsystem: common
//
// Author: sean galloway
// Created: {date_str}
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/{generator_script}
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

'''
    return header


def write_with_header(file_path, filename, module_name, purpose, generator_script,
                      content, documentation='IEEE754_ARCHITECTURE.md'):
    """
    Write a generated RTL file with proper header.

    Args:
        file_path: Directory to write the file
        filename: Name of the output file
        module_name: Name of the SystemVerilog module
        purpose: Brief description of module purpose
        generator_script: Name of the generator script
        content: Generated RTL content (without header)
        documentation: Path to documentation file
    """
    header = generate_rtl_header(module_name, purpose, generator_script, documentation)
    full_content = header + content

    with open(f'{file_path}/{filename}', 'w') as f:
        f.write(full_content)
