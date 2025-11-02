#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SVModuleParser
# Purpose: Generate GTKWave Save Files for RTL Common Library
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""
Generate GTKWave Save Files for RTL Common Library

This script parses SystemVerilog modules and automatically generates .gtkw
save files with organized signal groupings.

Usage:
    python bin/generate_gtkw_files.py [--output val/common/GTKW]
"""

import os
import re
import argparse
from pathlib import Path
from typing import List, Dict, Tuple
from datetime import datetime

class SVModuleParser:
    """Parse SystemVerilog module to extract ports and internal signals"""

    def __init__(self, sv_file: str):
        self.sv_file = sv_file
        self.module_name = None
        self.parameters = []
        self.inputs = []
        self.outputs = []
        self.inouts = []
        self.internals = {'registers': [], 'wires': []}

    def parse(self) -> bool:
        """Parse SystemVerilog file"""
        try:
            with open(self.sv_file, 'r') as f:
                content = f.read()

            # Extract module name
            module_match = re.search(r'module\s+(\w+)\s*[#(]', content)
            if not module_match:
                return False
            self.module_name = module_match.group(1)

            # Extract parameters
            param_pattern = r'parameter\s+(?:int\s+)?(\w+)\s*=\s*([^,;)]+)'
            for match in re.finditer(param_pattern, content):
                self.parameters.append(match.group(1))

            # Extract ports (multiline-aware)
            port_section = self._extract_port_section(content)
            if port_section:
                self._parse_ports(port_section)

            # Extract internal signals
            self._parse_internals(content)

            return True

        except Exception as e:
            print(f"Error parsing {self.sv_file}: {e}")
            return False

    def _extract_port_section(self, content: str) -> str:
        """Extract port declaration section"""
        # Find module declaration start
        module_start = content.find('module ')
        if module_start == -1:
            return ""

        # Find module name
        module_match = re.search(r'module\s+(\w+)', content[module_start:])
        if not module_match:
            return ""

        # Look for port list - skip parameter list if present
        search_start = module_start + module_match.end()

        # Check if there's a parameter list (# followed by parentheses)
        param_check = content[search_start:search_start+20].strip()
        if param_check.startswith('#'):
            # Skip parameter parentheses
            paren_start = content.find('(', search_start)
            if paren_start == -1:
                return ""
            paren_count = 1
            pos = paren_start + 1
            while pos < len(content) and paren_count > 0:
                if content[pos] == '(':
                    paren_count += 1
                elif content[pos] == ')':
                    paren_count -= 1
                pos += 1
            # Now find the port list after parameter list
            search_start = pos

        # Find port list parentheses
        paren_start = content.find('(', search_start)
        if paren_start == -1:
            return ""

        # Find matching closing parenthesis
        paren_count = 1
        pos = paren_start + 1
        while pos < len(content) and paren_count > 0:
            if content[pos] == '(':
                paren_count += 1
            elif content[pos] == ')':
                paren_count -= 1
            pos += 1

        return content[paren_start:pos]

    def _parse_ports(self, port_section: str):
        """Parse port declarations"""
        # Remove comments and extra whitespace
        port_section = re.sub(r'//.*?\n', '\n', port_section)
        port_section = re.sub(r'/\*.*?\*/', '', port_section, flags=re.DOTALL)

        # Match port declarations (handle multi-line and array syntax)
        # Pattern matches: input/output/inout [optional type] [optional width] signal_name
        port_pattern = r'(input|output|inout)\s+(?:logic|wire|reg)?\s*(?:\[.*?\])?\s*(\w+)(?:\s*,|\s*\))'
        for match in re.finditer(port_pattern, port_section, re.MULTILINE):
            direction = match.group(1)
            signal_name = match.group(2)

            if direction == 'input':
                self.inputs.append(signal_name)
            elif direction == 'output':
                self.outputs.append(signal_name)
            elif direction == 'inout':
                self.inouts.append(signal_name)

    def _parse_internals(self, content: str):
        """Parse internal signals (registers and wires)"""
        # Find module body (after port list)
        module_body_match = re.search(r'\);(.*)endmodule', content, re.DOTALL)
        if not module_body_match:
            return

        body = module_body_match.group(1)

        # Extract registers (always_ff blocks and explicit logic declarations)
        reg_pattern = r'(?:logic|reg)\s+(?:\[.*?\])?\s*(r_\w+)'
        for match in re.finditer(reg_pattern, body):
            signal = match.group(1)
            if signal not in self.internals['registers']:
                self.internals['registers'].append(signal)

        # Extract wires (assign statements and explicit wire declarations)
        wire_pattern = r'(?:wire|logic)\s+(?:\[.*?\])?\s*(w_\w+)'
        for match in re.finditer(wire_pattern, body):
            signal = match.group(1)
            if signal not in self.internals['wires']:
                self.internals['wires'].append(signal)

        # Also find signals in assign statements
        assign_pattern = r'assign\s+(w_\w+)'
        for match in re.finditer(assign_pattern, body):
            signal = match.group(1)
            if signal not in self.internals['wires']:
                self.internals['wires'].append(signal)

class GTKWaveGenerator:
    """Generate GTKWave save file from parsed module"""

    def __init__(self, parser: SVModuleParser):
        self.parser = parser
        self.module_name = parser.module_name

    def generate(self, output_file: str):
        """Generate .gtkw file"""
        with open(output_file, 'w') as f:
            # Header
            f.write('[*]\n')
            f.write('[*] GTKWave Analyzer v3.3.116 (w)1999-2023 BSI\n')
            f.write(f'[*] Generated: {datetime.now().strftime("%a %b %d %H:%M:%S %Y")}\n')
            f.write('[*]\n')
            f.write('[dumpfile] "(null)"\n')
            f.write(f'[savefile] "{output_file}"\n')
            f.write('[timestart] 0\n')
            f.write('[size] 1920 1080\n')
            f.write('[pos] -1 -1\n')
            f.write('*-20.0 0 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1\n')
            f.write('[treeopen] .\n')
            f.write(f'[treeopen] .{self.module_name}.\n')
            f.write('[sst_width] 401\n')
            f.write('[signals_width] 250\n')
            f.write('[sst_expanded] 1\n')
            f.write('[sst_vpaned_height] 400\n')

            # Parameters section
            if self.parser.parameters:
                f.write('@420\n')  # Parameter color
                for param in self.parser.parameters:
                    f.write(f'{self.module_name}.{param}\n')

            # Clock and Reset section
            clk_signals = [s for s in self.parser.inputs if 'clk' in s.lower()]
            rst_signals = [s for s in self.parser.inputs if 'rst' in s.lower() or 'reset' in s.lower()]

            if clk_signals or rst_signals:
                f.write('@200\n')
                f.write('-Clock and Reset\n')
                f.write('@28\n')
                for sig in clk_signals:
                    f.write(f'{self.module_name}.{sig}\n')
                for sig in rst_signals:
                    f.write(f'{self.module_name}.{sig}\n')

            # Inputs section (excluding clk/rst)
            other_inputs = [s for s in self.parser.inputs
                          if 'clk' not in s.lower() and 'rst' not in s.lower() and 'reset' not in s.lower()]
            if other_inputs:
                f.write('@200\n')
                f.write('-Inputs\n')
                f.write('@28\n')
                for sig in other_inputs:
                    f.write(f'{self.module_name}.{sig}\n')

            # Outputs section
            if self.parser.outputs:
                f.write('@200\n')
                f.write('-Outputs\n')
                f.write('@28\n')
                for sig in self.parser.outputs:
                    f.write(f'{self.module_name}.{sig}\n')

            # Inouts section
            if self.parser.inouts:
                f.write('@200\n')
                f.write('-Inouts\n')
                f.write('@28\n')
                for sig in self.parser.inouts:
                    f.write(f'{self.module_name}.{sig}\n')

            # Internal Registers section
            if self.parser.internals['registers']:
                f.write('@200\n')
                f.write('-Internal Registers\n')
                f.write('@28\n')
                for sig in sorted(self.parser.internals['registers']):
                    f.write(f'{self.module_name}.{sig}\n')

            # Internal Wires section
            if self.parser.internals['wires']:
                f.write('@200\n')
                f.write('-Internal Wires\n')
                f.write('@28\n')
                for sig in sorted(self.parser.internals['wires']):
                    f.write(f'{self.module_name}.{sig}\n')

            # Footer
            f.write('[pattern_trace] 1\n')
            f.write('[pattern_trace] 0\n')

        print(f"✅ Generated: {output_file}")

def main():
    parser = argparse.ArgumentParser(description='Generate GTKWave save files for RTL Common Library')
    parser.add_argument('--rtl-dir', default='rtl/common', help='RTL source directory')
    parser.add_argument('--output', default='val/common/GTKW', help='Output directory for .gtkw files')
    parser.add_argument('--force', action='store_true', help='Overwrite existing .gtkw files')
    args = parser.parse_args()

    # Get repository root
    script_dir = Path(__file__).parent
    repo_root = script_dir.parent
    rtl_dir = repo_root / args.rtl_dir
    output_dir = repo_root / args.output

    # Create output directory
    output_dir.mkdir(parents=True, exist_ok=True)

    # Find all SystemVerilog files
    sv_files = sorted(rtl_dir.glob('*.sv'))

    print(f"{'='*70}")
    print(f"GTKWave Save File Generator for RTL Common Library")
    print(f"{'='*70}")
    print(f"RTL Directory: {rtl_dir}")
    print(f"Output Directory: {output_dir}")
    print(f"Found {len(sv_files)} SystemVerilog modules")
    print(f"{'='*70}\n")

    generated_count = 0
    skipped_count = 0
    failed_count = 0

    for sv_file in sv_files:
        module_name = sv_file.stem
        output_file = output_dir / f'{module_name}.gtkw'

        # Skip if file exists and not forcing
        if output_file.exists() and not args.force:
            print(f"⏭️  Skipping: {module_name}.gtkw (already exists)")
            skipped_count += 1
            continue

        # Parse module
        sv_parser = SVModuleParser(str(sv_file))
        if not sv_parser.parse():
            print(f"❌ Failed to parse: {module_name}.sv")
            failed_count += 1
            continue

        # Generate .gtkw file
        gtkw_gen = GTKWaveGenerator(sv_parser)
        try:
            gtkw_gen.generate(str(output_file))
            generated_count += 1
        except Exception as e:
            print(f"❌ Failed to generate {module_name}.gtkw: {e}")
            failed_count += 1

    print(f"\n{'='*70}")
    print(f"Summary:")
    print(f"  Generated: {generated_count}")
    print(f"  Skipped:   {skipped_count}")
    print(f"  Failed:    {failed_count}")
    print(f"  Total:     {len(sv_files)}")
    print(f"{'='*70}")

if __name__ == '__main__':
    main()
