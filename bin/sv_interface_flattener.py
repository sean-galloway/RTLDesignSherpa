#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: Signal
# Purpose: SystemVerilog Interface Flattener - Converts interfaces to logic signals for Ver
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""
SystemVerilog Interface Flattener - Converts interfaces to logic signals for Verilator compatibility
Uses Verible command-line tools for robust SystemVerilog parsing
"""

import argparse
import json
import re
import os
import subprocess
import tempfile
from pathlib import Path
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple


@dataclass
class Signal:
    name: str
    width: str = ""
    direction: str = "logic"  # input, output, inout, logic

    def to_port_string(self) -> str:
        width_str = f" {self.width}" if self.width else ""
        return f"{self.direction} logic{width_str} {self.name}"


@dataclass
class ModPort:
    name: str
    signals: Dict[str, str]  # signal_name -> direction (input/output/inout)


@dataclass
class Interface:
    name: str
    parameters: Dict[str, str]
    signals: Dict[str, Signal]
    modports: Dict[str, ModPort]


class SVInterfaceFlattener:
    def __init__(self, config_file: str):
        with open(config_file, 'r') as f:
            self.config = json.load(f)

        self.interfaces: Dict[str, Interface] = {}
        self.structs: Dict[str, dict] = {}
        self.file_processor = None
        self.verible_path = self._find_verible_syntax()

        # Initialize file processor if file list provided
        if 'file_list' in self.config:
            from file_list_processor import FileListProcessor
            self.file_processor = FileListProcessor([self.config['file_list']])

    def _find_verible_syntax(self) -> str:
        """Find verible-verilog-syntax executable"""
        # Check config first
        verible_path = self.config.get('verible_path', 'verible-verilog-syntax')

        # Test if it's available
        try:
            result = subprocess.run([verible_path, '--help'],
                                  capture_output=True, text=True, timeout=5)
            if result.returncode == 0:
                print(f"Found Verible at: {verible_path}")
                return verible_path
        except (subprocess.TimeoutExpired, FileNotFoundError):
            pass

        # Try common installation paths
        common_paths = [
            'verible-verilog-syntax',
            '/usr/local/bin/verible-verilog-syntax',
            '/usr/bin/verible-verilog-syntax',
            '~/bin/verible-verilog-syntax'
        ]

        for path in common_paths:
            try:
                expanded_path = os.path.expanduser(path)
                result = subprocess.run([expanded_path, '--help'],
                                      capture_output=True, text=True, timeout=5)
                if result.returncode == 0:
                    print(f"Found Verible at: {expanded_path}")
                    return expanded_path
            except (subprocess.TimeoutExpired, FileNotFoundError):
                continue

        print("ERROR: verible-verilog-syntax not found.")
        print("Install Verible from: https://github.com/chipsalliance/verible")
        print("Or specify path in config: {'verible_path': '/path/to/verible-verilog-syntax'}")
        exit(1)

    def smart_parse_dependencies(self, target_file: str):
        """Parse only files that contain interfaces/structs used by target"""
        print(f"Smart parsing dependencies for {target_file}...")

        # Step 1: Extract interface/struct usage from target file
        with open(target_file, 'r') as f:
            target_content = f.read()

        needed_interfaces = self._extract_used_interfaces(target_content)
        needed_structs = self._extract_used_structs(target_content) if not self.config.get('keep_structs', False) else set()

        print(f"Found {len(needed_interfaces)} interfaces needed: {needed_interfaces}")
        print(f"Found {len(needed_structs)} structs needed: {needed_structs}")

        # Step 2: Find which files contain these definitions
        files_to_parse = self._find_definition_files(needed_interfaces, needed_structs)

        print(f"Parsing {len(files_to_parse)} files for definitions...")

        # Step 3: Parse only those files
        for file_path in files_to_parse:
            try:
                self.parse_file(file_path)  # Parse both interfaces and structs in one pass
            except Exception as e:
                print(f"Warning: Could not parse {file_path}: {e}")

    def _extract_used_interfaces(self, content: str) -> set:
        """Find interface names used in module ports and instantiations"""
        used_interfaces = set()

        # Look for interface.modport patterns in module ports
        patterns = [
            r'(\w+)\.(\w+)\s+\w+',      # axi_if.master my_axi
            r'(\w+)\s+\w+\[\]\s*\(',    # axi_if my_bus[]()
            r'(\w+)\s+#.*?\w+\s*\(',    # axi_if #(...) my_bus()
            r'(\w+)\s+\w+\s*\(',        # axi_if my_bus()
        ]

        for pattern in patterns:
            for match in re.finditer(pattern, content):
                intf_name = match.group(1)
                # Skip common SystemVerilog keywords
                if intf_name not in ['input', 'output', 'inout', 'logic', 'wire', 'reg']:
                    used_interfaces.add(intf_name)

        return used_interfaces

    def _extract_used_structs(self, content: str) -> set:
        """Find struct types used in the module"""
        used_structs = set()

        # Look for struct type usage
        patterns = [
            r'(\w+_t)\s+\w+',          # my_struct_t my_var
            r'typedef.*?(\w+)\s*;',    # typedef ... my_type;
        ]

        for pattern in patterns:
            for match in re.finditer(pattern, content):
                struct_name = match.group(1)
                if not struct_name.startswith(('input', 'output', 'logic')):
                    used_structs.add(struct_name)

        return used_structs

    def _find_definition_files(self, interfaces: set, structs: set) -> list:
        """Scan file list to find where interfaces/structs are defined"""
        if not self.file_processor:
            return []

        definition_files = []

        for file_path in self.file_processor.get_file_list():
            if self._file_contains_definitions(file_path, interfaces, structs):
                definition_files.append(file_path)

        return definition_files

    def _file_contains_definitions(self, file_path: str, interfaces: set, structs: set) -> bool:
        """Quick scan to see if file contains needed definitions"""
        try:
            if not os.path.exists(file_path) or not file_path.endswith(('.sv', '.v', '.vh')):
                return False

            with open(file_path, 'r') as f:
                content = f.read()

            # Quick regex check for interface definitions
            for intf in interfaces:
                if re.search(rf'\binterface\s+{intf}\b', content):
                    return True

            # Quick regex check for struct definitions
            for struct in structs:
                if re.search(rf'\btypedef\s+struct.*?\b{struct}\b', content, re.DOTALL):
                    return True

            return False
        except Exception:
            return False  # Skip files that can't be read

    def get_interface_lazy(self, intf_name: str) -> Optional[Interface]:
        """Get interface definition with lazy loading"""
        if intf_name in self.interfaces:
            return self.interfaces[intf_name]

        # Search for the interface definition
        if not self.file_processor:
            return None

        for file_path in self.file_processor.get_file_list():
            if self._file_contains_definitions(file_path, {intf_name}, set()):
                try:
                    self.parse_file(file_path)  # Parse both interfaces and structs
                    if intf_name in self.interfaces:
                        return self.interfaces[intf_name]
                except Exception:
                    continue

        return None

    def parse_all_files(self):
        """Parse interfaces and structs from all files in the file list"""
        if not self.file_processor:
            return

        for file_path in self.file_processor.get_file_list():
            if os.path.exists(file_path) and file_path.endswith(('.sv', '.v')):
                try:
                    self.parse_file(file_path)  # Parse both interfaces and structs in one pass
                except Exception as e:
                    print(f"Warning: Could not parse {file_path}: {e}")

    def parse_file(self, file_path: str):
        """Parse both interfaces and structs from SystemVerilog file using Verible"""
        try:
            # Run verible-verilog-syntax with JSON export
            result = subprocess.run([
                self.verible_path,
                '--export_json',
                file_path
            ], capture_output=True, text=True, timeout=30)

            if result.returncode != 0:
                print(f"Verible parsing failed for {file_path}: {result.stderr}")
                return

            # Parse the JSON AST
            try:
                ast_json = json.loads(result.stdout)
                self._traverse_ast(ast_json, file_path)
            except json.JSONDecodeError as e:
                print(f"Failed to parse Verible JSON output for {file_path}: {e}")

        except subprocess.TimeoutExpired:
            print(f"Verible parsing timed out for {file_path}")
        except Exception as e:
            print(f"Verible parsing error for {file_path}: {e}")

    def parse_interfaces(self, file_path: str):
        """Extract interface definitions from SystemVerilog file using Verible"""
        self.parse_file(file_path)

    def parse_structs(self, file_path: str):
        """Extract struct definitions from SystemVerilog file using Verible"""
        self.parse_file(file_path)

    def _traverse_ast(self, node: dict, file_path: str):
        """Recursively traverse Verible AST JSON to find interfaces and structs"""
        if not isinstance(node, dict):
            return

        node_tag = node.get('tag', '')

        # Check if this node is an interface declaration
        if node_tag == 'kInterfaceDeclaration':
            interface = self._extract_interface_from_json_node(node, file_path)
            if interface:
                self.interfaces[interface.name] = interface
                print(f"Parsed interface: {interface.name} with {len(interface.signals)} signals and {len(interface.modports)} modports")

        # Check if this node is a typedef declaration (for structs)
        elif node_tag == 'kTypedefDeclaration' and not self.config.get('keep_structs', False):
            struct_name, struct_members = self._extract_struct_from_json_node(node, file_path)
            if struct_name and struct_members:
                self.structs[struct_name] = struct_members
                print(f"Parsed struct: {struct_name} with {len(struct_members)} members")

        # Recursively check children
        if 'children' in node:
            for child in node['children']:
                if child is not None:
                    self._traverse_ast(child, file_path)

    def _extract_interface_from_json_node(self, interface_node: dict, file_path: str) -> Optional[Interface]:
        """Extract interface details from a Verible JSON AST interface node"""
        interface_name = None
        parameters = {}
        signals = {}
        modports = {}

        if 'children' not in interface_node:
            return None

        # Extract interface name and components
        for child in interface_node['children']:
            if child is None:
                continue

            child_tag = child.get('tag', '')

            if child_tag == 'kInterfaceHeader':
                interface_name, parameters = self._parse_interface_header_json(child)
            elif child_tag == 'kInterfaceItemList':
                signals, modports = self._parse_interface_items_json(child)

        if interface_name:
            return Interface(
                name=interface_name,
                parameters=parameters,
                signals=signals,
                modports=modports
            )
        return None

    def _parse_interface_header_json(self, header_node: dict) -> Tuple[str, Dict[str, str]]:
        """Parse interface header from JSON for name and parameters"""
        name = None
        parameters = {}

        if 'children' not in header_node:
            return name, parameters

        for child in header_node['children']:
            if child is None:
                continue

            child_tag = child.get('tag', '')

            if child_tag == 'SymbolIdentifier':
                name = child.get('text', '').strip()
            elif child_tag == 'kParameterDeclarationList':
                parameters = self._parse_parameter_list_json(child)

        return name, parameters

    def _parse_interface_items_json(self, items_node: dict) -> Tuple[Dict[str, Signal], Dict[str, ModPort]]:
        """Parse interface items from JSON for signals and modports"""
        signals = {}
        modports = {}

        if 'children' not in items_node:
            return signals, modports

        for child in items_node['children']:
            if child is None:
                continue

            child_tag = child.get('tag', '')

            if child_tag == 'kDataDeclaration':
                new_signals = self._parse_data_declaration_json(child)
                signals.update(new_signals)
            elif child_tag == 'kModportDeclaration':
                modport = self._parse_modport_declaration_json(child)
                if modport:
                    modports[modport.name] = modport

        return signals, modports

    def _parse_data_declaration_json(self, data_node: dict) -> Dict[str, Signal]:
        """Parse signal declarations from JSON"""
        signals = {}

        if 'children' not in data_node:
            return signals

        data_type = "logic"
        width = ""
        signal_names = []

        # Extract type and signal names
        for child in data_node['children']:
            if child is None:
                continue

            child_tag = child.get('tag', '')

            if child_tag == 'kDataType':
                data_type, width = self._parse_data_type_json(child)
            elif child_tag == 'kVariableDeclarationAssignmentList':
                signal_names = self._parse_variable_list_json(child)

        # Create Signal objects
        for name in signal_names:
            signals[name] = Signal(
                name=name,
                width=width,
                direction="logic"
            )

        return signals

    def _parse_data_type_json(self, type_node: dict) -> Tuple[str, str]:
        """Parse data type from JSON to extract type and width"""
        data_type = "logic"
        width = ""

        if 'children' not in type_node:
            return data_type, width

        # Look for packed dimensions [31:0]
        for child in type_node['children']:
            if child is None:
                continue

            if child.get('tag') == 'kPackedDimensionList':
                width = self._extract_width_from_dimensions_json(child)

        return data_type, width

    def _extract_width_from_dimensions_json(self, dim_node: dict) -> str:
        """Extract width like [31:0] from packed dimensions JSON"""
        # This extracts the text representation of the dimension
        return self._extract_text_from_node(dim_node)

    def _parse_variable_list_json(self, var_list_node: dict) -> List[str]:
        """Parse list of variable names from JSON"""
        names = []

        if 'children' not in var_list_node:
            return names

        for child in var_list_node['children']:
            if child is None:
                continue

            if child.get('tag') == 'SymbolIdentifier':
                name = child.get('text', '').strip()
                if name:
                    names.append(name)

        return names

    def _parse_modport_declaration_json(self, modport_node: dict) -> Optional[ModPort]:
        """Parse modport declaration from JSON"""
        modport_name = None
        signal_directions = {}

        if 'children' not in modport_node:
            return None

        for child in modport_node['children']:
            if child is None:
                continue

            child_tag = child.get('tag', '')

            if child_tag == 'SymbolIdentifier':
                modport_name = child.get('text', '').strip()
            elif child_tag == 'kModportItemList':
                signal_directions = self._parse_modport_items_json(child)

        if modport_name:
            return ModPort(name=modport_name, signals=signal_directions)
        return None

    def _parse_modport_items_json(self, items_node: dict) -> Dict[str, str]:
        """Parse modport items from JSON for signal directions"""
        signal_directions = {}

        # Extract text and parse for direction keywords
        text = self._extract_text_from_node(items_node)

        # Simple parsing for "input signal1, signal2, output signal3"
        current_direction = None
        for word in text.split():
            word = word.strip(',();')
            if word in ['input', 'output', 'inout']:
                current_direction = word
            elif current_direction and word and word not in [',', '(', ')']:
                signal_directions[word] = current_direction

        return signal_directions

    def _parse_parameter_list_json(self, param_list_node: dict) -> Dict[str, str]:
        """Parse parameter list from JSON"""
        parameters = {}

        # Extract text and parse for parameter assignments
        text = self._extract_text_from_node(param_list_node)

        # Look for parameter assignments like "parameter int WIDTH = 32"
        for match in re.finditer(r'parameter\s+\w*\s*(\w+)\s*=\s*([^,)]+)', text):
            param_name = match.group(1)
            param_value = match.group(2).strip()
            parameters[param_name] = param_value

        return parameters

    def _extract_text_from_node(self, node: dict) -> str:
        """Recursively extract all text from a JSON AST node"""
        if isinstance(node, dict):
            text = node.get('text', '')
            if 'children' in node:
                for child in node['children']:
                    if child is not None:
                        text += ' ' + self._extract_text_from_node(child)
            return text
        elif isinstance(node, str):
            return node
        else:
            return ''

    def _extract_struct_from_json_node(self, typedef_node: dict, file_path: str) -> Tuple[Optional[str], Dict[str, str]]:
        """Extract struct definition from typedef JSON AST node"""
        struct_name = None
        members = {}

        if 'children' not in typedef_node:
            return None, {}

        # Look for struct definition and name
        for child in typedef_node['children']:
            if child is None:
                continue

            child_tag = child.get('tag', '')

            if child_tag == 'kDataType':
                members = self._parse_struct_members_json(child)
            elif child_tag == 'SymbolIdentifier':
                struct_name = child.get('text', '').strip()

        return struct_name, members

    def _parse_struct_members_json(self, data_type_node: dict) -> Dict[str, str]:
        """Parse struct members from data type JSON node"""
        members = {}

        if 'children' not in data_type_node:
            return members

        # Look for struct body
        for child in data_type_node['children']:
            if child is None:
                continue

            if child.get('tag') == 'kStructType':
                members = self._parse_struct_body_json(child)
                break

        return members

    def _parse_struct_body_json(self, struct_node: dict) -> Dict[str, str]:
        """Parse struct body from JSON to extract member signals"""
        members = {}

        if 'children' not in struct_node:
            return members

        for child in struct_node['children']:
            if child is None:
                continue

            child_tag = child.get('tag', '')

            if child_tag == 'kStructMemberList':
                members = self._parse_struct_member_list_json(child)
                break

        return members

    def _parse_struct_member_list_json(self, member_list_node: dict) -> Dict[str, str]:
        """Parse struct member list from JSON"""
        members = {}

        if 'children' not in member_list_node:
            return members

        for child in member_list_node['children']:
            if child is None:
                continue

            child_tag = child.get('tag', '')

            if child_tag == 'kDataDeclaration':
                # Parse each data declaration in the struct
                new_members = self._parse_struct_data_declaration_json(child)
                members.update(new_members)

        return members

    def _parse_struct_data_declaration_json(self, data_decl_node: dict) -> Dict[str, str]:
        """Parse individual data declaration within struct"""
        members = {}

        if 'children' not in data_decl_node:
            return members

        width = ""
        member_names = []

        for child in data_decl_node['children']:
            if child is None:
                continue

            child_tag = child.get('tag', '')

            if child_tag == 'kDataType':
                _, width = self._parse_data_type_json(child)
            elif child_tag == 'kVariableDeclarationAssignmentList':
                member_names = self._parse_variable_list_json(child)

        # Create member entries
        for name in member_names:
            members[name] = width

        return members

    def generate_wrapper(self, input_file: str, output_file: str, wrapper_name: str = None):
        """Generate flattened wrapper module"""
        with open(input_file, 'r') as f:
            content = f.read()

        # Parse the target module
        module_match = re.search(r'module\s+(\w+)\s*(?:#\s*\((.*?)\))?\s*\((.*?)\)\s*;', content, re.DOTALL)
        if not module_match:
            raise ValueError("Could not find module definition")

        module_name = module_match.group(1)
        module_params = module_match.group(2) or ""
        module_ports = module_match.group(3) or ""

        # Generate wrapper
        if not wrapper_name:
            wrapper_name = f"{module_name}_flat"
        wrapper_content = self._generate_wrapper_content(
            wrapper_name, module_name, module_params, module_ports, content
        )

        with open(output_file, 'w') as f:
            f.write(wrapper_content)

    def _generate_wrapper_content(self, wrapper_name: str, orig_module: str,
                                  params: str, ports: str, orig_content: str) -> str:
        """Generate the actual wrapper module content"""

        # Parse interface ports from original module
        interface_ports = self._extract_interface_ports(ports)
        flat_ports = []
        instance_connections = []
        internal_signals = []

        # Process each interface port
        for port_info in interface_ports:
            intf_name = port_info['interface']
            inst_name = port_info['instance']
            modport = port_info.get('modport', 'master')  # default to master

            if intf_name in self.interfaces:
                intf = self.interfaces[intf_name]
                prefix = self._get_signal_prefix(inst_name, intf_name, modport)

                # Generate flattened signals
                for sig_name, signal in intf.signals.items():
                    direction = self._get_signal_direction(sig_name, intf, modport)
                    flat_name = f"{prefix}_{sig_name}"

                    flat_ports.append(f"    {direction} logic{signal.width} {flat_name}")
                    instance_connections.append(f"        .{inst_name}_{sig_name}({flat_name})")
            else:
                print(f"Warning: Interface {intf_name} not found in parsed interfaces")

        # Add non-interface ports as-is
        regular_ports = self._extract_regular_ports(ports)
        flat_ports.extend([f"    {port}" for port in regular_ports])

        # Build wrapper
        wrapper = f"""// Auto-generated wrapper for Verilator compatibility
// Generated by SystemVerilog Interface Flattener using Verible parser
`timescale 1ns / 1ps

module {wrapper_name}
"""

        if params:
            wrapper += f"#(\n    {params}\n)\n"

        wrapper += "(\n"
        wrapper += ",\n".join(flat_ports)
        wrapper += "\n);\n\n"

        # Add internal interface instances if needed
        for internal in internal_signals:
            wrapper += f"    {internal}\n"

        wrapper += f"\n    // Instance of original module\n"
        wrapper += f"    {orig_module}"
        if params:
            wrapper += f" #({params})"
        wrapper += f" u_{orig_module} (\n"
        wrapper += ",\n".join(instance_connections)
        wrapper += "\n    );\n\n"
        wrapper += "endmodule\n"

        return wrapper

    def _extract_interface_ports(self, ports_str: str) -> List[dict]:
        """Extract interface port declarations"""
        interface_ports = []

        # Look for interface.modport patterns
        pattern = r'(\w+)\.(\w+)\s+(\w+)'
        for match in re.finditer(pattern, ports_str):
            interface_ports.append({
                'interface': match.group(1),
                'modport': match.group(2),
                'instance': match.group(3)
            })

        return interface_ports

    def _extract_regular_ports(self, ports_str: str) -> List[str]:
        """Extract non-interface port declarations"""
        regular_ports = []

        # Remove interface ports and extract the rest
        lines = ports_str.split('\n')
        for line in lines:
            line = line.strip()
            if line and not re.search(r'\w+\.\w+\s+\w+', line):
                # This is a regular port
                regular_ports.append(line.rstrip(','))

        return regular_ports

    def _get_signal_prefix(self, instance: str, interface: str, modport: str) -> str:
        """Generate signal prefix based on naming convention"""
        convention = self.config.get('naming_convention', 'amba')

        if convention == 'amba':
            # Use modport-based naming: m_axi_, s_axi_
            prefix_map = {
                'master': 'm',
                'slave': 's',
                'initiator': 'm',
                'target': 's'
            }
            role = prefix_map.get(modport, 'm')
            return f"{role}_{interface}"
        elif convention == 'instance':
            return instance
        elif convention == 'hierarchical':
            return f"{interface}_{modport}"
        else:
            return instance

    def _get_signal_direction(self, signal_name: str, interface: Interface, modport_name: str) -> str:
        """Determine signal direction based on modport"""
        if modport_name in interface.modports:
            modport = interface.modports[modport_name]
            if signal_name in modport.signals:
                direction = modport.signals[signal_name]
                return 'input' if direction == 'input' else 'output'

        # Default fallback
        return 'input'


def main():
    parser = argparse.ArgumentParser(description='Flatten SystemVerilog interfaces for Verilator')
    parser.add_argument('config', help='JSON configuration file')
    parser.add_argument('--input', help='Input SystemVerilog file (overrides config)')
    parser.add_argument('--output', help='Output file (overrides config)')
    parser.add_argument('--wrapper-name', help='Wrapper module name (overrides config)')

    args = parser.parse_args()

    flattener = SVInterfaceFlattener(args.config)

    # Get target info from config or command line
    target_config = flattener.config.get('target', {})
    input_file = args.input or target_config.get('input_file')
    output_file = args.output or target_config.get('output_file')
    wrapper_name = args.wrapper_name or target_config.get('wrapper_module_name')

    if not input_file:
        raise ValueError("No input file specified in config or command line")

    if not output_file:
        output_file = Path(input_file).stem + '_flat.sv'

    if not wrapper_name:
        wrapper_name = Path(input_file).stem + '_flat'

    # Parse based on strategy
    strategy = flattener.config.get('parsing_strategy', 'smart')
    if strategy == 'smart':
        flattener.smart_parse_dependencies(input_file)
    elif strategy == 'lazy':
        pass  # Parse on-demand during generation
    else:  # 'all'
        flattener.parse_all_files()

    flattener.generate_wrapper(input_file, output_file, wrapper_name)

    print(f"Generated flattened wrapper: {output_file}")
    print(f"Wrapper module name: {wrapper_name}")


if __name__ == "__main__":
    main()
