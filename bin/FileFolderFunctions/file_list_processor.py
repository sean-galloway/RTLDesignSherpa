# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FileListProcessor
# Purpose: Processes existing file lists to create a single one
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""Processes existing file lists to create a single one"""

import os
import re


def remove_dups_from_list(my_list):
    return list(dict.fromkeys(my_list))


class FileListProcessor:
    # Define the strings list for various filters
    exclude_strings = ["SC_IP", "TSMC", "MPPHY_DIR", "PCIE_CC_DIR", "NDS_HOME", 
                        "PVT_IP", "CML", "tm16ff", "DIVTS", "sc9m"]
    verilog_strings = [".sv", ".v", ".vg", ".vh"]
    vhdl_strings = [".vhd"]


    def __init__(self, filelist=None, debug=False):
        self.file_list = []
        self.file_list_no_repl = []
        self.file_list_no_repl_syn = []
        self.file_list_no_repl_syn_verilog = []
        self.file_list_no_repl_syn_vhdl = []
        self.includes = []
        self.plus_define = []
        self.debug_file = None
        if filelist is not None:
            for file in filelist:
                self._process_file(file, tab=0, debug=debug)


    def replace_curly_braces(self, text):
        # This regular expression will match patterns like ${VARNAME}
        pattern = r'\$\{(\w+)\}'
        return re.sub(pattern, r'$\1', text)


    def _process_file(self, filename, tab=0, debug=False):
        if debug and self.debug_file is None:
            self.debug_file = open('debug_process_file.txt', 'w')

        def debug_print(message):
            if debug:
                print(message, file=self.debug_file)

        debug_print('    '*tab + f'---------->{filename=}')

        with open(filename, 'r') as file:
            for line in file:
                line = line.strip()
                # remove the curly braces
                line = self.replace_curly_braces(line)
                # Remove comments starting with #
                line = re.sub(r'\s*#.*', '', line)
                # Remove comments starting with //
                line = re.sub(r'\s*//.*', '', line)
                # Ignore blank lines and comments
                if not line or line.startswith('#') or line.startswith('//'):
                    continue
                # Handle +define+ lines
                if match := re.match(r'^\s*\+define\+(\S+)', line):
                    plus_define = match[1]
                    debug_print('defn' + '    '*tab + f'{line=}')
                    self.plus_define.append(plus_define)
                    continue
                # Special case for [ list ... ] with optional leading spaces
                if re.match(r'^\s*\[ list', line):
                    debug_print('list' + '    '*tab + f'{line=}')
                    self._process_list(line)
                    continue
                # Store the include dirs to be used in the command line
                if match := re.match(r'^\s*\+incdir\+\s*(.*)', line):
                    include = match[1]
                    debug_print('incl' + '    '*tab + f'{line=}')
                    self.includes.append(include)
                    continue
                # Replace environment variables
                line_no_repl = line
                line = self._replace_env_variables(line)
                if match := re.match(r'^\s*\-f\s+(\S+)', line):
                    included_file = match[1]
                    debug_print('file' + '    '*tab + f'{included_file=}')
                    self._process_file(included_file, tab=tab+1, debug=debug)
                else:
                    self.file_list.append(line)
                    self.file_list_no_repl.append(line_no_repl)

        # Create a new list that includes only items not in the exclude list
        for item in self.file_list_no_repl:
            # Check if any of the exclude_= strings are a substring of the current item
            excl_found = False
            for exclude in self.exclude_strings:
                if exclude in item:
                    excl_found = True
                    debug_print(f'Excluding {item}')
                    break
            if not excl_found:
                self.file_list_no_repl_syn.append(item)

        # Create a list of the verilog files
        for item in self.file_list_no_repl_syn:
            # Check if any of the include strings are a substring of the current item
            if any(include in item for include in self.verilog_strings) and not item.endswith(".vhd"):
                self.file_list_no_repl_syn_verilog.append(item)
            # Check for exact matches with VHDL extensions
            elif any(item.endswith(ext) for ext in self.vhdl_strings):
                self.file_list_no_repl_syn_vhdl.append(item)

        if debug and tab == 0 and self.debug_file is not None:
            print('Full List:', file=self.debug_file)
            for file in self.file_list_no_repl:
                print(f'Full--> {file}', file=self.debug_file)

        if debug and tab == 0 and self.debug_file is not None:
            print('\nfile list no repl vhdl:', file=self.debug_file)
            for file in self.file_list_no_repl_syn_vhdl:
                print(f'    {file}', file=self.debug_file)

            print('\ninclude_file list:', file=self.debug_file)
            for file in self.includes:
                print(f'    {file}', file=self.debug_file)

            self.debug_file.close()
            self.debug_file = None


    def _process_list(self, line):
        # Remove [ list and ] \
        line = re.sub(r'^\s*\[ list', '', line).rstrip('] \\').strip()
        # Split by whitespace and process each part
        parts = line.split()
        for part in parts:
            # Store the include dirs to be used in the command line
            if match := re.match(r'^\+incdir\+\s*(.*)', part):
                include = match[1]
                self.includes.append(include)
            else:
                # Replace environment variables
                part_no_repl = part
                part = self._replace_env_variables(part)
                self.file_list.append(part)
                self.file_list_no_repl.append(part_no_repl)


    def _replace_env_variables(self, line):
        # Regex to find $VARNAME patterns
        return re.sub(r'\$(\w+)', lambda match: os.getenv(match.group(1), match.group(0)), line)


    def get_file_list(self):
        return remove_dups_from_list(self.file_list)


    def get_include_list(self):
        return remove_dups_from_list(self.includes)


    def get_plus_define_list(self):
        return remove_dups_from_list(self.plus_define)


    def write_filelist(self, filename):
        verilog_fn = f'{filename}_verilog.f'
        vhdl_fn = f'{filename}_vhdl.f'
        with open(verilog_fn, 'w') as file:
            self._write_verilog_filelist(file)
        with open(vhdl_fn, 'w') as file:
            self._write_vhdl_filelist(file)


    def _write_verilog_filelist(self, file):
        print('#############################################################', file=file)
        print('# filelist created by FileListProcessor', file=file)
        print('#############################################################', file=file)
        message = ''.join(
            f'+define+{define}\n'
            for define in remove_dups_from_list(self.plus_define)
        )
        for include in remove_dups_from_list(self.includes):
            message += f'+incdir+{include}\n'
        for filename in remove_dups_from_list(self.file_list_no_repl_syn_verilog):
            message += f'{filename}\n'
        print(message, file=file)


    def _write_vhdl_filelist(self, file):
        print('#############################################################', file=file)
        print('# filelist created by FileListProcessor', file=file)
        print('#############################################################', file=file)
        message = ''.join(
            f'+define+{define}\n'
            for define in remove_dups_from_list(self.plus_define)
        )
        for include in remove_dups_from_list(self.includes):
            message += f'+incdir+{include}\n'
        print(message, file=file)
        for filename in remove_dups_from_list(self.file_list_no_repl_syn_vhdl):
            message += f'{filename}\n'
        print(message, file=file)


    def write_synth_filelist(self, filename):
        with open(filename, 'w') as file:
            self._write_synth_filelist(file)


    def _write_synth_filelist(self, file):
        print('#############################################################', file=file)
        print('# Synthesis filelist created by FileListProcessor', file=file)
        print('#############################################################', file=file)
        # Verilog portion
        print('analyze -format sverilog -library WORK  -vcs \\', file=file)
        message = '    [ list  '
        for define in remove_dups_from_list(self.plus_define):
            message += f'+define+{define} '
        for include in remove_dups_from_list(self.includes):
            message += f'+incdir+{include} '
        message += '] \\ \n'
        message = '    [list \\ \n'
        for filename in remove_dups_from_list(self.file_list_no_repl_syn_verilog):
            message += f'    "{filename}" \\ \n'
        message += '    ]\n'
        print(message, file=file)
        # vhdl portion
        print('analyze -format vhdl -library WORK  -vcs \\', file=file)
        message = '    [ list  '
        for define in remove_dups_from_list(self.plus_define):
            message += f'+define+{define} '
        for include in remove_dups_from_list(self.includes):
            message += f'+incdir+{include} '
        message += '] \\ \n'
        print(message, file=file)
        message = '    [list \\ \n'
        for filename in remove_dups_from_list(self.file_list_no_repl_syn_vhdl):
            message += f'    "{filename}" \\ \n'
        message += '    ]\n'
        print(message, file=file)


# Example usage
# if __name__ == "__main__":
#     processor = FileListProcessor('top_level_file_list.f')
#     all_files = processor.get_file_list()
#     for file in all_files:
#         print(file)
#     all_includes = processor.get_include_list()
#     for inc in all_includes:
#         print(inc)

