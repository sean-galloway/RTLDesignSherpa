#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: update_fst_tracing
# Purpose: Detect the indentation style used in the file
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

import os
import re
import argparse
from pathlib import Path

def detect_indentation(content):
    """Detect the indentation style used in the file"""
    # Find lines with indentation
    indent_pattern = re.compile(r'^(\s+)[^\s]')
    indents = []
    
    for line in content.splitlines():
        match = indent_pattern.match(line)
        if match:
            indents.append(match.group(1))
    
    if not indents:
        return "    "  # Default to 4 spaces
    
    # Find the most common indent
    indent_counts = {}
    for indent in indents:
        if len(indent) > 0:  # Skip empty indents
            indent_counts[indent] = indent_counts.get(indent, 0) + 1
    
    if not indent_counts:
        return "    "  # Default to 4 spaces
        
    most_common_indent = max(indent_counts, key=indent_counts.get)
    return most_common_indent

def get_item_indentation(lines, start_pattern):
    """Get the indentation used for items in a collection"""
    # Find the first line matching the pattern
    for i, line in enumerate(lines):
        if start_pattern in line:
            # If this is the start of a dictionary or list, check the next line
            if i + 1 < len(lines):
                # Get the indentation of the next line
                indent_match = re.match(r'^(\s+)', lines[i+1])
                if indent_match:
                    return indent_match.group(1)
    return "    "  # Default to 4 spaces

def update_test_file(file_path):
    with open(file_path, 'r') as f:
        content = f.read()
    
    original_content = content
    
    # Detect indentation style
    indent = detect_indentation(content)
    
    # Check if file already has FST tracing additions
    if 'compile_args' in content and '--trace-fst' in content:
        print(f"File {file_path} already updated for FST tracing, skipping...")
        return False
    
    # Split the file into lines for more precise editing
    lines = content.splitlines()
    
    # Find extra_env dictionary
    extra_env_start_line = -1
    extra_env_indent = ""
    extra_env_item_indent = ""
    
    for i, line in enumerate(lines):
        if re.match(r'\s*extra_env\s*=\s*\{', line):
            extra_env_start_line = i
            extra_env_indent = re.match(r'(\s*)', line).group(1)
            break
    
    if extra_env_start_line != -1:
        # Find the indentation used for items in extra_env
        extra_env_item_indent = get_item_indentation(lines, "extra_env = {")
        
        # Check if extra_env contains TRACE_FILE already
        has_trace_file = False
        for j in range(extra_env_start_line, min(extra_env_start_line + 15, len(lines))):
            if 'TRACE_FILE' in lines[j]:
                has_trace_file = True
                break
        
        if not has_trace_file:
            # Find where to insert our new entries
            insert_line = extra_env_start_line
            opening_brace_pos = lines[insert_line].find('{')
            
            if opening_brace_pos >= 0:
                # If opening brace is not at end of line, content follows it
                if opening_brace_pos < len(lines[insert_line]) - 1 and lines[insert_line][opening_brace_pos+1:].strip():
                    # The brace is not the last character on the line
                    # Split the line at the opening brace
                    prefix = lines[insert_line][:opening_brace_pos + 1]
                    suffix = lines[insert_line][opening_brace_pos + 1:]
                    
                    # Replace the original line and add new lines
                    lines[insert_line] = prefix
                    lines.insert(insert_line + 1, f"{extra_env_item_indent}'TRACE_FILE': f\"{{sim_build}}/dump.fst\",")
                    lines.insert(insert_line + 2, f"{extra_env_item_indent}'VERILATOR_TRACE': '1',  # Enable tracing")
                    
                    # Add the content that followed the opening brace
                    if suffix.strip():
                        lines.insert(insert_line + 3, f"{extra_env_item_indent}{suffix.lstrip()}")
                else:
                    # Opening brace is the last character on the line, add new lines after it
                    lines.insert(insert_line + 1, f"{extra_env_item_indent}'TRACE_FILE': f\"{{sim_build}}/dump.fst\",")
                    lines.insert(insert_line + 2, f"{extra_env_item_indent}'VERILATOR_TRACE': '1',  # Enable tracing")
    
    # Find where to insert compile_args, sim_args, and plusargs
    run_line = -1
    cmd_filename_line = -1
    
    for i, line in enumerate(lines):
        if 'run(' in line and not line.strip().startswith('#'):
            run_line = i
            break
        if 'cmd_filename =' in line:
            cmd_filename_line = i
            break
    
    insertion_line = cmd_filename_line if cmd_filename_line != -1 else run_line
    if insertion_line != -1:
        insertion_indent = re.match(r'(\s*)', lines[insertion_line]).group(1)
        
        # Only insert if compile_args doesn't already exist
        has_compile_args = False
        for i in range(max(0, insertion_line-10), insertion_line):
            if 'compile_args' in lines[i]:
                has_compile_args = True
                break
                
        if not has_compile_args:
            # Determine indentation for array items
            item_indent = insertion_indent + indent
            
            # Create the compile_args, sim_args, and plusargs blocks with consistent spacing
            compile_args_block = [
                f"{insertion_indent}compile_args = [",
                f"{item_indent}\"--trace-fst\",",
                f"{item_indent}\"--trace-structs\",",
                f"{item_indent}\"--trace-depth\", \"99\",",
                f"{insertion_indent}]"
            ]
            
            # Check if sim_args already exists
            has_sim_args = False
            for i in range(max(0, insertion_line-10), insertion_line):
                if 'sim_args' in lines[i]:
                    has_sim_args = True
                    break
                    
            if not has_sim_args:
                sim_args_block = [
                    "",  # Empty line for better readability
                    f"{insertion_indent}sim_args = [",
                    f"{item_indent}\"--trace-fst\",  # Tell Verilator to use FST",
                    f"{item_indent}\"--trace-structs\",",
                    f"{item_indent}\"--trace-depth\", \"99\",",
                    f"{insertion_indent}]"
                ]
                compile_args_block.extend(sim_args_block)
            
            # Check if plusargs already exists
            has_plusargs = False
            for i in range(max(0, insertion_line-10), insertion_line):
                if 'plusargs' in lines[i]:
                    has_plusargs = True
                    break
                    
            if not has_plusargs:
                plusargs_block = [
                    "",  # Empty line for better readability
                    f"{insertion_indent}plusargs = [",
                    f"{item_indent}\"+trace\",",
                    f"{insertion_indent}]"
                ]
                compile_args_block.extend(plusargs_block)
            
            # Insert the blocks with an empty line before and after
            lines[insertion_line:insertion_line] = [""] + compile_args_block + [""]
    
    # Update the run() function call
    in_run_call = False
    run_start_line = -1
    run_end_line = -1
    run_indent = ""
    run_item_indent = ""
    
    for i, line in enumerate(lines):
        # Skip comments
        if line.strip().startswith('#'):
            continue
            
        if 'run(' in line and not in_run_call:
            in_run_call = True
            run_start_line = i
            run_indent = re.match(r'(\s*)', line).group(1)
            
            # If there are arguments on subsequent lines, determine their indentation
            if i + 1 < len(lines) and ')' not in line:
                run_item_match = re.match(r'^(\s+)', lines[i+1])
                if run_item_match:
                    run_item_indent = run_item_match.group(1)
                else:
                    run_item_indent = run_indent + indent
            else:
                run_item_indent = run_indent + indent
        
        if in_run_call and ')' in line:
            run_end_line = i
            break
    
    if run_start_line != -1 and run_end_line != -1:
        # Extract the run call arguments
        run_args = []
        for i in range(run_start_line, run_end_line + 1):
            run_args.append(lines[i])
        
        run_args_text = '\n'.join(run_args)
        
        # Check if the required arguments are already present
        has_compile_args = 'compile_args=' in run_args_text or 'compile_args =' in run_args_text
        has_sim_args = 'sim_args=' in run_args_text or 'sim_args =' in run_args_text
        has_plusargs = 'plusargs=' in run_args_text or 'plusargs =' in run_args_text
        
        # Update waves parameter
        waves_pattern = re.compile(r'waves\s*=\s*False')
        
        # Check if any line contains waves=False
        has_waves_false = False
        for i in range(run_start_line, run_end_line + 1):
            if waves_pattern.search(lines[i]):
                has_waves_false = True
                lines[i] = waves_pattern.sub('waves=True', lines[i])
        
        # Check if waves is already set to True
        has_waves_true = False
        for i in range(run_start_line, run_end_line + 1):
            if 'waves=True' in lines[i] or 'waves = True' in lines[i]:
                has_waves_true = True
        
        # Add missing arguments before the closing parenthesis
        missing_args = []
        if not has_compile_args:
            missing_args.append(f"{run_item_indent}compile_args=compile_args,")
        if not has_sim_args:
            missing_args.append(f"{run_item_indent}sim_args=sim_args,")
        if not has_plusargs:
            missing_args.append(f"{run_item_indent}plusargs=plusargs,")
        if not has_waves_true and not has_waves_false:
            missing_args.append(f"{run_item_indent}waves=True,")
        
        if missing_args:
            # Find the position to insert the missing arguments
            if run_end_line > run_start_line:
                # The run call spans multiple lines
                # Ensure the line before has a comma
                prev_line = lines[run_end_line - 1].rstrip()
                if prev_line and not prev_line.endswith(','):
                    if '=' in prev_line:  # Only add comma if it's a parameter
                        lines[run_end_line - 1] = prev_line + ','
                
                # Find the closing parenthesis
                closing_line = run_end_line
                closing_text = lines[closing_line]
                closing_pos = closing_text.find(')')
                
                if closing_pos > 0 and closing_text[:closing_pos].strip():
                    # There's content before the closing parenthesis
                    lines[run_end_line:run_end_line] = missing_args
                else:
                    # Insert before the closing parenthesis
                    lines[run_end_line:run_end_line] = missing_args
            else:
                # It's a single-line run call - need to split it
                run_line = lines[run_start_line]
                opening_pos = run_line.find('run(')
                closing_pos = run_line.rfind(')')
                
                prefix = run_line[:opening_pos + 4]  # Include 'run('
                args = run_line[opening_pos + 4:closing_pos]
                suffix = run_line[closing_pos:]
                
                # If there are existing args, add a comma
                if args.strip():
                    new_args = args + ','
                else:
                    new_args = args
                
                # Build the new run call
                new_lines = [prefix + new_args]
                new_lines.extend(missing_args)
                new_lines.append(run_indent + suffix)
                
                lines[run_start_line:run_start_line + 1] = new_lines
    
    # Reconstruct the file content
    new_content = '\n'.join(lines)
    
    # Only write the file if changes were made
    if new_content != original_content:
        with open(file_path, 'w') as f:
            f.write(new_content)
        print(f"Updated {file_path} for FST tracing")
        return True
    else:
        print(f"No changes needed for {file_path}")
        return False

def main():
    parser = argparse.ArgumentParser(description='Update Cocotb tests to enable FST tracing with Verilator')
    parser.add_argument('directory', help='Directory containing test files to update')
    parser.add_argument('--pattern', default='test_*.py', help='Filename pattern to match (default: test_*.py)')
    parser.add_argument('--dry-run', action='store_true', help='Print what would be done without making changes')
    args = parser.parse_args()
    
    # Find all matching test files
    directory = Path(args.directory)
    files = list(directory.glob(f"**/{args.pattern}"))
    
    if not files:
        print(f"No files matching {args.pattern} found in {directory}")
        return
    
    print(f"Found {len(files)} test files to process")
    
    updated_files = 0
    for file_path in files:
        print(f"Processing {file_path}...")
        
        if args.dry_run:
            print(f"[DRY RUN] Would update {file_path}")
        else:
            if update_test_file(file_path):
                updated_files += 1
    
    print(f"Updated {updated_files} test files")

if __name__ == '__main__':
    main()
