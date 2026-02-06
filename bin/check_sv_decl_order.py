#!/usr/bin/env python3
"""
check_sv_decl_order.py - Check SystemVerilog signals are declared before use

This script parses SystemVerilog files and warns when a signal is used
before it is declared. While SystemVerilog allows forward references,
this coding style makes code harder to read and debug.

Usage:
    check_sv_decl_order.py <file1.sv> [file2.sv ...]
    check_sv_decl_order.py --all          # Check all .sv files in src/rtl
    check_sv_decl_order.py --staged       # Check staged .sv files (for pre-commit)

Exit codes:
    0 - No issues found
    1 - Issues found (signals used before declaration)
    2 - Error (file not found, parse error, etc.)
"""

import argparse
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple


@dataclass
class SignalInfo:
    """Information about a signal."""
    name: str
    decl_line: int
    first_use_line: Optional[int] = None


@dataclass
class Issue:
    """A declaration order issue."""
    file: str
    signal: str
    use_line: int
    decl_line: int


def strip_comments(content: str) -> str:
    """Remove comments from SystemVerilog content."""
    # Remove single-line comments
    content = re.sub(r'//.*$', '', content, flags=re.MULTILINE)
    # Remove multi-line comments
    content = re.sub(r'/\*.*?\*/', '', content, flags=re.DOTALL)
    return content


def strip_strings(content: str) -> str:
    """Remove string literals from content."""
    return re.sub(r'"[^"]*"', '""', content)


def get_module_boundaries(content: str) -> List[Tuple[int, int, str]]:
    """Find module/endmodule boundaries. Returns list of (start_line, end_line, module_name)."""
    modules = []
    lines = content.split('\n')

    module_start = None
    module_name = None

    for i, line in enumerate(lines, 1):
        # Match module declaration
        match = re.match(r'\s*module\s+(\w+)', line)
        if match:
            module_start = i
            module_name = match.group(1)

        # Match endmodule
        if re.match(r'\s*endmodule', line):
            if module_start is not None:
                modules.append((module_start, i, module_name))
                module_start = None
                module_name = None

    return modules


def parse_declarations(content: str, start_line: int = 1) -> Dict[str, SignalInfo]:
    """Parse signal declarations from content.

    Handles:
    - logic, wire, reg declarations
    - Input/output/inout ports
    - Parameters and localparams (excluded from check)
    - Unpacked array dimensions
    """
    signals: Dict[str, SignalInfo] = {}
    lines = content.split('\n')

    # Pattern for signal declarations
    # Matches: logic/wire/reg [signed] [width] signal_name [array] [, more_signals]
    decl_pattern = re.compile(
        r'\b(logic|wire|reg|input|output|inout)\b'
        r'(?:\s+signed)?'                           # Optional signed
        r'(?:\s*\[[^\]]+\])*'                       # Optional packed dimensions
        r'\s+'
        r'(\w+)'                                     # Signal name
        r'(?:\s*\[[^\]]+\])*'                       # Optional unpacked dimensions
    )

    # Also catch declarations with type first (e.g., "logic [7:0] foo, bar, baz;")
    multi_decl_pattern = re.compile(
        r'\b(logic|wire|reg)\b'
        r'(?:\s+signed)?'
        r'(?:\s*\[[^\]]+\])*'
        r'\s+'
        r'([\w\s,\[\]]+?)'                          # Multiple signal names
        r'\s*;'
    )

    for i, line in enumerate(lines, start_line):
        # Skip parameter/localparam lines
        if re.search(r'\b(parameter|localparam)\b', line):
            continue

        # Skip generate/genvar
        if re.search(r'\b(generate|genvar)\b', line):
            continue

        # Skip function/task declarations (they have local scope)
        if re.search(r'\b(function|task)\b', line):
            continue

        # Try multi-declaration pattern first
        multi_match = multi_decl_pattern.search(line)
        if multi_match:
            decl_type = multi_match.group(1)
            names_str = multi_match.group(2)
            # Extract individual names
            for name_match in re.finditer(r'\b(\w+)\b(?:\s*\[[^\]]*\])*(?:\s*,|\s*$)', names_str):
                name = name_match.group(1)
                if name not in signals and name not in ('signed', 'unsigned'):
                    signals[name] = SignalInfo(name=name, decl_line=i)
        else:
            # Try single declaration pattern
            for match in decl_pattern.finditer(line):
                name = match.group(2)
                if name not in signals:
                    signals[name] = SignalInfo(name=name, decl_line=i)

    return signals


def find_signal_uses(content: str, signals: Dict[str, SignalInfo], start_line: int = 1) -> None:
    """Find first use of each signal and update SignalInfo."""
    lines = content.split('\n')

    # Build regex pattern for all signal names
    if not signals:
        return

    # Sort by length (longest first) to avoid partial matches
    names = sorted(signals.keys(), key=len, reverse=True)

    for i, line in enumerate(lines, start_line):
        # Skip declaration lines and comments
        if re.search(r'\b(logic|wire|reg|input|output|inout|parameter|localparam)\b', line):
            continue

        for name in names:
            if signals[name].first_use_line is not None:
                continue

            # Look for signal use (word boundary match)
            pattern = r'\b' + re.escape(name) + r'\b'
            if re.search(pattern, line):
                signals[name].first_use_line = i


def check_file(filepath: str) -> List[Issue]:
    """Check a single file for declaration order issues."""
    issues = []

    try:
        with open(filepath, 'r') as f:
            content = f.read()
    except IOError as e:
        print(f"Error reading {filepath}: {e}", file=sys.stderr)
        return issues

    # Strip comments and strings for parsing
    clean_content = strip_strings(strip_comments(content))

    # Find module boundaries
    modules = get_module_boundaries(clean_content)

    if not modules:
        # No modules found, check entire file
        modules = [(1, len(clean_content.split('\n')), 'unknown')]

    # Check each module separately
    lines = clean_content.split('\n')
    for start, end, module_name in modules:
        module_content = '\n'.join(lines[start-1:end])

        # Parse declarations
        signals = parse_declarations(module_content, start)

        # Find uses
        find_signal_uses(module_content, signals, start)

        # Check for issues
        for name, info in signals.items():
            if info.first_use_line is not None and info.first_use_line < info.decl_line:
                issues.append(Issue(
                    file=filepath,
                    signal=name,
                    use_line=info.first_use_line,
                    decl_line=info.decl_line
                ))

    return issues


def get_staged_sv_files() -> List[str]:
    """Get list of staged .sv files."""
    try:
        result = subprocess.run(
            ['git', 'diff', '--cached', '--name-only', '--diff-filter=ACM'],
            capture_output=True, text=True, check=True
        )
        files = result.stdout.strip().split('\n')
        return [f for f in files if f.endswith('.sv') and os.path.exists(f)]
    except subprocess.CalledProcessError:
        return []


def get_all_sv_files(root_dir: str) -> List[str]:
    """Get all .sv files under root_dir."""
    sv_files = []
    for dirpath, _, filenames in os.walk(root_dir):
        for fname in filenames:
            if fname.endswith('.sv'):
                sv_files.append(os.path.join(dirpath, fname))
    return sv_files


def main():
    parser = argparse.ArgumentParser(
        description='Check SystemVerilog signals are declared before use'
    )
    parser.add_argument('files', nargs='*', help='Files to check')
    parser.add_argument('--all', action='store_true',
                        help='Check all .sv files in src/rtl')
    parser.add_argument('--staged', action='store_true',
                        help='Check staged .sv files (for pre-commit)')
    parser.add_argument('--quiet', '-q', action='store_true',
                        help='Only print summary')

    args = parser.parse_args()

    # Determine files to check
    files_to_check = []

    if args.staged:
        files_to_check = get_staged_sv_files()
        if not files_to_check:
            print("No staged .sv files to check")
            return 0
    elif args.all:
        # Find repo root
        try:
            result = subprocess.run(
                ['git', 'rev-parse', '--show-toplevel'],
                capture_output=True, text=True, check=True
            )
            repo_root = result.stdout.strip()
            rtl_dir = os.path.join(repo_root, 'src', 'rtl')
            files_to_check = get_all_sv_files(rtl_dir)
        except subprocess.CalledProcessError:
            print("Error: Not in a git repository", file=sys.stderr)
            return 2
    elif args.files:
        files_to_check = args.files
    else:
        parser.print_help()
        return 2

    # Check files
    all_issues = []
    for filepath in files_to_check:
        if not os.path.exists(filepath):
            print(f"Warning: File not found: {filepath}", file=sys.stderr)
            continue
        issues = check_file(filepath)
        all_issues.extend(issues)

    # Report issues
    if all_issues:
        if not args.quiet:
            print(f"\n{'='*70}")
            print("DECLARATION ORDER ISSUES: Signal used before declaration")
            print(f"{'='*70}\n")

            # Group by file
            by_file: Dict[str, List[Issue]] = {}
            for issue in all_issues:
                if issue.file not in by_file:
                    by_file[issue.file] = []
                by_file[issue.file].append(issue)

            for filepath, issues in sorted(by_file.items()):
                print(f"{filepath}:")
                for issue in sorted(issues, key=lambda x: x.use_line):
                    print(f"  Line {issue.use_line}: '{issue.signal}' used before "
                          f"declaration at line {issue.decl_line}")
                print()

        print(f"Found {len(all_issues)} declaration order issue(s) in "
              f"{len(set(i.file for i in all_issues))} file(s)")
        return 1
    else:
        if not args.quiet:
            print(f"Checked {len(files_to_check)} file(s) - no declaration order issues found")
        return 0


if __name__ == '__main__':
    sys.exit(main())
