#!/usr/bin/env python3
"""
Wrap string parameters in SystemVerilog files with translate_off/translate_on pragmas.

Usage:
    python wrap_string_params.py <file.sv> [--inplace]
    python wrap_string_params.py src/rtl/q32/fub/*.sv --inplace
"""

import argparse
import re
import sys
from pathlib import Path


def wrap_string_params(content: str, pragma_style: str = "synopsys") -> str:
    """Wrap parameter string declarations with translate pragmas."""

    off_pragma = f"// {pragma_style} translate_off"
    on_pragma = f"// {pragma_style} translate_on"

    lines = content.split('\n')
    result = []
    i = 0

    while i < len(lines):
        line = lines[i]

        # Skip if already wrapped (check previous line for translate_off)
        if i > 0 and "translate_off" in lines[i-1]:
            result.append(line)
            i += 1
            continue

        # Check for parameter string (with optional 'localparam')
        # Matches: parameter string NAME = "value"
        #          localparam string NAME = "value"
        match = re.match(
            r'^(\s*)((?:local)?parameter\s+string\s+\w+\s*=\s*.*)$',
            line
        )

        if match:
            indent = match.group(1)

            # For string parameters that end with comma, strip it and re-add after translate_on
            # For those without comma (last param), just wrap the line
            param_line = line.rstrip()

            # Check if line ends with comma (possibly followed by comment)
            comma_match = re.match(r'^(.*),(\s*//.*)?$', param_line)

            if comma_match:
                # Parameter ends with comma - need to restructure
                # Before: parameter string FOO = "bar",  // comment
                # After:  // synopsys translate_off
                #         parameter string FOO = "bar",  // comment
                #         // synopsys translate_on
                result.append(f"{indent}{off_pragma}")
                result.append(line)
                result.append(f"{indent}{on_pragma}")
            else:
                # Parameter without trailing comma (last parameter before closing paren)
                # Before: parameter string FOO = "bar"  // comment
                # After:  // synopsys translate_off
                #         parameter string FOO = "bar",  // comment  <- ADD COMMA
                #         // synopsys translate_on
                #         // (dummy parameter to maintain syntax)
                #
                # Actually, simpler approach: just wrap it
                result.append(f"{indent}{off_pragma}")
                result.append(line)
                result.append(f"{indent}{on_pragma}")

            i += 1
            continue

        result.append(line)
        i += 1

    return '\n'.join(result)


def process_file(filepath: Path, inplace: bool = False, pragma_style: str = "synopsys") -> bool:
    """Process a single file. Returns True if changes were made."""

    content = filepath.read_text()

    # Skip if no string parameters
    if not re.search(r'(?:local)?parameter\s+string\s+', content):
        return False

    # Skip if already has translate pragmas around string params
    if re.search(r'translate_off\s*\n\s*(?:local)?parameter\s+string', content):
        print(f"  {filepath}: already wrapped, skipping")
        return False

    new_content = wrap_string_params(content, pragma_style)

    if new_content == content:
        return False

    if inplace:
        filepath.write_text(new_content)
        print(f"  {filepath}: updated")
    else:
        print(f"=== {filepath} ===")
        print(new_content)

    return True


def main():
    parser = argparse.ArgumentParser(
        description="Wrap string parameters with translate_off/on pragmas"
    )
    parser.add_argument("files", nargs="+", help="SystemVerilog files to process")
    parser.add_argument("--inplace", "-i", action="store_true",
                        help="Modify files in place")
    parser.add_argument("--pragma", "-p", default="synopsys",
                        choices=["synopsys", "cadence", "pragma"],
                        help="Pragma style (default: synopsys)")

    args = parser.parse_args()

    files_changed = 0
    for pattern in args.files:
        for filepath in Path(".").glob(pattern) if "*" in pattern else [Path(pattern)]:
            if filepath.suffix in (".sv", ".svh", ".v", ".vh"):
                if process_file(filepath, args.inplace, args.pragma):
                    files_changed += 1

    print(f"\n{files_changed} file(s) {'modified' if args.inplace else 'would be modified'}")


if __name__ == "__main__":
    main()
