#!/usr/bin/env python3
"""
flatten_filelist.py - Flatten hierarchical Verilog/SystemVerilog filelists

Takes a hierarchical filelist with -f includes and produces a flat filelist
with all files in correct compilation order. Supports excluding certain
filelists from expansion (keeping them as -f references).

Usage:
    python flatten_filelist.py <input.f> [options]

Examples:
    # Basic flatten
    python flatten_filelist.py src/filelists/q32/top/q32_top.f

    # Exclude qcore from expansion (keep as -f reference)
    python flatten_filelist.py src/filelists/q32/top/q32_top.f --exclude qcore

    # Output to file
    python flatten_filelist.py src/filelists/q32/top/q32_top.f -o flat.f

    # Resolve environment variables
    python flatten_filelist.py src/filelists/q32/top/q32_top.f --resolve-env
"""

import argparse
import os
import re
import sys
from pathlib import Path
from typing import Set, List, Tuple


class FilelistFlattener:
    def __init__(self, exclude_patterns: List[str] = None, resolve_env: bool = False,
                 keep_env_vars: bool = True, preferred_vars: List[str] = None,
                 dedup: bool = True, verbose: bool = False):
        """
        Initialize the filelist flattener.

        Args:
            exclude_patterns: List of patterns to exclude from expansion (e.g., ['qcore', 'external'])
            resolve_env: If True, resolve environment variables when reading files
            keep_env_vars: If True, keep $VAR in output; if False, use resolved paths
            preferred_vars: List of preferred variable names (in priority order)
            dedup: If True, remove duplicate entries (keep first occurrence)
            verbose: If True, print debug information
        """
        self.exclude_patterns = exclude_patterns or []
        self.resolve_env = resolve_env
        self.keep_env_vars = keep_env_vars
        self.preferred_vars = preferred_vars or []
        self.dedup = dedup
        self.verbose = verbose
        self.seen_files: Set[str] = set()
        self.seen_incdirs: Set[str] = set()

        # Track environment variable mappings for path restoration
        # Exclude generic env vars that would match too broadly
        self.env_mappings: dict = {}
        generic_vars = {'PWD', 'HOME', 'USER', 'PATH', 'SHELL', 'TERM', 'LANG',
                        'OLDPWD', 'SHLVL', 'HOSTNAME', '_', 'LOGNAME', 'REPO_ROOT'}

        if keep_env_vars:
            # First add preferred variables (highest priority)
            for key in self.preferred_vars:
                value = os.environ.get(key)
                if value and len(value) > 3 and value.startswith('/'):
                    self.env_mappings[value] = f"${key}"
                    self._log(f"Preferred var: ${key} = {value}")

            # Then add other variables
            for key, value in os.environ.items():
                if key in generic_vars or key in self.preferred_vars:
                    continue
                if value and len(value) > 3 and value.startswith('/'):
                    # Don't override preferred vars
                    if value not in self.env_mappings:
                        self.env_mappings[value] = f"${key}"

    def _log(self, msg: str):
        """Print debug message if verbose mode is enabled."""
        if self.verbose:
            print(f"[DEBUG] {msg}", file=sys.stderr)

    def _restore_env_vars(self, path: str) -> str:
        """
        Restore environment variables in a resolved path.

        Args:
            path: Resolved absolute path

        Returns:
            Path with environment variables restored (if keep_env_vars is True)
        """
        if not self.keep_env_vars:
            return path

        # Sort by length (longest first) to match most specific paths first
        for resolved_path, env_var in sorted(self.env_mappings.items(),
                                              key=lambda x: len(x[0]), reverse=True):
            if path.startswith(resolved_path):
                return path.replace(resolved_path, env_var, 1)

        return path

    def _resolve_path(self, path: str, base_dir: Path) -> str:
        """
        Resolve a path, optionally expanding environment variables.

        Args:
            path: The path to resolve
            base_dir: Base directory for relative paths

        Returns:
            Resolved path string
        """
        if self.resolve_env:
            # Expand environment variables
            path = os.path.expandvars(path)

        # If path is relative and doesn't start with $, make it relative to base_dir
        if not path.startswith('$') and not path.startswith('/'):
            path = str(base_dir / path)

        return path

    def _should_exclude(self, filepath: str) -> bool:
        """
        Check if a filelist should be excluded from expansion.

        Args:
            filepath: Path to the filelist

        Returns:
            True if the filelist should NOT be expanded
        """
        for pattern in self.exclude_patterns:
            if pattern.lower() in filepath.lower():
                self._log(f"Excluding from expansion: {filepath} (matches '{pattern}')")
                return True
        return False

    def _parse_filelist(self, filepath: str, base_dir: Path) -> Tuple[List[str], List[str], List[str]]:
        """
        Parse a single filelist file.

        Args:
            filepath: Path to the filelist
            base_dir: Base directory for relative paths

        Returns:
            Tuple of (incdir_lines, file_lines, excluded_f_lines)
        """
        incdirs = []
        files = []
        excluded_refs = []

        resolved_path = self._resolve_path(filepath, base_dir)

        # Try to find the actual file
        if resolved_path.startswith('$'):
            # Can't resolve - keep as-is
            self._log(f"Cannot resolve path with env var: {resolved_path}")
            return [], [resolved_path], []

        try:
            with open(resolved_path, 'r') as f:
                lines = f.readlines()
        except FileNotFoundError:
            print(f"Warning: Cannot find filelist: {resolved_path}", file=sys.stderr)
            return [], [], [f"-f {filepath}"]

        filelist_dir = Path(resolved_path).parent

        for line in lines:
            line = line.strip()

            # Skip empty lines and full-line comments
            if not line or line.startswith('#'):
                continue

            # Strip inline comments: everything from the first unquoted '#'
            # (or '//') to end-of-line. Filelists don't have quoted strings
            # so plain split is safe here.
            line = re.split(r'\s+#|\s+//', line, maxsplit=1)[0].rstrip()
            if not line:
                continue

            # Handle +incdir+
            if line.startswith('+incdir+'):
                incdir = line[8:]  # Remove '+incdir+' prefix
                resolved_incdir = self._resolve_path(incdir, filelist_dir)
                output_incdir = self._restore_env_vars(resolved_incdir)
                incdirs.append(f"+incdir+{output_incdir}")

            # Handle -f includes
            elif line.startswith('-f ') or line.startswith('-f\t'):
                ref_path = line[3:].strip()

                if self._should_exclude(ref_path):
                    # Keep as -f reference without expanding
                    excluded_refs.append(line)
                else:
                    # Recursively parse the included filelist
                    sub_incdirs, sub_files, sub_excluded = self._parse_filelist(
                        ref_path, filelist_dir
                    )
                    incdirs.extend(sub_incdirs)
                    files.extend(sub_files)
                    excluded_refs.extend(sub_excluded)

            # Handle regular file entries
            else:
                resolved_file = self._resolve_path(line, filelist_dir)
                output_file = self._restore_env_vars(resolved_file)
                files.append(output_file)

        return incdirs, files, excluded_refs

    def flatten(self, input_file: str) -> str:
        """
        Flatten a hierarchical filelist.

        Args:
            input_file: Path to the input filelist

        Returns:
            Flattened filelist as a string
        """
        self.seen_files.clear()
        self.seen_incdirs.clear()

        input_path = Path(input_file).resolve()
        base_dir = input_path.parent

        self._log(f"Processing: {input_path}")

        incdirs, files, excluded_refs = self._parse_filelist(str(input_path), base_dir)

        # Build output
        output_lines = []

        # Header
        output_lines.append(f"# Flattened filelist generated from: {input_file}")
        output_lines.append(f"# Excluded patterns: {self.exclude_patterns if self.exclude_patterns else 'none'}")
        output_lines.append("")

        # Excluded -f references (kept as-is)
        if excluded_refs:
            output_lines.append("# =============================================================================")
            output_lines.append("# External Dependencies (not expanded)")
            output_lines.append("# =============================================================================")
            for ref in excluded_refs:
                if not self.dedup or ref not in self.seen_files:
                    output_lines.append(ref)
                    self.seen_files.add(ref)
            output_lines.append("")

        # Include directories
        if incdirs:
            output_lines.append("# =============================================================================")
            output_lines.append("# Include Directories")
            output_lines.append("# =============================================================================")
            for incdir in incdirs:
                if not self.dedup or incdir not in self.seen_incdirs:
                    output_lines.append(incdir)
                    self.seen_incdirs.add(incdir)
            output_lines.append("")

        # Source files
        if files:
            output_lines.append("# =============================================================================")
            output_lines.append("# Source Files")
            output_lines.append("# =============================================================================")
            for f in files:
                if not self.dedup or f not in self.seen_files:
                    output_lines.append(f)
                    self.seen_files.add(f)

        return "\n".join(output_lines)


def main():
    parser = argparse.ArgumentParser(
        description="Flatten hierarchical Verilog/SystemVerilog filelists",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s src/filelists/q32/top/q32_top.f
  %(prog)s src/filelists/q32/top/q32_top.f --exclude qcore
  %(prog)s src/filelists/q32/top/q32_top.f --exclude qcore --exclude external -o flat.f
  %(prog)s src/filelists/q32/top/q32_top.f --resolve-env --no-dedup
        """
    )

    parser.add_argument("input", help="Input filelist to flatten")
    parser.add_argument("-o", "--output", help="Output file (default: stdout)")
    parser.add_argument("-e", "--exclude", action="append", default=[],
                        help="Pattern to exclude from expansion (can be used multiple times)")
    parser.add_argument("--resolve-env", action="store_true",
                        help="Resolve environment variables when reading files (required for expansion)")
    parser.add_argument("--absolute-paths", action="store_true",
                        help="Output absolute paths instead of keeping $VAR references")
    parser.add_argument("--prefer-var", action="append", default=[],
                        help="Preferred env var name for output (e.g., Q32_ROOT over REPO_ROOT)")
    parser.add_argument("--no-dedup", action="store_true",
                        help="Don't remove duplicate entries")
    parser.add_argument("-v", "--verbose", action="store_true",
                        help="Enable verbose debug output")

    args = parser.parse_args()

    # Check input file exists
    if not os.path.exists(args.input):
        print(f"Error: Input file not found: {args.input}", file=sys.stderr)
        sys.exit(1)

    # Create flattener and process
    flattener = FilelistFlattener(
        exclude_patterns=args.exclude,
        resolve_env=args.resolve_env,
        keep_env_vars=not args.absolute_paths,
        preferred_vars=args.prefer_var,
        dedup=not args.no_dedup,
        verbose=args.verbose
    )

    result = flattener.flatten(args.input)

    # Output
    if args.output:
        with open(args.output, 'w') as f:
            f.write(result)
            f.write("\n")
        print(f"Wrote flattened filelist to: {args.output}", file=sys.stderr)
    else:
        print(result)


if __name__ == "__main__":
    main()
