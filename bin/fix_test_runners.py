#!/usr/bin/env python3
"""
fix_test_runners.py - Unify all test runners to the canonical wave generation pattern.

Canonical pattern (from q32-ip-0p5_HAS/design_dv):

    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        ...
    }

    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-...',
    ]

    run(
        ...
        extra_args=extra_args,
        extra_env=extra_env,
        waves=enable_waves,
    )

Things removed:
- compile_args / sim_args / plusargs (replaced by extra_args)
- waves=False / waves=True (replaced by waves=enable_waves)
- COCOTB_TRACE_FILE conditional blocks
- keep_files=True
- simulator='verilator' (use SIM env var)
- dump.vcd (replaced by dump.fst)
- --trace (replaced by --trace-fst)
- from conftest import get_coverage_compile_args

Usage:
    python3 bin/fix_test_runners.py val/common/
    python3 bin/fix_test_runners.py val/common/test_math_bf16_adder.py
    python3 bin/fix_test_runners.py --dry-run val/common/
"""

import argparse
import glob
import os
import re
import sys


def extract_wno_flags(content: str) -> list:
    """Extract all -Wno-* flags from compile_args, sim_args, extra_args."""
    flags = set()
    for m in re.finditer(r"['\"](-Wno-\w+)['\"]", content):
        flags.add(m.group(1))
    # Always include TIMESCALEMOD
    flags.add('-Wno-TIMESCALEMOD')
    return sorted(flags)


def fix_file(filepath: str, dry_run: bool = False) -> bool:
    with open(filepath, 'r') as f:
        content = f.read()

    original = content

    # Skip if no run() call
    if 'run(' not in content:
        return False

    # Skip if already canonical
    if ("'--trace-fst'" in content and 'waves=enable_waves' in content
            and 'extra_args=extra_args' in content
            and 'compile_args' not in content
            and 'sim_args' not in content
            and 'plusargs' not in content):
        return False

    # 1. Extract -Wno-* flags before removing blocks
    wno_flags = extract_wno_flags(content)

    # 2. dump.vcd -> dump.fst everywhere
    content = content.replace('dump.vcd', 'dump.fst')

    # 3. Remove "from conftest import get_coverage_compile_args"
    content = re.sub(r'from conftest import get_coverage_compile_args\n', '', content)

    # 4. Remove compile_args block (multi-line)
    content = re.sub(
        r'(?:    # (?:VCD|Add coverage|Trace).*\n)*'
        r'    compile_args\s*=\s*\[.*?\]\s*\n',
        '', content, flags=re.DOTALL)
    # Remove compile_args.extend(...)
    content = re.sub(r'    compile_args\.extend\(.*?\)\s*\n', '', content)

    # 5. Remove sim_args block
    content = re.sub(
        r'    sim_args\s*=\s*\[.*?\]\s*\n',
        '', content, flags=re.DOTALL)

    # 6. Remove plusargs block
    content = re.sub(
        r'    plusargs\s*=\s*\[.*?\]\s*\n',
        '', content, flags=re.DOTALL)

    # 7. Remove COCOTB_TRACE_FILE conditional
    content = re.sub(
        r'    #.*?(?:COCOTB_TRACE_FILE|WAVES support|Conditionally set).*?\n'
        r'    if bool\(int\(os\.environ\.get\([\'"]WAVES[\'"].*?\n'
        r'        extra_env\[[\'"]COCOTB_TRACE_FILE[\'"]\].*?\n',
        '', content)

    # 8. Remove stale comments about VCD/trace
    content = re.sub(r'    # VCD waveform generation support.*\n', '', content)
    content = re.sub(r'    # VCD controlled by compile_args.*\n', '', content)
    content = re.sub(r'    # Must be False!.*\n', '', content)
    content = re.sub(r'    # Explicitly disable auto-FST.*\n', '', content)
    content = re.sub(r'    # We\'re handling tracing manually.*\n', '', content)
    content = re.sub(r'    # WaveDrom handles waveform capture.*\n', '', content)

    # 9. Add enable_waves if missing (before first os.makedirs)
    if 'enable_waves' not in content:
        content = re.sub(
            r'(    os\.makedirs\(sim_build)',
            r'    enable_waves = bool(int(os.environ.get(\'WAVES\', \'0\')))\n\1',
            content, count=1)

    # 10. Build extra_args block
    args_lines = "    extra_args = [\n"
    args_lines += "        '--trace-fst',\n"
    args_lines += "        '--trace-structs',\n"
    for f in wno_flags:
        args_lines += f"        '{f}',\n"
    args_lines += "    ]\n"

    # 11. Remove any existing extra_args block
    content = re.sub(
        r'    extra_args\s*=\s*\[.*?\]\s*\n',
        '', content, flags=re.DOTALL)

    # 12. Insert extra_args before cmd_filename or before try:/run(
    # Prefer before cmd_filename if it exists
    if 'cmd_filename = create_view_cmd' in content:
        content = content.replace(
            '    cmd_filename = create_view_cmd',
            args_lines + '\n    cmd_filename = create_view_cmd')
    elif '    try:\n' in content:
        content = content.replace(
            '    try:\n',
            args_lines + '\n    try:\n')
    else:
        # Last resort: before run(
        content = re.sub(
            r'(\s+run\(\s*\n)',
            args_lines + r'\n\1',
            content, count=1)

    # 13. Fix run() call arguments
    # Remove old args from run()
    content = re.sub(r',?\s*compile_args=compile_args', '', content)
    content = re.sub(r',?\s*sim_args=sim_args', '', content)
    content = re.sub(r',?\s*sim_args=compile_args\)', ')', content)
    content = re.sub(r',?\s*plusargs=plusargs', '', content)
    content = re.sub(r',?\s*keep_files=True', '', content)
    content = re.sub(r",?\s*simulator='verilator'", '', content)
    content = re.sub(r',?\s*simulator="verilator"', '', content)

    # Replace waves=False or waves=True with waves=enable_waves
    content = re.sub(r'waves=False', 'waves=enable_waves', content)
    content = re.sub(r'waves=True', 'waves=enable_waves', content)

    # Add extra_args=extra_args if not already in run()
    if 'extra_args=extra_args' not in content:
        # Insert before waves=enable_waves in run()
        content = re.sub(
            r'(\s+)(waves=enable_waves)',
            r'\1extra_args=extra_args,\n\1\2',
            content, count=1)

    # 14. Clean up multiple blank lines
    content = re.sub(r'\n{3,}', '\n\n', content)

    if content == original:
        return False

    if not dry_run:
        with open(filepath, 'w') as f:
            f.write(content)

    return True


def main():
    parser = argparse.ArgumentParser(
        description='Fix test runners to canonical wave generation pattern')
    parser.add_argument('targets', nargs='+',
                        help='Files or directories to fix')
    parser.add_argument('--dry-run', action='store_true',
                        help='Show what would change without writing')
    args = parser.parse_args()

    files = []
    for target in args.targets:
        if os.path.isdir(target):
            files.extend(sorted(glob.glob(os.path.join(target, 'test_*.py'))))
        elif os.path.isfile(target):
            files.append(target)
        else:
            print(f"Warning: {target} not found", file=sys.stderr)

    fixed = 0
    skipped = 0
    for f in files:
        if fix_file(f, dry_run=args.dry_run):
            action = "WOULD FIX" if args.dry_run else "FIXED"
            print(f"  {action}: {os.path.relpath(f)}")
            fixed += 1
        else:
            skipped += 1

    print(f"\n{fixed} {'would be ' if args.dry_run else ''}fixed, "
          f"{skipped} already OK, {len(files)} total")


if __name__ == '__main__':
    main()
