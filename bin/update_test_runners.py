#!/usr/bin/env python3
"""
Update test runner files to include rtl/amba/includes in their get_paths() and run() calls.

This script uses text-based regex manipulation to preserve formatting and comments,
unlike AST-based approaches which destroy code structure.

Usage:
    python3 update_test_runners.py --path val/common --list val/module_list.tst --dry-run --why
"""

import argparse
import re
import shutil
from pathlib import Path
from typing import List, Tuple


TARGET_KEY = "rtl_amba_includes"
TARGET_VAL = "rtl/amba/includes"


# ----------------------- Module list & matching helpers -----------------------

def load_module_list(list_path: Path) -> List[str]:
    """Load module names from a text file, one per line."""
    if not list_path:
        return []
    mods = []
    for raw in list_path.read_text(encoding="utf-8", errors="ignore").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        # Strip HDL extensions
        for ext in ['.sv', '.v', '.vhd']:
            if line.lower().endswith(ext):
                line = line[:-len(ext)]
                break
        mods.append(line.lower())
    return mods


def content_matches(text: str, modules: List[str], *, regex: bool, case_sensitive: bool) -> bool:
    """Return True if any module pattern matches the file text."""
    if not modules:
        return True
    if regex:
        flags = 0 if case_sensitive else re.IGNORECASE
        for pat in modules:
            if not pat:
                continue
            try:
                if re.search(pat, text, flags=flags):
                    return True
            except re.error:
                # Fallback to literal if regex invalid
                if case_sensitive:
                    if pat in text:
                        return True
                else:
                    if pat.lower() in text.lower():
                        return True
        return False
    else:
        if case_sensitive:
            return any(p and (p in text) for p in modules)
        low = text.lower()
        return any(p and (p.lower() in low) for p in modules)


# Regex to find dut_name/toplevel assignments
DUT_TOP_PAT = re.compile(
    r'^\s*(?:dut_name|toplevel)\s*=\s*["\']([^"\']+)["\']\s*(?:#.*)?$',
    flags=re.MULTILINE
)


def names_from_dut_or_toplevel(text: str) -> set:
    """Extract literal strings assigned to dut_name/toplevel."""
    return {m.strip().lower() for m in DUT_TOP_PAT.findall(text)}


# ------------------------------- Text-based rewriters -------------------------------

# Pattern 1: Match get_paths({ ... })
GET_PATHS_PAT = re.compile(
    r'''
    (get_paths\s*\(\s*\{)       # Capture opening: get_paths({
    ([^}]*)                      # Capture dict content (non-greedy, no closing brace)
    (\}\s*\))                    # Capture closing: })
    ''',
    re.VERBOSE | re.DOTALL
)


def add_to_get_paths(text: str) -> Tuple[str, bool]:
    """
    Add TARGET_KEY: TARGET_VAL to get_paths({...}) if not already present.
    Returns (modified_text, changed).
    """
    changed = False

    def replacer(match):
        nonlocal changed
        opening = match.group(1)  # "get_paths({"
        content = match.group(2)  # dict content
        closing = match.group(3)  # "})"

        # Check if TARGET_KEY already exists
        if f"'{TARGET_KEY}'" in content or f'"{TARGET_KEY}"' in content:
            return match.group(0)  # Already present, no change

        # Add the new entry
        # If content is empty or whitespace-only, just add it
        if not content.strip():
            new_content = f"'{TARGET_KEY}': '{TARGET_VAL}'"
        else:
            # Add with comma separator
            # Check if content ends with comma already
            stripped = content.rstrip()
            if stripped.endswith(','):
                new_content = f"{content} '{TARGET_KEY}': '{TARGET_VAL}'"
            else:
                new_content = f"{content}, '{TARGET_KEY}': '{TARGET_VAL}'"

        changed = True
        return opening + new_content + closing

    new_text = GET_PATHS_PAT.sub(replacer, text)
    return new_text, changed


# Pattern 2: Match run() call and add includes parameter
# This is more complex - we need to find run(...) and check if includes= exists

def add_includes_to_run(text: str) -> Tuple[str, bool]:
    """
    Ensure run() has includes=[rtl_dict['rtl_amba_includes']] parameter.
    Returns (modified_text, changed).

    Strategy:
    1. Find run( ... ) calls
    2. Check if includes= parameter exists
    3. If not, add it before the closing paren
    """
    changed = False

    # Find run() calls - match from 'run(' to the matching ')'
    # This is tricky because we need to match balanced parens

    # Simpler approach: find 'run(' and look for 'includes=' nearby
    # If not found, add 'includes=[rtl_dict["rtl_amba_includes"]]' before the last ')'

    # Pattern to find run( ... ) - we'll use a different approach
    # Look for lines with 'run(' and track to the matching ')'

    lines = text.split('\n')
    new_lines = []
    i = 0

    while i < len(lines):
        line = lines[i]

        # Check if this line contains 'run('
        if 'run(' in line:
            # Collect the full run() call (might span multiple lines)
            run_lines = [line]
            paren_depth = line.count('(') - line.count(')')
            j = i + 1

            while paren_depth > 0 and j < len(lines):
                run_lines.append(lines[j])
                paren_depth += lines[j].count('(') - lines[j].count(')')
                j += 1

            run_text = '\n'.join(run_lines)

            # Check if includes= parameter exists
            if 'includes=' in run_text:
                # includes parameter exists - check if it contains our target
                if TARGET_KEY not in run_text:
                    # Need to modify the includes list
                    # This is complex - for now, just warn and skip
                    new_lines.extend(run_lines)
                else:
                    # Already has our target
                    new_lines.extend(run_lines)
            else:
                # No includes parameter - add it
                # Find the last ')' and insert before it
                # Find indent of the run() call
                indent_match = re.match(r'^(\s*)', run_lines[0])
                indent = indent_match.group(1) if indent_match else ''

                # Find the closing paren - it should be on the last line
                last_line_idx = len(run_lines) - 1
                last_line = run_lines[last_line_idx]

                # Find the position of the last ')'
                close_paren_pos = last_line.rfind(')')
                if close_paren_pos != -1:
                    # Insert includes parameter before the closing paren
                    # Check if there's a comma before the closing paren
                    before_paren = last_line[:close_paren_pos].rstrip()
                    if before_paren.endswith(','):
                        # Already has comma
                        insert_text = f"\n{indent}    includes=[rtl_dict['{TARGET_KEY}']],"
                    else:
                        # Need to add comma
                        insert_text = f",\n{indent}    includes=[rtl_dict['{TARGET_KEY}']]"

                    # Modify the last line
                    run_lines[last_line_idx] = (
                        last_line[:close_paren_pos] +
                        insert_text + '\n' + indent +
                        last_line[close_paren_pos:]
                    )
                    changed = True

                new_lines.extend(run_lines)

            i = j
        else:
            new_lines.append(line)
            i += 1

    return '\n'.join(new_lines), changed


# Pattern 3: Add includes variable declaration if needed
def ensure_includes_var(text: str) -> Tuple[str, bool]:
    """
    Ensure there's an includes variable that contains rtl_dict['rtl_amba_includes'].
    If includes variable exists and is empty list, add our entry.
    Returns (modified_text, changed).
    """
    changed = False

    # Look for 'includes = []' pattern
    empty_includes_pat = re.compile(r'^(\s*)includes\s*=\s*\[\s*\]\s*$', re.MULTILINE)

    def replacer(match):
        nonlocal changed
        indent = match.group(1)
        changed = True
        return f"{indent}includes = [rtl_dict['{TARGET_KEY}']]"

    new_text = empty_includes_pat.sub(replacer, text)
    return new_text, changed


# ------------------------------- Core rewriter -------------------------------

def rewrite_test_file(
    path: Path,
    modules: List[str],
    dry_run: bool,
    orig_dir: Path,
    no_filter: bool,
    *,
    grep_only: bool,
    grep_regex: bool,
    grep_case_sensitive: bool,
    why: bool,
) -> Tuple[bool, bool, bool, bool, str]:
    """
    Returns (modified, paths_changed, includes_changed, run_changed, reason).
    """
    text = path.read_text(encoding="utf-8", errors="ignore")

    # Match policy
    match_reason = ""
    if not no_filter:
        if modules:
            mods_norm = set(modules)

            # 1) dut_name / toplevel
            name_hits = names_from_dut_or_toplevel(text)
            if name_hits & mods_norm:
                match_reason = f"dut/toplevel-match({sorted(name_hits & mods_norm)})"
            else:
                # 2) grep policy
                if grep_only:
                    if not content_matches(text, modules, regex=grep_regex, case_sensitive=grep_case_sensitive):
                        return (False, False, False, False, "no-match")
                    match_reason = "grep-match"
                else:
                    if not content_matches(text, modules, regex=False, case_sensitive=False):
                        return (False, False, False, False, "no-match")
                    match_reason = "content-literal-ci"
        else:
            return (False, False, False, False, "empty-list-no-filter")

    # Apply transformations
    new_text = text
    reasons = []

    # 1) Add to get_paths()
    new_text, chg_paths = add_to_get_paths(new_text)
    if chg_paths:
        reasons.append("patched-get_paths")

    # 2) Ensure includes variable
    new_text, chg_includes_var = ensure_includes_var(new_text)
    if chg_includes_var:
        reasons.append("fixed-empty-includes")

    # 3) Add includes to run()
    new_text, chg_run = add_includes_to_run(new_text)
    if chg_run:
        reasons.append("added-includes-to-run")

    changed = chg_paths or chg_includes_var or chg_run

    if not changed:
        return (False, False, False, False, f"matched({match_reason})-but-no-change")

    if dry_run:
        return (True, chg_paths, chg_includes_var, chg_run, f"{match_reason}; {', '.join(reasons)}")

    # Write the modified file
    orig_dir.mkdir(parents=True, exist_ok=True)
    shutil.copy2(path, orig_dir / path.name)
    path.write_text(new_text, encoding="utf-8")
    return (True, chg_paths, chg_includes_var, chg_run, f"{match_reason}; {', '.join(reasons)}")


def iter_test_files(base: Path, recursive: bool) -> List[Path]:
    if recursive:
        return [p for p in base.rglob("test_*.py") if p.is_file()]
    return [p for p in base.iterdir() if p.is_file() and p.name.startswith("test_") and p.suffix == ".py"]


# ----------------------------------- CLI ------------------------------------

def main():
    ap = argparse.ArgumentParser(
        description=("Update test runners to include rtl/amba/includes in get_paths() and run() calls. "
                    "Uses text-based manipulation to preserve formatting and comments."),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    ap.add_argument("--path", required=True, type=Path, help="Directory containing test_*.py files.")
    ap.add_argument("--list", type=Path, help="Text file with module names (one per line). Optional.")
    ap.add_argument("--no-filter", action="store_true", help="Ignore module list and update all test_*.py files.")
    ap.add_argument("--grep-only", action="store_true", help="Match files ONLY if any line from --list appears in file text.")
    ap.add_argument("--grep-regex", action="store_true", help="Interpret --list lines as regex patterns for matching.")
    ap.add_argument("--grep-case-sensitive", action="store_true", help="By default, matching is case-insensitive; enable to make it case-sensitive.")
    ap.add_argument("--dry-run", action="store_true", help="Analyze only; do not write files or copy originals.")
    ap.add_argument("--recursive", action="store_true", help="Recurse into subdirectories.")
    ap.add_argument("--why", action="store_true", help="Print match/change reason per file.")
    args = ap.parse_args()

    base = args.path.resolve()
    if not base.is_dir():
        print(f"[ERROR] --path is not a directory: {base}")
        return

    modules = load_module_list(args.list) if args.list else []
    if not args.no_filter and not modules:
        print("[INFO] No --list provided or list empty; nothing will match unless you use --no-filter.")
        return

    print(f"[INFO] Scanning: {base} (recursive={args.recursive})")
    if args.no_filter:
        print("[INFO] Module filtering disabled (--no-filter)")
    else:
        print(f"[INFO] Modules in list: {len(modules)}")
        mode = "grep-only" if args.grep_only else "dut/toplevel + content (literal, case-insensitive)"
        print(f"[INFO] Match mode: {mode} | regex={args.grep_regex} | case_sensitive={args.grep_case_sensitive}")
    if args.dry_run:
        print("[INFO] DRY RUN (no files modified; no originals copied)")

    tfs = iter_test_files(base, args.recursive)
    if not tfs:
        print("[INFO] No test_*.py files found.")
        return

    orig_dir = Path.cwd() / "ORIG"

    total = 0
    modified = 0
    paths_edits = 0
    includes_edits = 0
    run_edits = 0

    for tf in sorted(tfs):
        total += 1
        changed, chp, chi, chrn, reason = rewrite_test_file(
            tf, modules, args.dry_run, orig_dir, args.no_filter,
            grep_only=args.grep_only,
            grep_regex=args.grep_regex,
            grep_case_sensitive=args.grep_case_sensitive,
            why=args.why,
        )
        if changed:
            modified += 1
            paths_edits += int(chp)
            includes_edits += int(chi)
            run_edits += int(chrn)
            tag = "SCAN" if args.dry_run else "WRITE"
            print(f"[{tag}] {tf}  get_paths:+{int(chp)}  includes:+{int(chi)}  run_kw:+{int(chrn)}"
                + (f"  REASON: {reason}" if args.why else ""))
        else:
            if args.why:
                print(f"[SKIP] {tf}  REASON: {reason}")

    print("\n[SUMMARY]")
    print(f"  test files scanned:   {total}")
    print(f"  files modified:       {modified}")
    print(f"  get_paths() edits:    {paths_edits}")
    print(f"  includes edits:       {includes_edits}")
    print(f"  run(...includes=...)  {run_edits}")
    print("  Done.")


if __name__ == "__main__":
    main()
