#!/usr/bin/env python3
"""
check_sv_call_select.py - find a select applied to a function call

IEEE 1800 allows a bit / part select on a variable or a net, not on the value
a function call returns: `f_sb(addr, seed)[0]` and `$clog2(N)[1:0]` are not
legal SystemVerilog. Verilator accepts both without a warning, even with
-Wall, and simulates them, so a block can pass every test and then stop
Vivado at read time:

    ERROR: [Synth 8-12513] select on function call violates IEEE 1800 syntax

Give the result a name and select that. A width cast of the whole call,
`8'(f(x))`, is legal and is not reported.

Rule and history: vault/handbook/design/select-on-function-call.md

Usage:
    check_sv_call_select.py <file1.sv> [file2.sv ...]
    check_sv_call_select.py --all          # every .sv under rtl/, projects/, val/, formal/
    check_sv_call_select.py --staged       # staged .sv files (for pre-commit)

Exit codes:
    0 - no select on a call found
    1 - one or more found (each printed as file:line: text)
    2 - error (a file could not be read)
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path
from typing import List, Tuple

# Words that are followed by a parenthesised expression in SystemVerilog but
# are not calls: control flow, event control, and the constructs whose
# parenthesis closes a header rather than an expression.
NOT_CALLS = {
    'if', 'for', 'foreach', 'while', 'repeat', 'case', 'casez', 'casex',
    'wait', 'iff', 'assert', 'assume', 'cover', 'restrict', 'property',
    'sequence', 'with', 'return', 'disable', 'unique', 'unique0', 'priority',
    'always', 'always_ff', 'always_comb', 'always_latch', 'initial', 'final',
    'module', 'interface', 'program', 'package', 'function', 'task',
    'begin', 'fork', 'else', 'do', 'forever', 'void',
}

IDENT_BEFORE_PAREN = re.compile(r'(\$?[A-Za-z_][A-Za-z0-9_$]*)\s*\($')


def strip_comments_and_strings(text: str) -> str:
    """Blank comments and string literals, keeping every newline (and so every
    line number) where it was."""
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith('//', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i))
            i = j
        elif text.startswith('/*', i):
            j = text.find('*/', i + 2)
            j = n if j < 0 else j + 2
            out.append(re.sub(r'[^\n]', ' ', text[i:j]))
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"' and text[j] != '\n':
                j += 2 if text[j] == '\\' else 1
            j = min(j + 1, n)
            out.append('"' + ' ' * max(0, j - i - 2) + '"' if j - i >= 2 else '"')
            i = j
        else:
            out.append(c)
            i += 1
    return ''.join(out)


def find(text: str) -> List[Tuple[int, str]]:
    """(line, call) for every `name(...)[` in already-stripped text."""
    hits = []
    for m in re.finditer(r'\(', text):
        start = m.start()
        head = text[max(0, start - 200):start + 1]
        hm = IDENT_BEFORE_PAREN.search(head)
        if not hm:
            continue
        name = hm.group(1)
        if name in NOT_CALLS:
            continue
        name_pos = start - (len(hm.group(0)) - 1)
        prev = text[:name_pos].rstrip()[-1:] if text[:name_pos].strip() else ''
        if prev in ('`', '.', '#'):        # macro, named port, parameter list
            continue
        # balanced close of this parenthesis
        depth, j = 0, start
        while j < len(text):
            if text[j] == '(':
                depth += 1
            elif text[j] == ')':
                depth -= 1
                if depth == 0:
                    break
            j += 1
        if j >= len(text):
            continue
        k = j + 1
        while k < len(text) and text[k] in ' \t':
            k += 1
        if k < len(text) and text[k] == '[':
            line = text.count('\n', 0, name_pos) + 1
            call = re.sub(r'\s+', ' ', text[name_pos:k + 1])
            hits.append((line, call if len(call) <= 90 else call[:87] + '...'))
    return hits


def staged_files() -> List[str]:
    out = subprocess.run(['git', 'diff', '--cached', '--name-only', '--diff-filter=ACMR'],
                         capture_output=True, text=True, check=True).stdout
    return [f for f in out.split() if f.endswith('.sv')]


def all_files() -> List[str]:
    roots = ['rtl', 'projects', 'val', 'formal']
    return sorted(str(p) for r in roots if Path(r).is_dir() for p in Path(r).rglob('*.sv'))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('files', nargs='*')
    ap.add_argument('--all', action='store_true')
    ap.add_argument('--staged', action='store_true')
    args = ap.parse_args()
    files = args.files + (staged_files() if args.staged else []) + (all_files() if args.all else [])
    rc, found = 0, 0
    for f in files:
        try:
            text = Path(f).read_text(errors='replace')
        except OSError as e:
            print(f'{f}: cannot read: {e}', file=sys.stderr)
            rc = 2
            continue
        for line, call in find(strip_comments_and_strings(text)):
            print(f'{f}:{line}: select on a function call: {call}')
            found += 1
    print(f'Checked {len(files)} file(s) - '
          + (f'{found} select(s) on a function call (not IEEE 1800; Vivado refuses them)'
             if found else 'no select on a function call'))
    if found and rc == 0:
        rc = 1
    return rc


if __name__ == '__main__':
    sys.exit(main())
