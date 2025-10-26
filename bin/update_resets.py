#!/usr/bin/env python3
import argparse
import os
import re
from pathlib import Path
from shutil import copy2

# Match: always_ff @(posedge <clk> or negedge <rst>) begin
HDR_RE = re.compile(
    r'^(?P<indent>[ \t]*)always_ff\s*@\(\s*posedge\s+(?P<clk>\w+)'
    r'\s+or\s+negedge\s+(?P<rst>\w+)\s*\)\s*begin',
    re.MULTILINE,
)

BEGIN_RE = re.compile(r'\bbegin\b', re.IGNORECASE)
BE_END_RE = re.compile(r'\b(begin|end)\b', re.IGNORECASE)

TOP_IF_RE = re.compile(r'(?m)^\s*if\s*\([^)]*\)\s*begin')

MODULE_RE = re.compile(r'^\s*module\b', re.MULTILINE)
INCLUDE_RE = re.compile(r'^\s*`include\b.*$', re.MULTILINE)

SV_EXTS = ('.sv', '.v')


def find_block_end(text: str, begin_start: int) -> int:
    m_begin = BEGIN_RE.search(text, begin_start)
    if not m_begin:
        return -1
    depth = 0
    i = m_begin.start()
    while True:
        m = BE_END_RE.search(text, i)
        if not m:
            return -1
        tok = m.group(1).lower()
        if tok == 'begin':
            depth += 1
        else:  # 'end'
            depth -= 1
            if depth == 0:
                return m.end()
        i = m.end()


def normalize_body(inner_body: str, macro_indent: str) -> str:
    # Keep a leading newline if present (prevents token gluing)
    if inner_body.startswith('\n'):
        inner_body = inner_body[1:]

    lines = inner_body.splitlines()
    non_empty = [ln for ln in lines if ln.strip()]
    min_lead = min((len(ln) - len(ln.lstrip(' ')) for ln in non_empty), default=0)

    four = ' ' * 4
    out = []
    for ln in lines:
        # Dedent by min_lead (spaces only) while keeping tabs intact if any
        if ln.startswith(' ' * min_lead):
            core = ln[min_lead:]
        else:
            core = ln.lstrip('\t')
        out.append(macro_indent + four + core if core else macro_indent + four)
    return '\n'.join(out).rstrip() + '\n'


def rewrite_if_to_macro_cond(body_text: str, sync_rst: str) -> str:
    return TOP_IF_RE.sub(f'if (`RST_ASSERTED({sync_rst})) begin', body_text, count=1)


def process_always_blocks(text: str) -> tuple[str, int]:
    out = []
    idx = 0
    changes = 0

    for m in HDR_RE.finditer(text):
        indent = m.group('indent')
        clk = m.group('clk')
        rst = m.group('rst')

        begin_start = m.end() - len('begin')  # points at 'begin'
        end_idx = find_block_end(text, begin_start)
        if end_idx == -1:
            continue

        out.append(text[idx:m.start()])

        block = text[begin_start:end_idx]  # 'begin ... end'
        inner = block[len('begin'):].rstrip()
        if inner.lower().endswith('end'):
            inner = inner[:-len('end')]

        # Use the actual reset signal name (not sync_ prefix)
        body = normalize_body(inner, indent)
        body = rewrite_if_to_macro_cond(body, rst)

        macro = (
            f"{indent}`ALWAYS_FF_RST({clk}, {rst},\n"
            f"{body}"
            f"{indent})\n"
        )
        out.append(macro)
        idx = end_idx
        changes += 1

    out.append(text[idx:])
    return ''.join(out), changes


def insert_reset_include(text: str) -> tuple[str, bool]:
    if 'reset_defs.svh' in text:
        return text, False

    m_mod = MODULE_RE.search(text)
    if not m_mod:
        return text, False

    pre = text[:m_mod.start()]
    includes = list(INCLUDE_RE.finditer(pre))
    insert_pos = includes[-1].end() if includes else m_mod.start()

    insertion = '\n`include "reset_defs.svh"\n'
    return text[:insert_pos] + insertion + text[insert_pos:], True


def should_process(p: Path, exts) -> bool:
    return p.suffix.lower() in exts


def copy_passthrough(src: Path, dst: Path):
    dst.parent.mkdir(parents=True, exist_ok=True)
    copy2(src, dst)


def write_text(dst: Path, s: str):
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(s, encoding='utf-8')


def process_one(src: Path, dst: Path, dry: bool) -> tuple[int, bool]:
    txt = src.read_text(encoding='utf-8', errors='ignore')
    updated, nchg = process_always_blocks(txt)
    updated, inc = insert_reset_include(updated)
    if dry:
        return nchg, inc
    write_text(dst, updated)
    return nchg, inc


def main():
    ap = argparse.ArgumentParser(
        description="Mirror a tree to UPDATED/ and convert async-reset always_ff blocks to `ALWAYS_FF_RST`, inserting `reset_defs.svh`.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    ap.add_argument('src_root', type=Path, help='Source directory to scan')
    ap.add_argument('--dst', type=Path, default=Path('UPDATED'), help='Destination mirror root')
    ap.add_argument('--exts', default='.sv,.v', help='Comma-separated extensions to process')
    ap.add_argument('--dry-run', action='store_true', help='Analyze only; do not write files')
    args = ap.parse_args()

    exts = tuple(e.strip() if e.strip().startswith('.') else f".{e.strip()}"
                for e in args.exts.split(',') if e.strip())

    src_root = args.src_root.resolve()
    dst_root = args.dst.resolve()

    if not src_root.is_dir():
        print(f'[ERROR] Source directory not found: {src_root}')
        return

    print(f'[INFO] Processing:  {src_root}')
    print(f'[INFO] Destination: {dst_root}')
    print(f'[INFO] Extensions:  {exts}')
    if args.dry_run:
        print('[INFO] DRY RUN (no files written)')

    total_sv = 0
    total_blocks = 0
    total_includes = 0

    for root, _, files in os.walk(src_root):
        for fname in files:
            src = Path(root) / fname
            rel = src.relative_to(src_root)
            dst = dst_root / rel

            if not should_process(src, exts):
                if not args.dry_run:
                    copy_passthrough(src, dst)
                continue

            total_sv += 1
            text = src.read_text(encoding='utf-8', errors='ignore')

            if not HDR_RE.search(text) and 'reset_defs.svh' not in text:
                if args.dry_run:
                    print(f'[SKIP]  {rel} (no async always_ff; no include)')
                else:
                    copy_passthrough(src, dst)
                continue

            nchg, inc = process_one(src, dst, args.dry_run)
            total_blocks += nchg
            total_includes += 1 if inc else 0
            tag = 'SCAN' if args.dry_run else 'WRITE'
            print(f'[{tag}] {rel}  blocks:{nchg}  include_added:{inc}')

    print('\n[SUMMARY]')
    print(f'  Files scanned (SV/V):       {total_sv}')
    print(f'  always_ff blocks converted: {total_blocks}')
    print(f'  files with include inserted:{total_includes}')
    print('  Done.')


if __name__ == '__main__':
    main()
