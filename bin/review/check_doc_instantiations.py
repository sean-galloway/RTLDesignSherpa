#!/usr/bin/env python3
"""Check every instantiation in the docs against the real module interface.

A reviewer finds this class one instance at a time, and only where its unit
happens to carry the module's source. common round_1 flagged ONE wrong reset
port in `rtl/common/CLAUDE.md`; pulling that thread by hand found four whole
integration patterns describing modules that do not exist as documented, plus
nine more stale occurrences in the same file. That is a mechanical check, so it
should not cost a review round.

For every ```systemverilog block in the given Markdown, find `module_name #(...)
u_inst (...)` instantiations, resolve `module_name` to `rtl/**/<name>.sv`, and
report parameter overrides and port connections whose names the module does not
declare.

    python3 bin/review/check_doc_instantiations.py docs/markdown/rtl-common
    python3 bin/review/check_doc_instantiations.py docs/markdown rtl/common/CLAUDE.md

Exit status is 1 if anything is reported, so this can gate a commit.

Deliberately conservative -- it reports only names that are absent from the
declaration, never "you forgot to connect X". Docs elide ports on purpose, and
a checker that cries about every abbreviated example gets switched off.
"""
import glob
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# `.name (expr)` / `.name(expr)` -- the connection or override names in an
# instantiation body. `.*` (implicit .name) is legal and carries no name.
CONN = re.compile(r'\.([a-zA-Z_]\w*)\s*\(')
FENCE = re.compile(r'```(?:systemverilog|verilog|sv)\n(.*?)```', re.S)
# name #( ... ) u_inst ( ... );   or   name u_inst ( ... );
INST = re.compile(
    r'\b([a-z][a-z0-9_]{2,})\s*(?:#\s*\((?P<params>[^;]*?)\)\s*)?'
    r'(u_\w+|dut|inst\w*)\s*\((?P<ports>[^;]*?)\)\s*;', re.S)


def split_top(s):
    """Split on commas that are not inside (), [] or {}."""
    out, depth, cur = [], 0, []
    for ch in s:
        if ch in '([{':
            depth += 1
        elif ch in ')]}':
            depth -= 1
        if ch == ',' and depth == 0:
            out.append(''.join(cur))
            cur = []
        else:
            cur.append(ch)
    out.append(''.join(cur))
    return [x.strip() for x in out if x.strip()]


def declared(sv_path):
    """(param names, port names) declared by the module header.

    Ports are split on top-level commas rather than parsed line by line,
    because a direction keyword carries across commas:

        input wire clk,
        rst_n,          <-- still an input, on its own line

    A line-based reader misses `rst_n` and then reports every correct
    `.rst_n(...)` in the docs as undeclared. Two of this repo's modules
    (glitch_free_n_dff_arn, dataint_ecc_hamming_decode_secded) declare
    reset exactly that way.
    """
    src = open(sv_path, encoding='utf-8', errors='replace').read()
    m = re.search(r'^module\s+\w+(.*?)^\s*\);', src, re.S | re.M)
    if not m:
        return None, None
    head = re.sub(r'//[^\n]*', '', m.group(1))
    params = set()
    pm = re.search(r'#\s*\((.*?)\)\s*\(', head, re.S)
    if pm:
        # Drop packed dimensions first, exactly as the port scan below does.
        # Without this, `parameter logic [7:0] UNIT_ID = ...` is invisible to
        # the name regex, so every vector-typed parameter reads as undeclared
        # -- and a doc that MISNAMES one is indistinguishable from a doc that
        # gets it right. 8 such false positives in the monitor book alone.
        ptext = re.sub(r'\[[^\]]*\]', ' ', pm.group(1))
        params = set(re.findall(r'parameter\s+(?:type\s+)?(?:\w+\s+)*?(\w+)\s*=',
                                ptext))
        head = head[pm.end():]
    else:
        # No parameter list: `module name (` leaves the opening paren in `head`,
        # which puts every port comma at depth 1 so split_top never splits and
        # the whole list collapses to one "port". mod_3_compress reported its
        # only real port, d_in, as undeclared because of this.
        head = head.lstrip().lstrip('(')
    ports = set()
    for item in split_top(head):
        item = re.sub(r'\[[^\]]*\]', ' ', item)            # drop packed dims
        item = re.sub(r'\b(input|output|inout|wire|reg|logic|signed|unsigned|var)\b',
                      ' ', item)
        toks = re.findall(r'\b[A-Za-z_]\w*\b', item)
        if toks:
            ports.add(toks[-1])                            # name is last
    return params, ports


def index_modules():
    out = {}
    for p in glob.glob(f'{REPO}/rtl/**/*.sv', recursive=True):
        out.setdefault(os.path.basename(p)[:-3], p)
    return out


def check(md_path, modules):
    text = open(md_path, encoding='utf-8', errors='replace').read()
    issues = []
    for block in FENCE.findall(text):
        for m in INST.finditer(block):
            name = m.group(1)
            if name not in modules:
                continue
            params, ports = declared(modules[name])
            if ports is None:
                continue
            for kind, body, real in (('param', m.group('params'), params),
                                     ('port', m.group('ports'), ports)):
                if not body:
                    continue
                for conn in CONN.findall(body):
                    if conn not in real:
                        issues.append((name, kind, conn,
                                       os.path.relpath(modules[name], REPO)))
    return issues


def main():
    targets = sys.argv[1:] or ['docs/markdown']
    modules = index_modules()
    files = []
    for t in targets:
        t = os.path.join(REPO, t) if not os.path.isabs(t) else t
        files += ([t] if os.path.isfile(t)
                  else glob.glob(f'{t}/**/*.md', recursive=True))
    total = 0
    for f in sorted(set(files)):
        issues = check(f, modules)
        if not issues:
            continue
        print(f'\n{os.path.relpath(f, REPO)}')
        for name, kind, conn, src in issues:
            print(f'  {name}: {kind} `{conn}` is not declared in {src}')
            total += 1
    print(f'\n{total} undeclared name(s) across {len(set(files))} file(s)')
    return 1 if total else 0


if __name__ == '__main__':
    sys.exit(main())
