# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# The RTL a generated bridge can reference, computed from the generator itself.
#
# Every `$REPO_ROOT/...` path the generator can emit is a SEED; the closure is
# those seeds plus everything their filelists reach through -f. The wheel
# bundles exactly this set (bridge_pkg/ip/, repo-relative), and the unit test
# checks it resolves, so a generator change that emits a new dependency either
# lands in the next wheel or fails the test -- it cannot ship silently missing.

"""Seeds and filelist closure of the RTL a generated bridge depends on."""

from __future__ import annotations

import re
from pathlib import Path
from typing import Dict, FrozenSet, List, NamedTuple, Tuple

PKG_DIR = Path(__file__).resolve().parent
GENERATOR_SOURCES = (PKG_DIR.parent / 'bridge_generator.py', PKG_DIR)

# Area-root variables the closure's filelists use, repo-relative. Anything
# else is an error: the bundle mirrors the repo, so every variable must map
# to a directory inside it.
ROOT_VARS: Dict[str, str] = {
    'REPO_ROOT': '',
    'BRIDGE_ROOT': 'projects/components/fabric-gen-ip/bridge',
    'CONVERTERS_ROOT': 'projects/components/utility-ip/converters',
}

# Template fields the generator formats into filelist names, and the names
# they can take. A new field must be added here or seed extraction fails.
TEMPLATE_FIELDS: Dict[str, Tuple[str, ...]] = {
    'msfx': ('_monlite',),
}
TEMPLATE_GLOBS: Dict[str, str] = {
    # monbus_<p1>_<p2>_group: one per [bridge.mon_group] protocol pair.
    'module_name': 'monbus_*_group',
}

_REF = re.compile(r'\$REPO_ROOT/([A-Za-z0-9_./{}-]+\.(?:f|sv|svh|vlt))')
_VAR = re.compile(r'\$\{?(\w+)\}?')


class Closure(NamedTuple):
    filelists: FrozenSet[str]
    sources: FrozenSet[str]
    incdirs: FrozenSet[str]

    @property
    def files(self) -> FrozenSet[str]:
        return self.filelists | self.sources


def seeds(repo_root: Path) -> List[str]:
    """Every repo-relative file the generator can name, templates expanded."""
    bundled = (PKG_DIR / '_vendor', PKG_DIR / 'ip')   # build output, not generator source
    texts = []
    for src in GENERATOR_SOURCES:
        paths = [src] if src.is_file() else sorted(
            p for p in src.rglob('*') if p.suffix in ('.py', '.j2'))
        texts += [p.read_text(errors='ignore') for p in paths
                  if not any(b in p.parents for b in bundled)]
    found = set()
    for ref in (m.group(1) for t in texts for m in _REF.finditer(t)):
        fields = re.findall(r'\{(\w+)\}', ref)
        unknown = [f for f in fields if f not in TEMPLATE_FIELDS and f not in TEMPLATE_GLOBS]
        if unknown:
            raise ValueError(f"generator emits {ref!r} with unknown template field(s) "
                             f"{unknown}; add them to ip_closure.TEMPLATE_FIELDS/GLOBS")
        expanded = [ref]
        for f in fields:
            if f in TEMPLATE_FIELDS:
                expanded = [e.replace('{' + f + '}', v) for e in expanded
                            for v in TEMPLATE_FIELDS[f]]
            else:
                expanded = [str(p.relative_to(repo_root))
                            for e in expanded
                            for p in sorted(repo_root.glob(e.replace('{' + f + '}', TEMPLATE_GLOBS[f])))]
        found.update(expanded)
    return sorted(found)


def _expand(token: str, repo_root: Path) -> Path:
    def sub(m: re.Match) -> str:
        if m.group(1) not in ROOT_VARS:
            raise ValueError(f"filelist variable ${m.group(1)} has no mapping in ip_closure.ROOT_VARS")
        return str(repo_root / ROOT_VARS[m.group(1)])
    return Path(_VAR.sub(sub, token))


def closure(repo_root: Path) -> Closure:
    """Seeds plus everything their filelists reach. Raises on any dangling ref."""
    repo_root = repo_root.resolve()
    filelists, sources, incdirs, missing = set(), set(), set(), []

    def rel(p: Path) -> str:
        return p.resolve().relative_to(repo_root).as_posix()

    def walk(fl: Path, origin: str) -> None:
        if not fl.is_file():
            missing.append(f"{origin}: -f {fl}")
            return
        key = rel(fl)
        if key in filelists:
            return
        filelists.add(key)
        for raw in fl.read_text().splitlines():
            line = raw.split('//')[0].strip()
            if not line or line.startswith('#'):
                continue
            if line.startswith('-f '):
                walk(_expand(line[3:].strip(), repo_root), key)
            elif line.startswith('+incdir+'):
                incdirs.add(rel(_expand(line[len('+incdir+'):], repo_root)))
            elif line[0] in '+-':
                continue
            else:
                p = _expand(line, repo_root)
                (sources.add(rel(p)) if p.is_file() else missing.append(f"{key}: {line}"))

    for s in seeds(repo_root):
        p = repo_root / s
        if s.endswith('.f'):
            walk(p, 'generator')
        elif p.is_file():
            sources.add(s)
        else:
            missing.append(f"generator: {s}")
    if missing:
        raise FileNotFoundError("bridge IP closure has dangling references:\n  "
                                + "\n  ".join(missing))
    return Closure(frozenset(filelists), frozenset(sources), frozenset(incdirs))
