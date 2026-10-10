#!/usr/bin/env python3
"""Verify every register/field a host driver references exists -- IN THE MAP
THAT CALL ACTUALLY USES.

Device-aware on purpose, and that is the whole value. An earlier version
validated names against the UNION of the three regmaps and reported
"all references resolve" for `self.regs.read("STATUS.init_error")` -- because
init_error exists on the CONTROLLER's STATUS while self.regs is the HARNESS
device, whose STATUS has init_fail. A union check cannot see that class of bug,
and on hardware it does not raise: it returns whatever the harness has at that
offset.

Attribute -> regmap is declared below rather than inferred, because the whole
point is to catch a call using the wrong one.

    ./check_regnames.py          # exit 1 on any unresolved reference
"""
from __future__ import annotations
import ast, importlib.util, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.environ.get("REPO_ROOT") or os.popen(
    "git rev-parse --show-toplevel").read().strip()
FW = os.path.join(REPO, "projects/fpga-systems/rtl/mem_char_framework/dv/tbclasses")
SC = os.path.join(REPO, "projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3",
                  "regs/generated/scoria_csr_regmap.py")

#: self.<attr> -> which regmap that Device is constructed with.
DEVICE_MAP = {
    "regs":    os.path.join(FW, "harness_csr_regmap.py"),
    "chargen": os.path.join(FW, "chargen_regs_regmap.py"),
    "scoria":  SC,
}
SOURCES = ["ddr3_char.py", "scoria_device.py", "scoria_char.py"]
#: scoria_device.py's methods are all on the Scoria device itself (self.regs
#: there IS the scoria regmap, via Device.__init__), so it is checked alone.
SELF_IS = {"scoria_device.py": SC}


def load(path):
    spec = importlib.util.spec_from_file_location("m", path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m.top_block


def fields(blk, reg):
    return {k for k, v in blk.get(reg, {}).items()
            if isinstance(v, dict) and v.get("type") == "field"}


def check(path, resolve):
    """resolve(attr) -> regmap dict, or None when the attr is not a Device."""
    bad, seen = [], 0
    tree = ast.parse(open(os.path.join(HERE, path)).read())
    for call in [n for n in ast.walk(tree) if isinstance(n, ast.Call)]:
        fn = call.func
        if not isinstance(fn, ast.Attribute) or fn.attr not in (
                "read", "write", "write_word", "field"):
            continue
        # self.<attr>.read(...)  /  self.regs.write(...)
        owner = fn.value
        attr = None
        if (isinstance(owner, ast.Attribute)
                and isinstance(owner.value, ast.Name)
                and owner.value.id == "self"):
            # self.<attr>.read(...)
            attr = owner.attr
        elif (isinstance(owner, ast.Attribute) and owner.attr == "regs"
              and isinstance(owner.value, ast.Attribute)):
            # <param>.scoria.regs.read(...) -- how scoria_char reaches the
            # controller. The Device's own .regs IS that device's map, so the
            # map is named by the MIDDLE attribute, not by "regs".
            attr = owner.value.attr
        if attr is None:
            continue
        blk = resolve(attr)
        if blk is None:
            continue
        if not call.args or not isinstance(call.args[0], ast.Constant):
            continue
        name = call.args[0].value
        if not isinstance(name, str):
            continue
        reg, _, dotted = name.partition(".")
        cand = [reg]
        if "{" in reg:      # f-string-free literals only; skip computed names
            continue
        seen += 1
        if reg not in blk:
            bad.append((path, owner.attr, reg, "<REGISTER MISSING>")); continue
        want = [dotted] if dotted else []
        # kwargs are field names: write("REG", field=...)
        want += [k.arg for k in call.keywords if k.arg]
        # field("REG", "name", v)
        if fn.attr == "field" and len(call.args) >= 2 and isinstance(
                call.args[1], ast.Constant):
            want.append(call.args[1].value)
        for f in want:
            if f and f not in fields(blk, reg):
                bad.append((path, owner.attr, reg, f))
    return seen, bad


def main() -> int:
    maps = {k: load(v) for k, v in DEVICE_MAP.items()}
    total, allbad = 0, []
    for src in SOURCES:
        if src in SELF_IS:
            own = load(SELF_IS[src])
            r = lambda a: own if a == "regs" else None
        else:
            r = lambda a: maps.get(a)
        n, bad = check(src, r)
        print(f"  {src}: {n} device-qualified register calls checked")
        total += n; allbad += bad
    if allbad:
        print(f"\n  {len(allbad)} UNRESOLVED:")
        for p, dev, reg, f in allbad:
            print(f"     {p}  self.{dev}  {reg}.{f}")
        return 1
    print(f"  all {total} resolve against the map their Device actually uses")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
