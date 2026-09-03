#!/usr/bin/env python3
"""Mux-level schematics for the pumice RTL parts (Yosys + netlistsvg -> PNG).

Flow per module, following bin/mux-level-schematics.md:

    filelist (its exact compile closure)
      -> sv2v flatten        (Yosys's SV frontend chokes on pumice_pkg;
                              the doc's documented fallback, same as formal)
      -> yosys, stop after `proc`   (always-blocks -> $mux/$pmux/$dff, memories
                                     as boxes -- NO flatten/techmap/abc/opt)
      -> netlistsvg + ELK    -> SVG
      -> rsvg-convert        -> PNG

Modules over CELL_CAP cells are BLACK-BOXED: their internal schematic is a
hairball at this abstraction (the doc's page-size discipline, sec 9), so they
are skipped and reported. pumice_cmd_arbiter (6500+ cells) is the archetype --
render a sliced cone of it instead if you need its path.

Run:  source $REPO_ROOT/env_python
      python3 <this> [--module NAME]... [--cell-cap N]
"""
import argparse, json, os, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PUMICE = HERE.parent.parent                       # .../pumice-ddr2-lpddr2
REPO = Path(os.environ.get("REPO_ROOT",
            subprocess.check_output(["git","rev-parse","--show-toplevel"],
                                    text=True).strip()))
FUB_FL = PUMICE / "rtl" / "filelists" / "fub"
MACRO_FL = PUMICE / "rtl" / "filelists" / "macro"
BUILD = HERE / "build"
CELL_CAP = 1200        # above this, black-box (unreadable whole-page)

sys.path.insert(0, str(REPO / "bin"))
from TBClasses.shared.filelist_utils import get_sources_from_filelist as resolve_fl

YS = """\
read_verilog {flat}
hierarchy -top {top} -check
proc
opt_expr
opt_clean
memory_collect
memory -nomap
wreduce
write_json {json_out}
"""

def find_filelist(top):
    for d in (FUB_FL, MACRO_FL):
        f = d / f"{top}.f"
        if f.exists():
            return f
    return None

def build_one(top):
    fl = find_filelist(top)
    if fl is None:
        print(f"[skip] {top:<28} no own .f filelist -- if it is a submodule, "
              f"build the parent top instead (its closure includes this)"); return None
    srcs, incs = resolve_fl(repo_root=str(REPO), filelist_path=str(fl))
    sv = [s for s in srcs if s.endswith(".sv")]
    inc_args = [f"-I{d}" for d in incs]

    BUILD.mkdir(parents=True, exist_ok=True)
    flat = BUILD / f"{top}.v"
    with open(flat, "w") as fh:
        r = subprocess.run(["sv2v", "-DUSE_ASYNC_RESET", *inc_args, *sv],
                           stdout=fh, stderr=subprocess.PIPE, text=True)
    if r.returncode != 0:
        print(f"[FAIL] {top:<28} sv2v: {r.stderr.strip().splitlines()[-1:]}"); return None

    json_out = BUILD / f"{top}.json"
    ys = BUILD / f"{top}.ys"
    ys.write_text(YS.format(flat=flat, top=top, json_out=json_out))
    r = subprocess.run(["yosys", "-q", "-s", str(ys)],
                       capture_output=True, text=True)
    if r.returncode != 0:
        print(f"[FAIL] {top:<28} yosys: {r.stderr.strip().splitlines()[-1:]}"); return None

    mods = json.loads(json_out.read_text())["modules"]
    key = top if top in mods else next((m for m in mods if top in m), None)
    ncells = len(mods.get(key, {}).get("cells", {})) if key else 0

    if ncells > CELL_CAP:
        print(f"[bbox] {top:<28} {ncells:>5} cells  -- BLACK-BOXED (too big to render legibly)")
        return ("bbox", top, ncells)

    svg = HERE / f"{top}.svg"
    r = subprocess.run(["netlistsvg", str(json_out), "-o", str(svg)],
                       capture_output=True, text=True, timeout=300)
    if r.returncode != 0 or not svg.exists():
        print(f"[FAIL] {top:<28} netlistsvg: {r.stderr.strip()[:80]}"); return None

    png = HERE / f"{top}.png"
    r = subprocess.run(["rsvg-convert", "-f", "png", "-o", str(png), str(svg)],
                       capture_output=True, text=True)
    svg.unlink(missing_ok=True)          # keep only the PNG the user asked for
    if r.returncode != 0 or not png.exists():
        print(f"[FAIL] {top:<28} rsvg: {r.stderr.strip()[:80]}"); return None
    kb = png.stat().st_size / 1024
    print(f"[ok]   {top:<28} {ncells:>5} cells  {kb:7.1f} KB PNG")
    return ("ok", top, ncells)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--module", action="append")
    ap.add_argument("--cell-cap", type=int)
    a = ap.parse_args()
    global CELL_CAP
    if a.cell_cap: CELL_CAP = a.cell_cap
    if a.module:
        mods = a.module
    else:
        mods = sorted(p.stem for p in FUB_FL.glob("*.f"))
    ok = bbox = fail = 0
    for m in mods:
        r = build_one(m)
        if r is None: fail += 1
        elif r[0] == "bbox": bbox += 1
        else: ok += 1
    print(f"\n{ok} rendered, {bbox} black-boxed (too big), {fail} failed")
    return 1 if fail else 0   # non-zero on any skip/fail so a chained && can't false-green

if __name__ == "__main__":
    sys.exit(main())
