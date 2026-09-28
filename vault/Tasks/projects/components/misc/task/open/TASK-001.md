# TASK-001: all RDL lives in the rdl directory

> Migrated 2026-09-27 from `vault/Tasks/projects/components/misc/open.md` as **MISC-001** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** P3. Hygiene, but it is the kind that silently rots -- a stray
source has no obvious home, so the next person adds theirs beside it.
**Status:** open 2026-09-04. Raised by Sean: **all RDL must be in the `rdl`
directory.**

**The violation, exactly.** `projects/components/misc/` already has an `rdl/`
directory holding `dma_address_gen.rdl`, so the convention is established
here. Two more sit in `rtl/`:

**Layout: PER BLOCK** (Sean, 2026-09-04, same call as [[RLB-007]]) --
`rdl/<block>/<name>.rdl`, not a flat directory:

| File | Current | Belongs |
|---|---|---|
| `obs_regs.rdl` | `misc/rtl/` | `misc/rdl/obs/` |
| `tally_regs.rdl` | `misc/rtl/` | `misc/rdl/tally/` |

Note this also moves the file already in place: `misc/rdl/dma_address_gen.rdl`
becomes `misc/rdl/dma_address_gen/dma_address_gen.rdl`. That is the reading of
"per block" applied consistently -- if a single flat file was meant to stay put
in this area, say so, because leaving one file flat beside three nested ones is
the half-applied state this task exists to remove.

**This is not a `git mv`.** Eleven files reference them by path, and they span
two areas -- moving the sources without the references breaks generation and
two FPGA builds:

- `obs_regs.rdl` — `misc/rtl/regs/generated/obs_regs_top_regmap.py`,
  `misc/dv/tests/fub/test_axi4_intf_observer.py`,
  `misc/dv/tbclasses/axi4_intf_observer_tb.py`,
  `Genesys2/stream/dv/tbclasses/stream_harness_tb.py`
- `tally_regs.rdl` — `misc/rtl/regs/generated/tally_regs_top_regmap.py`,
  `misc/rtl/filelists/monbus_tally_axil.f`,
  `Genesys2/stream/rtl/filelists/monbus_tally_axil.f`,
  `Genesys2/stream/build-obs/host/host_reg_walk.py`,
  `Genesys2/stream/build-obs/dv/tests/test_stream_mon.py`

**Method.** Move the three, update all eleven references, then REGENERATE
rather than hand-edit the generated outputs -- the `*_top_regmap.py` files are
PeakRDL output and must come from `bin/peakrdl_generate.py`, which emits RTL,
docs and regmap in lockstep (a raw `peakrdl regblock` desyncs the regmap). Run
the misc tests and the Genesys2 stream build-obs host walk afterwards; both
consume `tally_regs` by name.

**Wider picture, not this task's scope.** The repo has 28 `.rdl` files and
misc is not the only area with them under `rtl/`: retro_legacy_blocks keeps
nine under `rtl/<block>/peakrdl/`, rapids four under `rtl/macro_beats/`,
stream two under `rtl/macro/`, pumice one under `rtl/macro/`. If the rule is
repo-wide rather than misc-local, that is a much larger task and should be
filed per area -- this block deliberately covers only misc, which is what was
asked for.
