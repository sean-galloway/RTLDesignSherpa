# TASK-019: filelist_utils.tcl exists as eight copies and seven do not treat // as a comment

**Priority:** P3
**Status:** CLOSED 2026-09-29 (done)
**Owner:** TBD
**Filed:** 2026-09-29 (found by timing_characterization TASK-001)

`filelist_utils.tcl` -- the Vivado-side expander for repo-style `.f`
filelists (env vars, `+incdir+`, nested `-f`, comments) -- exists as EIGHT
copies:

```
projects/asic-trials/timing_characterization/fpga/tcl/filelist_utils.tcl   (fixed 2026-09-29)
projects/components/fabric-gen-ip/bridge/fpga/tcl/filelist_utils.tcl
projects/fpga-systems/Genesys2/dma-ip/rapids_beats/flows-rapids-beats/tcl/filelist_utils.tcl
projects/fpga-systems/Genesys2/dma-ip/stream/fpga/tcl/filelist_utils.tcl
projects/fpga-systems/NexysA7/misc-ip/cdc_counter_display/build-demo/fpga/tcl/filelist_utils.tcl
projects/fpga-systems/NexysA7/misc-ip/cdc_counter_display/build-phase1/fpga/tcl/filelist_utils.tcl
projects/fpga-systems/NexysA7/mem-ctrl-ip/pumice/build-perf/fpga/tcl/filelist_utils.tcl
rtl/amba/fpga/tcl/filelist_utils.tcl
```

Seven of them treat only `#` as a comment. The repo's filelists use `//`
(`char_top.f` is written entirely with `//` headings), and the cocotb-side
expander `bin/TBClasses/shared/filelist_utils.py` strips both `#` and `//`.
With the Tcl copies, every `// heading` line comes back as a source path
beginning with `/ ` and the Vivado project creation fails on "source file
missing" -- which is what happened the first time the Quartus sweep reused
the timing_characterization copy. The other seven flows have not hit it only
because their filelists happen to use `#`.

Two copies of a parser with different grammars for the same file format is
[[filelists]]'s "a doubled slash is a comment and silently drops a source"
gotcha waiting to happen in reverse. Options, in order of preference:

1. One shared `make/tcl/filelist_utils.tcl` (beside `make/fpga_flow.mk`,
   which every flow already includes), sourced by each `create_project.tcl`;
   delete the copies.
2. Failing that, apply the `//` fix to all seven and add a check that the
   copies are byte-identical.

**Done when:**

- [ ] one expander (or eight identical ones, mechanically checked)
- [ ] `//` line and trailing comments handled in every copy, matching the
      Python expander
- [ ] a filelist with `//` headings expands identically through the Tcl and
      Python expanders (test it, do not eyeball it)

---

## CLOSED 2026-09-29 -- one expander, sourced by every flow, agreement tested

- `make/tcl/filelist_utils.tcl` is the one Tcl copy (git-moved from the
  timing_characterization flow, which carried the `//` fix). The seven others
  are deleted. All eight sourcing scripts (`create_project.tcl` x6,
  `bridge/fpga/tcl/synth_only.tcl`, `rtl/amba/fpga/tcl/monitor_synth.tcl`) and
  the Quartus sweep source it through `$::env(REPO_ROOT)` with a
  `git rev-parse --show-toplevel` fallback for running a script by hand.
- `bin/tests/test_filelist_utils_tcl.py`: one filelist using `#`, `//`,
  trailing comments, `+incdir+`, a `$REPO_ROOT`-anchored nested `-f`, an
  anchored source and bare relative sources, expanded through
  `filelist::flatten` (tclsh) and `get_sources_from_filelist` (Python);
  sources and include dirs compared as sets. 2/2 pass. Skips when tclsh is
  absent.
- The one grammar difference that remains -- the Python side opens a nested
  `-f` verbatim, the Tcl side resolves it against the filelist's
  parent-of-parent -- is recorded in [[filelists]] with the convention that
  keeps it harmless (anchor nested `-f` on a root variable, as every repo
  filelist already does).
- Proven on a real flow, not only the test: the timing_characterization
  Vivado `bitstream-sweep` running during this change picked up the rewired
  `create_project.tcl` at its second and third points and built through.
