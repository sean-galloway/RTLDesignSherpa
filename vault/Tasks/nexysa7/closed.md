# NexysA7 tasks - closed

## NEXYS-003: Migrate the remaining char flows onto the shared projects/fpga-systems/bin layer

**Status:** CLOSED 2026-09-23 -- GOAL ACHIEVED. Residue re-filed, not dropped.

Sean 2026-09-23: "All agents say it doesn't apply to them, but no one wants to
close it since it doesn't apply and it just stays open confusing things all of
the time."

That is the correct diagnosis and it is a lifecycle failure, not a work
backlog. This was an UMBRELLA -- port-scan consolidation, program_fpga.tcl
dedup, pumice directory moves, litedram fixes, the Vivado build-target move,
and hardware verification -- six independent jobs behind one number. An
umbrella cannot close until its last sub-item does, so it outlived its own
purpose by weeks and every session that opened it had to re-derive which parts
still applied.

It was also repeatedly WRONG ABOUT ITSELF, which is what made it unclosable.
Its own text records: the port-scan list "was wrong on every count -- the paths
were all pre-reorg, and one of the three had already been migrated"; the
program_fpga.tcl count was stale (four of six had gone with their flows); and
an earlier revision claimed the deferred build-target move was the only thing
left, "written from the top of this task without reading the rest of it."

### The goal is met

`projects/fpga-systems/bin/` holds the shared UART/board/sequence layer and
every flow is on it. Verified 2026-09-23:

- No hand-rolled `/dev/ttyUSB*` glob remains anywhere in the repo; all four
  `autodetect_port` implementations are thin `uart_link.find_port` wrappers.
- `projects/fpga-systems/bin/program_fpga.tcl` is the only copy in the tree.
- pumice -- the migration proof -- imports `sequence.Sequence` and the shared
  `board`/`uart_link`, and `make program` runs through `make/fpga_board.mk`.

### Hardware verification: DONE, and the entry was stale

NEXYS-003 listed "the migrated `make program` path and the pumice
`run_smoke.py` board path have never been run against a board" as outstanding.
Both were exercised repeatedly on 2026-09-21/22 against Nexys A7
`210292BFA3EE`: `make program` flashed `ddr2_char.bit`, and `run_smoke.py` ran
init / write_read / memtest / char / page_policy / wr_batch, all PASS, plus the
axlen, outstanding and bank-gap sweeps.

### Residue, re-filed rather than carried

- pumice directory moves -> **[[NEXYS-008]]**, with the full survey, the (a)
  full-move scope decision and both hazards. It is tidiness: the filelists `-f`
  include the framework in place today and that is legal.
- Vivado build-target move -> belongs to **[[NEXYS-001]]** (consistent
  Makefiles across the flows), which it always overlapped. Deferred there
  deliberately so adopting the shared file could not break a working build.
- litedram `regen.sh` -> `gen/board` + `gen/sim` per RULE #0.1: DONE in
  `8fd7a0406`.
- `char_engine_harness.sv`: no action. build-perf has no `char_engine`
  reference, so there is no divergent copy; the shared piece is
  `char_engine_block.sv`, which moves with NEXYS-008 anyway.

### What it caught on the way, which is why it was worth having

Consolidating the port scan found that the stream probe WRITES -- a SCRATCH
round-trip, not an ID read -- and every harness in this lab speaks the same
ASCII W/R protocol. `H("SCRATCH")` is `0x0001_0020`, inside the rapids board's
DESC-LOAD window, so an unfiltered scan did not bounce off a neighbouring
board, it wrote to it. Both probe builders were completely untested. Also: the
rapids `program_fpga.tcl` pinned a JTAG serial for a unit that left the bench
in August 2026, and `capture_ila.tcl` defaulted to a Genesys 2 serial inside a
Nexys flow.

**Lesson for the tracker, not just this task:** file the JOB, not the THEME. Six
independent jobs behind one number cannot be closed, only re-read.

---

<details><summary>Original entry as it stood at close</summary>

**[archived heading] NEXYS-003: Migrate the remaining char flows onto the shared projects/fpga-systems/bin layer

> **Reviewed 2026-09-23: NOT closeable.** Asked whether this still applies. It
> does -- items 1, 2 and 3 are all still live (each re-verified against the tree
> on that date, see below), and only HALF of item 4 closed. What is genuinely
> finished is the port-scan consolidation and the per-flow `program_fpga.tcl`
> removal, both already marked DONE above.
>
> Filing note: the CONTENT here is cross-cutting methodology, not Nexys-specific
> -- the canonical statements live in `vault/handbook/fpga/cmn-infra/`
> (host-stack, boards, flow-layout, area-structure, sequences) and
> `vault/handbook/dv/registers-by-name.md`. This task is only the migration
> TRACKER for them, and it sits in the nexysa7 area because that area predates
> the `projects/fpga-systems/<board>/<component>/` reorg it describes. It reads
> as board-specific and is not. Worth rehoming to a methodology area.

**Priority:** Medium
**Status:** [ ] Open (2026-07-30)

**Goal:** `projects/fpga-systems/bin/` now holds the common UART/board/sequence layer
(`uart_link.py`, `board.py`, `boards/`, `sequence.py`, one `program_fpga.tcl`).
The pumice DDR2 flow was migrated as the proof. Bring the other flows across.

**DONE (2026-09-22) -- the port scan is consolidated.** All four
`autodetect_port` implementations are now thin `uart_link.find_port` wrappers
and no hand-rolled `/dev/ttyUSB*` glob remains anywhere in the repo. The
original list was wrong on every count: the paths were all pre-reorg, and one of
the three had already been migrated.

- `Genesys2/stream/bin/harness_addrs.py` — DONE. Now
  `find_port(probe=scratch_probe(H("SCRATCH")))`, which is the helper
  `uart_link` had been carrying FOR this function all along (same 0xC0FFEE5A
  magic) and that nothing had ever called. It also gained a `board=` argument
  (honouring `$FPGA_BOARD`) that narrows candidates by USB serial before
  probing -- see the hazard note below.
- `Genesys2/rapids_characterization/flows-rapids-beats/host/rapids_char_io.py`
  — DONE 2026-09-22. Now `find_port(probe=harness_probe())`; the probe reads
  CTRL by name and compares the 'RAP1' magic taken from rapids_char_top.sv
  rather than a docstring. The same pass stopped this file reaching
  `UARTAxiBridge` through the `projects/components/converters/bin` re-export
  shim, which that shim's own docstring forbids new code from using.
- `NexysA7/cdc_counter_display/build-demo/host/cdc_demo.py` — was ALREADY
  migrated before this pass; the entry here was simply stale. It has carried a
  `harness_probe()` and a `find_port` wrapper for some time.

**The hazard this closed.** The stream probe WRITES (a SCRATCH round-trip)
rather than reading an ID constant, and every harness in this lab speaks the
same ASCII W/R protocol -- so an unfiltered scan does not bounce off a
neighbouring board, it writes to it. `H("SCRATCH")` is `0x0001_0020`, which on
the rapids board is inside its DESC-LOAD window. Two changes: naming a board
narrows the candidates by USB serial first, and `uart_link.scratch_probe` now
reads the original value and restores it on a MISMATCH instead of abandoning
the magic in a foreign register. Both probe builders were completely untested
until now, which is why that went unnoticed; `test_uart_link.py` covers them.

New callers should still prefer `Board.find_uart_port(probe=...)` over the bare
`find_port`, for the same USB-serial filtering reason.

**DONE (2026-09-22) -- no per-flow `program_fpga.tcl` remains.**
`projects/fpga-systems/bin/program_fpga.tcl` is the only copy in the tree. The
count here was itself stale: of the six listed, four had already gone with their
flows, and only `flows-rapids-beats` and `timing_characterization/fpga` survived.
Both now set `BITSTREAM` and include `make/fpga_board.mk` instead of carrying an
inline `program:` recipe. The rapids copy pinned a JTAG serial for a unit that
left the bench in August 2026; the timing_characterization copy pinned nothing at
all (`get_hw_targets */xilinx_tcf/*` takes whatever Vivado lists first).
`capture_ila.tcl` was fixed the same way -- it had defaulted to a Genesys 2
serial inside a flow that defaults to the Nexys.

Both halves listed above are done as of 2026-09-22. Several other items in
this task are not -- see "What remains" below.

**Then:** consider moving the Vivado build targets (`project`/`synth`/
`bitstream`/`utilization`/`timing`) into `make/fpga_flow.mk` too — they are
near-identical across all seven flows. Deliberately left out of the first pass
so adopting the file could not break a working build. Overlaps NEXYS-001.

**What remains (corrected 2026-09-22).** An earlier revision of this entry said
the deferred build-target move was the ONLY thing left. That was wrong: it was
written from the top of this task without reading the rest of it. Outstanding:

1. The Vivado build-target move directly above (deferred; overlaps NEXYS-001).
   STILL OPEN, and now down to ONE flow: `make/fpga_flow.mk` carries all five
   targets and every flow uses them EXCEPT
   `Genesys2/rapids_characterization/flows-rapids-beats/Makefile`, which still
   defines its own `bitstream:`. Verified 2026-09-23 by running that flow's
   local target twice.
2. The remaining pumice directory moves under "Remaining moves" below.
   STILL OPEN. Checked 2026-09-23: `pumice/ddr2_char_framework/{rtl,dv}` AND
   `pumice/{rtl,dv}` both exist, so the moves have not happened and the tree is
   carrying both locations at once -- the same duplicate-destination hazard this
   task records under the DROPPED litedram move.
3. The two litedram carry-over fixes below. STILL OPEN, both confirmed
   2026-09-23: `flows-litedram-uart/regen.sh` still writes `build_board`/
   `build_sim`, and `char_engine_harness.sv` is still in
   `flows-litedram-uart/rtl/` rather than `pumice/rtl/`.
4. Hardware verification. **HALF CLOSED 2026-09-23.** The migrated `make program`
   path HAS now run against a board: twice on the Genesys 2 via
   `make/fpga_board.mk` -> `fpga_board.py` -> the shared
   `projects/fpga-systems/bin/program_fpga.tcl`, both `Program complete` RC=0,
   and the FT2232 prefix hazard behaved as designed (passing serial
   `200300B818A0` opened `...B818A0B`, the JTAG channel, via the candidate walk).
   The pumice `run_smoke.py` board path is STILL unverified.

Item 4 cannot be closed without a board attached, so this task stays open even
once everything else here is finished.

**Sequences:** consider `projects/fpga-systems/<board>/<component>/bin/` sequence areas
for rapids/stream, mirroring `projects/fpga-systems/NexysA7/pumice/bin/`.

**Pumice area (build-perf migrated 2026-07-31):** the component lives at
`projects/fpga-systems/NexysA7/pumice/`. `bin/` (sequences) and `build-perf/`
(the whole pumice-on-DDR2 harness) are POPULATED; the former
`projects/fpga-systems/NexysA7/pumice/ddr2-characterization/flows-ours-uart/` no longer exists.
Verified at the new location: `make lint` clean (matches the pre-move baseline),
`bin/filelist_registry.py --check` PASS, 27 sim tests still collect, host unit
tests pass. NOT verified: anything needing Vivado or a board.

Remaining moves:
- `ddr2_char_framework/rtl/*` -> `pumice/rtl/` (flat; keep `bridges/` as-is).
  Shared blocks; `build-perf/rtl/filelists/` currently `-f` includes them in
  place, which is legal, so this is tidiness rather than breakage.
- `ddr2_char_framework/dv/{tb,tbclasses,tests}` -> `pumice/dv/`, then repoint
  `SIM_TESTS` in `build-perf/Makefile` from the framework path to
  `$(SELF_DIR)/dv/tests`.
- ~~`flows-litedram-uart/{rtl,constraints,tcl}` -> `pumice/build-litedram/`~~
  **DROPPED 2026-09-10 (Sean).** `build-litedram/` was scaffolded as the
  destination but the move was never executed, so the repo carried an EMPTY
  duplicate alongside the real, WIRED flow. That cost a session: the empty
  scaffold was found first, taken for the whole job, and the LiteX tooling was
  rebuilt from scratch before `flows-litedram-uart/` surfaced. The empty
  scaffold is deleted and the flow stays where it is; every reference now
  points at `ddr2-characterization/flows-litedram-uart/`. If it is ever moved,
  move it in ONE commit -- do not leave a scaffold standing at the
  destination.

**While moving litedram, two things to fix rather than carry over:**
- `regen.sh` writes to `build_board/` + `build_sim/` at the flow root. Point it
  at `gen/board/` + `gen/sim/` (`--output-dir`) so generated cores sit in one
  named subdirectory per CRITICAL RULE #0.1, and update the `.gitignore`
  (already scaffolded as `gen/`).
- `rtl/char_engine_harness.sv` is described as DUT-agnostic and is what makes
  the pumice-vs-LiteDRAM comparison apples-to-apples, yet it lives in the
  litedram flow. It belongs in `pumice/rtl/` (shared by both builds); check
  whether build-perf has diverged its own copy of the same wiring before
  promoting it.

Reference-fixing checklist, from doing the build-perf half (all five were real,
the rest were comments): `bin/filelists.toml` filelist dir, the build's own `.f`
flow-RTL lines, `ddr2_char_framework/dv/filelists/ddr2_char_uart_tb_top.f`,
`_HOST` in `dv/tests/test_ddr2_char_{uart,char}.py`, and `pumice_env.py`.
Also: the moved build needs `CONVERTERS_ROOT` exported by its Makefile (its
filelist closure resolves `$CONVERTERS_ROOT`), and the tcl scripts now take
`FPGA_PROJECT_ROOT` from the environment instead of guessing `script_dir/..`.

**Parent directory: SETTLED (Sean, 2026-07-30).** New FPGA board areas live
under `projects/fpga-systems/<board>/<component>/`, agreeing with NEXYS-002's
plan. The pumice area was created there. NEXYS-002's move of the existing
`projects/NexysA7/` tree lands alongside it.

**Unverified:** the migrated `make program` path and the pumice `run_smoke.py`
board path have NOT been run against hardware (no board attached, and pyserial
is not installed in the venv — `pip install pyserial` before board work).

</details>

---

