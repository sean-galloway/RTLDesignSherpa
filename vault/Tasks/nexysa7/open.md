<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# NexysA7 tasks — open (not started)

## NEXYS-004: ddr2-char harness needs TWO bridges, 8 bank-targeted masters each

**Priority:** Medium
**Status:** [x] RTL + DV + host LANDED 2026-08-31; read/write mix sweep still open

**What landed (2026-08-31):**
- `chargen_regs` -- a GENERATED PeakRDL block (229 registers) holding all
  sixteen generators' config: `WR_GEN[8]` / `RD_GEN[8]` on a 0x40 stride, plus
  a global `GO` (sixteen singlepulse bits, so one write starts any subset on
  one cycle), `DONE` / `ERRORS` roll-ups and a `GEN_CONFIG` identity register
  driven from the harness's own parameters.
- `chargen_apb` slave at 0x000A0000; the config bridge regenerated 1x5 -> 1x6.
- `bridge_ddr2_char_wr` / `bridge_ddr2_char_rd` -- 8x1 AXI4 each, feeding
  pumice's AW/W/B and AR/R channel groups respectively.
- `ddr2_char_macro` rebuilt around a generate loop of 8 writers + 8 readers,
  both bridges, and run-level aggregates (`gen_wr_done` over LAUNCHED
  generators only, `gen_any_error`, `gen_crc_match` over launched pairs).
- `harness_csr`'s single-engine `WR_*`/`RD_*` window (0x100..0x1AF), its CTRL
  start bits, and the single CRC pair are RETIRED; the hole reads 0 and is
  deliberately not re-used.
- DV: `ChargenDriver` (dv/tbclasses) programs by register name over APB --
  the same path the board uses, so the register decode is now exercised in
  simulation instead of being bypassed by poked ports. New `bank_parallel`
  test drives all sixteen concurrently.
- Host: `DDR2CharDriver` gained a `chargen` Device and a `go(wr_mask, rd_mask)`;
  `program_wr_engine` / `start_wr` / `crc` kept their signatures with `gen=0`
  defaults, so the nine bring-up scripts were untouched.

**Two reserved-name traps found, both worth knowing before the next RDL:**
an RDL field named `value` generates `REG.value.value`, which the
declaration-order gate reports as use-before-declaration; a field named
`count` collides with RegisterMap's array-count metadata key and makes the
whole regmap fail to construct. Neither is caught by review -- the first
by `make lint`, the second only by loading the generated regmap.

**Still open:** the read/write mix sweep described below (the measurement the
split exists for), and the synthesis/timing check -- the previous build closed
at WNS +0.050 ns and this adds sixteen generators plus two crossbars.

**Original description follows.**
**Source:** Sean, 2026-08-30 — "the harness will need two bridges, one for
writes and one for reads. On each will be 8 masters each targeting a
different bank."

**Goal:** Restructure the DDR2 characterization harness so read and write
traffic are generated independently and every bank is driven concurrently.

- **Two bridges, split by direction** — one write, one read, rather than
  today's single shared path. Independent direction pressure is what lets a
  test hold one direction saturated while sweeping the other, and it stops
  read/write turnaround from being an accidental variable in every number.
- **8 masters per bridge, one per bank** — bank-parallel by construction, so
  the stimulus exercises the concurrency the scheduler is built around.
  Today's single-stream harness cannot reach the corner that separates the
  paging modes: the sim sweep shows every mode reading 100% with 8-way
  rotation and only `static_close`/`rbl_static` dropping (to 27.79%) once
  traffic is confined to ONE bank. A per-bank master array makes that a
  property of the harness rather than a hand-built address pattern.

**Why it matters for the numbers:** the flat ~12.7 MB/s board result was
traced to a fallback pinned on a single oldest bank (serialised ACT -> tRCD
-> access). A harness that cannot drive banks concurrently cannot tell that
apart from a controller that will not.

**Relation to existing work:** the harness bridge is already generated
(`bridge_ddr2_char_axil`, 1x5 after the obs_apb slot was added 2026-08-28) —
see `ddr2_char_framework/rtl/bridges/configs/`. Splitting it in two is a
config + regen job under CRITICAL RULE #0 (delete ALL generated output, then
regenerate), plus the harness rewire. Pairs with [[TASK-002]]
characterization. (It used to pair with [[PUMICE-016]] observer adoption —
"decide whether each bridge gets its own observer instance before wiring".
016 was dropped 2026-09-23, so there is no observer instance to place and
that decision is moot.)

**Once enabled — read/write mix sweep.** With the two bridges independent,
sweep the direction mix from 100% write / 0% read to 0% write / 100% read in
**5% increments** (21 points). This is the measurement the split exists for:
read/write turnaround (tWTR, tRTW, bus turnaround) is paid at the DRAM and is
invisible to any single-direction test, so the interesting shape is the middle
of the curve, not the endpoints. A single shared path cannot produce it
because direction ratio and offered load are not separable there.

Hold everything else fixed across the sweep — same total offered load, same
address pattern, same page policy — so the only moving variable is the mix.
Every burst stays a whole DFI BL8 transaction (a sub-burst is illegal in the
generators; see `_check_full_burst`), otherwise the mix curve is confounded
by partial-burst overhead.

Endpoints are the sanity check: 100/0 and 0/100 should reproduce the existing
single-direction numbers. A dip that is deeper than turnaround alone explains
points at scheduler behaviour rather than at the device.

## NEXYS-001: Consistent Makefiles across the stream characterization flows

**Priority:** Medium
**Status:** [ ] Open (2026-07-29)

**Goal:** The NexysA7 stream-characterization flows each carry their own
Makefile with drifting targets and build settings. Make them consistent — but
first **define what "consistent" means** (open question, to settle with Sean),
then align the flows to it.

**Flows in scope:**
- `projects/NexysA7/stream_characterization/flows-stream-bridge/` — perf/char
  (the "stream-perf"/"stream-char" flow; `dv/tests/Makefile` + host runner).
- `projects/NexysA7/stream_characterization/flows-stream-monitor/` — monitor
  coverage.
- siblings: `flows-idma-bridge/`, `flows-vivado-mcdma/`, and the top-level
  `stream_characterization/Makefile` dispatcher.

**Why now:** drift is already biting. Concrete symptoms:
- The perf sim build was missing `--unroll-count 4096 --unroll-stmts 20000`
  (needed once monitors-on `RD_MON_MAX_TRANS = NUM_CHANNELS*AR_MAX+4 > 64`),
  while the sibling monitors-on sims (`test_stream_mon`, `test_stream_top_monbus`,
  macro `test_stream_core`) already had it. Fixed ad hoc in commit fe58c772 — but
  the per-flow copy is exactly the rot a consistent contract would prevent.
- `compile_args` are duplicated three times inside `test_stream_char.py` alone.
- Target names / levels / clean semantics are not guaranteed identical across
  flows.

**To DEFINE (the real first step):** what a consistent flow Makefile guarantees —
candidate contract:
- Same target names + meaning: `clean-all`, `run-all-{gate,func,full}`,
  `*-parallel`, `*-wave`, `help`, and the `REG_LEVEL`/`TEST_LEVEL` bridge.
- One shared source of Verilator build args (the unroll flags, the `-Wno-*`
  set) instead of per-test copies — likely a shared include or a helper in
  `make/` / `bin/`, mirroring the components `make/tests.mk` convergence.
- `make clean-all` ALWAYS wipes generated + `local_sim_build` before a run
  (the CRITICAL RULE #0 regen discipline).

**Unified board runner (the bigger half — stop writing a new runner per test):**
Every board test currently re-implements connect + config + kick + poll + verify
in its own `main()`, and `poc_coverage.py` bypasses the shared runner entirely
(rolls its own bridge + config). Layer it once:

1. **Common UART harness (host-stack, already exists — reuse, never reinvent):**
   the transport + by-name register access -- `UARTAxiBridge`, `autodetect_port`
   (ttyUSB numbering drifts), and CSR-by-name via `harness_addrs.H()` (harness
   CSRs) / regmap `A()` (STREAM regs). See [[fpga/cmn-infra/host-stack]]. The
   runner PLUGS INTO this; it must not own UART/AXIL or hardcode offsets.
2. **Shared runner** on top: `CharacterizationRunner`'s core
   (`configure_stream` / `clear_stats` / `setup_timer` / `kick_channels` /
   `poll_completion`) -- one engine for every flow.
3. **Plug-points**: a `workload` (legacy chain / mixed extended chain / error- or
   packet-type-triggering traffic) and a `verify`/`coverage` step (TIMER beat +
   CRC, perf-window read, or **monbus tally sweep for the packet tuples**), plus
   a `loop` mode (one-shot / N-iter soak / scenario sequence).

Then a new board test is a `{workload, verify, loop}` config, NOT a new program:
`stream_ext_soak` = {mixed ext chains, TIMER+CRC, soak}; monitor coverage =
{all-packet-type traffic, tally sweep, scenario sequence}; legacy char =
{legacy chains, perf windows}. Kill the roll-your-own path in `poc_coverage`;
fold `stream_ext_suite` / `stream_ext_soak` / `run_characterization` onto the
shared runner.

**Deliverable:** the agreed definition captured in
[[fpga/cmn-infra/build-flows]], then the flow Makefiles converged to it (shared
include, no duplicated build args), with a note in each flow pointing at the
common contract.

**Related:** the components-side convergence already done via `make/tests.mk`
([[reference_components_regression_makefile]] pattern) is the model to mirror.

---

## NEXYS-002: Rehome NexysA7 under projects/fpga-systems + split Genesys2-specific flows

**Priority:** Medium
**Status:** [ ] Open (2026-07-29)

**Goal:** Structural reorg of the FPGA board projects under the existing
`projects/fpga-systems/` parent.

**Moves:**
- Move `projects/NexysA7/` -> `projects/fpga-systems/NexysA7/`.
- The stream-perf / stream-mon collateral that is **Genesys2-specific** (today it
  lives under the NexysA7 tree, e.g. `flows-stream-bridge/rtl/stream_char_genesys2_top.sv`,
  `flows-stream-monitor/rtl/stream_mon_genesys2_top.sv`, and any Genesys2 XDC /
  build recipes) moves into a `projects/fpga-systems/Genesys2/` directory.
- Split shared vs board-specific: NexysA7-only tops/XDC stay under NexysA7,
  Genesys2-only under Genesys2, common harness/host under a shared area
  (mirrors the [[fpga/cmn-infra]] split already in the handbook).

**Then update ALL references:** filelists (`*.f`), `get_paths`/env roots in the
`dv/tests` wrappers, host `sys.path` inserts, Makefile paths, XDC includes, and
the handbook/vault links (`vault/handbook/fpga/NexysA7/...`,
`vault/handbook/fpga/Genesys2/...`, and this Tasks area's own path). Run
`bin/filelist_registry.py --check` and the char/mon sims after the move.

**Note:** likely rename/rehome this very Tasks area to
`vault/Tasks/projects/fpga-systems/...` (mirror-the-repo-path convention) as part
of the move; fold NEXYS-001 in with it.

---

## NEXYS-008: Move ddr2_char_framework into pumice/ (the NEXYS-003 residue)

**Priority:** Low
**Status:** [ ] Open (2026-09-23)

Split out of [[NEXYS-003]] when that closed. This is the ONLY functional work
that was left in it, and it is TIDINESS, not breakage -- `build-perf/rtl/
filelists/` `-f` includes the framework in place today and that is legal, the
tests run, the flow builds.

- `ddr2_char_framework/rtl/*` -> `pumice/rtl/` (flat; keep `bridges/` as-is)
- `ddr2_char_framework/dv/{tb,tbclasses,tests}` -> `pumice/dv/`, then repoint
  `SIM_TESTS` in `build-perf/Makefile` at `$(SELF_DIR)/dv/tests`

Scope decided 2026-09-23: take the FULL move (retire `ddr2_char_framework`,
rename the `filelists.toml` area and `DDR2_CHAR_FRAMEWORK_ROOT`), not the two
literal bullets. The bullets alone leave `dv/filelists` behind -- `filelists.toml`
registers it and the tests reference it by path -- so DV collateral ends up
split across two directories, and it orphans `regen_bridges.sh` from the bridges
it generates. A half-move needing a second move later is worse than either end.

Survey (verified 2026-09-22, repo-cleanup): 76 tracked files; 51 literal
`ddr2_char_framework` paths across 9 filelists; 4 `bin/filelists.toml` lines;
20 embedded Python path strings, three of them OUTSIDE the pumice tree
(`bin/filelist_registry.py:90`, `bin/TBClasses/shared/filelist_utils.py:117`,
`bin/TBClasses/harness/test_device_bus.py:26`). `DDR2_CHAR_FRAMEWORK_ROOT` is
DEAD CONFIG -- defined in two tables, used by zero `.f` files -- so this is ~70
literal edits, not a one-line variable change. Destinations are empty
(`.gitkeep` only); no name collisions.

**Two hazards.**
1. `regen_bridges.sh` is a GENERATOR and breaks on this move: it derives
   `FRAMEWORK_ROOT="$SCRIPT_DIR/.."` then `BRIDGES_DIR="$FRAMEWORK_ROOT/rtl/
   bridges"`. Invoked by BOTH `build-perf/Makefile:41` and
   `flows-litedram-uart/Makefile:37`, and registered as `regen=` in
   `filelists.toml:158`. CRITICAL RULE #0 applies: regenerate the three bridges
   into a SCRATCH tree and diff the ~30 generated files INDIVIDUALLY before
   committing -- a generator that writes nothing also produces no diff, so the
   regen step must prove it ran, not prove it was quiet. (Scar:
   `regen_bridges.sh` once reverted three rounds of work by writing DV.)
2. `char_engine_harness.sv`'s stated rationale describes a different file.
   build-perf has NO `char_engine` reference, so there is no divergent copy to
   reconcile; the genuinely shared piece is `char_engine_block.sv`, which is in
   `ddr2_char_framework/rtl` and moves anyway.

**Acceptance.** Collection counts are not a gate ([[stale-sim-build-false-green]]).
Record the exact invocation AND geometry on both sides -- the pumice suite runs
the same files at two shapes now (`make run-all-func-both`), so a bare test
total is not like-for-like. Pre-move baseline: `fc83c1b3c`, `top/` 188 passed at
BOTH geometries, char board gate 216 passed / 2 xfailed.

## NEXYS-005: One name per quantity — BYTES_PER_AXI_BEAT / BYTES_PER_DFI_BEAT / DRAM_BL

**Priority:** Medium
**Status:** [ ] Open (2026-08-30)
**Source:** Sean, 2026-08-30 — "can you decide on ONE name instead of 3-4 for
the same thing"; scheme agreed same day.

**Problem:** five names per quantity, and a mismatch between any two of them
fails SILENTLY. Three separate places held a stale BL4 value for six weeks
after the RTL moved to BL8, and none of them complained.

| concept | today | canonical |
|---|---|---|
| one AXI interface transfer | `AXI_DATA_WIDTH`/8, `bytes_per_beat` | `BYTES_PER_AXI_BEAT` |
| one DFI PHASE's data slice | `DRAM_BEAT_WIDTH`/8, `dfi_phase_bytes` | `BYTES_PER_DFI_BEAT` |
| the DQ width (x16 => 2) | `DRAM_DEVICE_WIDTH`/8, `dram_device_bytes` | `BYTES_PER_DEVICE_WORD` |
| JEDEC MR0 burst length | `DRAM_BL`, `BL`, `dram_bl`, `DFI_PHASE.bl`, `BEATS_PER_BURST` | `DRAM_BL` |
| DFI phases per clock | `DFI_RATE` | `DFI_RATE` |

**Everything else derives, one definition each:**

    AXI_BEATS_PER_BURST = DRAM_BL * BYTES_PER_DEVICE_WORD / BYTES_PER_AXI_BEAT
        replaces CHUNK_BEATS, BURST_WORDS, EXP_AXI_BEATS, BURST_LEN_MULTIPLE
    BL_SHIFT / BL_PUMICE  from BYTES_PER_DFI_BEAT / BYTES_PER_DEVICE_WORD
    BYTE_OFFSET_WIDTH     = clog2(BYTES_PER_DEVICE_WORD)
    gear_ratio (CSR)      = log2(DFI_RATE)   -- ALWAYS derived, never typed

**Two rules that are not cosmetic:**

- **`DRAM_BL` is in DEVICE words, not DFI beats.** BL8 on the x16 part is 8
  DQ transfers = 16 bytes = TWO 8-byte DFI beats. Naming it `DFI_BL` would
  read as "8 DFI beats" and be wrong by the device ratio — which is
  `BL_SHIFT`, and getting it wrong is what produced the on-silicon column
  overlap (writes advancing +2 while a BL4 burst spanned +4).
- **`BYTES_PER_DFI_BEAT` is the PHASE slice**, not the full bus word. The bus
  word is `BYTES_PER_DFI_BEAT * DFI_RATE`. DFISlavePHY's `dfi_phase_bytes`
  already uses the phase convention; match it rather than fight it.
- **`gear_ratio` is never hand-written.** It is log2(DFI_RATE); writing the
  rate there overflows `(RATEW'(1) << gear_i)` to 0, every DFI phase reads
  inactive and writes vanish with B=OKAY. That bug cost a full day.

**Scope:** pumice RTL (`CHUNK_BEATS` spans chopper/splitter/ifc), both TB
classes, the harness tests. Behaviour-neutral: land as its own commit and
lean on the 210 (pumice FULL) + 170 (harness macro) regression to prove
bit-identity. Do NOT fold into a functional change.


---

## NEXYS-006: RISC-V SoC on pumice, running memory-controller stress benchmarks

**Priority:** Medium
**Status:** [ ] Open (2026-08-31)
**Source:** Sean, 2026-08-31 — "Is there a riscv cpu we could drop in and run
real benchmarks?", clarified: "By benchmark, I mean a program specific to
stress in MC's."

**Goal:** Put a cached RISC-V core in front of pumice on the Nexys A7 and run
programs written to stress a memory controller, so pumice is exercised by real
software-generated traffic and can be compared against LiteDRAM on the same
board with the same binaries.

**Why this is worth doing even though the generator array exists.** The
generators ([[NEXYS-004]]) are the better *instrument*: bank, stride, burst
length, direction mix and outstanding depth are all dialed exactly. What they
are not is *evidence that real software works*. The counter-argument to a CPU
— that a cache hierarchy sits between the program and the DRAM and obscures
the pattern — does not apply to this class of benchmark, because an MC-stress
program is specifically built to defeat caches and prefetchers. When the
working set is several times the last-level cache and the access pattern is
either streaming or random, the traffic arriving at the controller IS the
traffic the program asked for. That is the whole design intent of these
benchmarks, and it is what makes them usable here.

**The core must have a data cache that does line fills.** This is the one
hard constraint and it eliminates most small cores. A cacheless core
(PicoRV32, Ibex in its default configuration) issues single-word accesses, so
the controller sees single-beat traffic: bank-parallel scheduling, paging
policy and the read-return path are all barely engaged, and the measurement
degrades into a core-latency test. The requirement is AXI burst traffic from
cache line refill and writeback.

**Proven path, and it is cheap.** LiteX + VexRiscv already runs on this exact
board with LiteDRAM — that is the build which proved board, PHY, pins and DRAM
all good ([[project_litedram_ref_proves_board]], 128 MiB @ 300 MT/s memtest,
recipe in `/tmp/nexys_ddr2_memtest.py` + `litex-venv310`). Swapping LiteDRAM
for pumice behind the same port yields the CPU SoC *and* the long-wanted
pumice-vs-LiteDRAM A/B in one move, with identical binaries on both sides —
which is the only way that comparison is honest.

Area is not the obstacle. VexRiscv with 4 KB I$/D$ is roughly 3-5k LUTs
against the XC7A100T's 63400. For scale: the 8+8 generator array cost ~48k
LUTs and did not fit (66470 LUTs; placement short 1469 slices), which is why
the harness is 4+4. A CPU is far cheaper than the array it would sit beside.

**The benchmarks — MC-stress, not CPU benchmarks.** CoreMark, Dhrystone and
Embench are cache-resident and measure the core; they say essentially nothing
about a memory controller and are explicitly out of scope. The set worth
porting, each chosen for a different controller behaviour:

- **STREAM** (copy / scale / add / triad) — sequential read+write bandwidth
  with a working set several times the cache. The canonical bandwidth number,
  and directly comparable against published figures. Exercises page hits and
  the write path.
- **GUPS / HPC-Challenge RandomAccess** — random single-word updates across
  the whole 128 MiB. Maximum row/bank thrash and the worst case for page
  policy; this is the benchmark that should separate the Axis-2 paging modes
  ([[TASK-002]]) if anything does.
- **Pointer chase** (lmbench `lat_mem_rd` style) — dependent-load latency as a
  function of working-set size. Walks the cache hierarchy and then exposes
  tRCD/CL and the read-return path directly; a latency curve is the natural
  companion to a bandwidth number.
- **TinyMemBench** — small, portable C, gives bandwidth and latency together;
  the cheapest thing to stand up first on bare metal.
- **A read/write mix loop** — the software analogue of NEXYS-004's mix sweep,
  so tWTR/tRTW turnaround is paid by real traffic and the two curves can be
  laid over each other.

**What this does NOT replace.** The generator array stays. It isolates
scheduler behaviour in a way no program can, because it can hold every
variable but one fixed. This task adds realism and a comparison baseline; it
does not retire the instrument.

**Open questions to settle before starting:**
1. **Coexist or replace?** Does the CPU SoC live alongside the char harness in
   one bitstream (area and timing pressure on a part that is already tight) or
   as its own separate build sharing pumice? Separate build is the obvious
   first answer, but then the perf counters and the observer slot need to be
   reachable from it.
2. **Where does code live?** BRAM for text/stack with DDR2 as the benchmark
   arena keeps the measurement clean — instruction fetch traffic would
   otherwise contaminate every number. Recommend BRAM for code.
3. **Bare metal or Linux?** Bare metal is enough for all five benchmarks and
   avoids MMU configuration, page-cache effects and a much larger core. Linux
   only if the goal shifts to "boots an OS", which is a different claim.
4. **Which cache line size and outstanding depth**, since these set the burst
   shape pumice actually sees and therefore how comparable the numbers are to
   the generator sweeps.

**Deliverables:** the SoC build under `projects/fpga-systems/NexysA7/pumice/`,
a bare-metal BSP, the ported benchmark set, and a results table against
LiteDRAM on the same board with the same binaries.

---

## NEXYS-007: timing_characterization lost the ability to characterise sync-reset cells

**Priority:** Low
**Status:** Open. Capability gap, not a defect — nothing is broken, something
is no longer measurable.

**What happened.** `ALWAYS_FF_RST` was made unconditionally asynchronous on
assertion repo-wide (2026-09-07). The old `USE_ASYNC_RESET` switch defaulted to
SYNCHRONOUS while `make lint` set the define, so lint and the shipped bitstream
disagreed about what the design was; making it unconditional removed a knob that
let two tools hold different answers and both report success. That was the right
call for the design.

It has a side effect here. `projects/asic-trials/timing_characterization` exists to
characterise a target ASIC cell library, and its README documented sync-reset
numbers as coming from the macro-driven `rtl/` tree with `USE_ASYNC_RESET` left
undefined. That is now impossible: the define is a no-op, so the tree cannot emit a
synchronous-reset flop. A library with sync-reset cells cannot be characterised
for them. (`rtl/asic_only/` was deleted on 2026-09-07 as a duplicate -- it was
hard-wired async anyway, so it never offered this either.)

Nothing consumed those numbers in-tree, which is why this is Low and not a
regression — but the README claimed the capability, so the claim was corrected
in the same change rather than left to be discovered by whoever needed it.

**What a fix looks like.** Give this component its OWN reset header — a
characterization knob, named so it is unmistakably not a copy of the design's
header (`char_reset_defs.svh`, say, not another `reset_defs.svh`). The naming
matters more than it sounds: this component already vendors a copy of
`reset_defs.svh` into `rtl/common/` to keep its filelist self-contained, and
that copy silently kept the OLD conditional after the canonical file changed —
so its flops would have elaborated synchronous while the rest of the tree was
async, with both trees compiling and passing. `bin/check_shared_include_copies.py`
now fails on any tracked copy that has drifted, which is exactly why a
deliberate local variant must not reuse the shared basename.

**Do not** reintroduce `USE_ASYNC_RESET` in the shared header to get this back.
The knob is what broke; a measurement harness wanting a second posture is not a
reason to hand it back to the whole repo.

**Related:** [[build-flows]] records the original lint/synth split and its
resolution.

