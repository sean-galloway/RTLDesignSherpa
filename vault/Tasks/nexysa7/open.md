<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# NexysA7 tasks — open (not started)

### NEXYS-007: build-mon host walks slvmon_apb with the wrong regmap

**Priority:** Medium — silent wrong-field writes, but build-mon is not going
near the board until it closes timing, so nothing is at risk today.
**Status:** open 2026-08-31. Found from the rtl/amba side while retiring
`dma_slave_monitors` (TASK-065); filed HERE because the fix is entirely in
`projects/fpga-systems/Genesys2/stream/`.

`dma_slave_monitors` is gone, but its REGBLOCK outlived it and the APB window
got reassigned underneath the host:

- `Genesys2/stream/rtl/stream_harness.sv:452` routes `slvmon_apb` (@ 0x180000)
  to `u_slave_observer`.
- `axi4_intf_slave_observer.sv:518` instantiates **`obs_regs_top`**.
- `Genesys2/stream/build-mon/host/host_reg_walk.py:22,76-78` still walks that
  window with **`slvmon_device`**'s map, labelled "slvmon_apb
  dma_slave_monitors regblock".

The two maps are unrelated at the same offsets — at `0x024`, obs_regs has
`AXIS_MASK1` and slvmon_regs has `RDSLV_ADDR_RANGE_HIGH`. So a register walk,
or any configuration written through that window, touches the wrong fields and
nothing complains. Wrong-field WRITES are worse than a failure here, because
they look like they worked.

**Agreed fix (stream-genesys session, 2026-08-31): retarget the host at
obs_regs.** The window IS `u_slave_observer/obs_regs_top` now, so
`slvmon_device` is describing a block that is not there.

**Then the cleanup falls out.** On the RTL side `slvmon_regs` is already fully
orphaned: `slvmon_regs_top` is instantiated nowhere and no filelist pulls
`slvmon_regs_top.f`. Once the host points at obs_regs, the whole set —
`slvmon_regs.rdl`, `slvmon_regs.vlt`, the filelist, and the generated
RTL + regmap — is dead and deletes cleanly, the same shape as the four dead
packages removed in `65fa8cf0`. Regenerate only via `bin/peakrdl_generate.py`
([[feedback_peakrdl_generate_bin]]), and generate into the directory the
FILELIST consumes.

**Do not delete the regmap before the host moves** — `host_reg_walk.py`
imports `slvmon_device`, so removing it first breaks a script someone may be
running.

---

### NEXYS-004: ddr2-char harness needs TWO bridges, 8 bank-targeted masters each

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
regenerate), plus the harness rewire. Pairs with [[PUMICE-013]]
characterization and [[PUMICE-016]] (observer adoption) — decide whether
each bridge gets its own observer instance before wiring.

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

### NEXYS-001: Consistent Makefiles across the stream characterization flows

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

### NEXYS-002: Rehome NexysA7 under projects/fpga-systems + split Genesys2-specific flows

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

### NEXYS-003: Migrate the remaining char flows onto the shared projects/fpga-systems/bin layer

**Priority:** Medium
**Status:** [ ] Open (2026-07-30)

**Goal:** `projects/fpga-systems/bin/` now holds the common UART/board/sequence layer
(`uart_link.py`, `board.py`, `boards/`, `sequence.py`, one `program_fpga.tcl`).
The pumice DDR2 flow was migrated as the proof. Bring the other flows across.

**Still duplicated (3 copies of the port scan):**
- `stream_characterization/flows-stream-bridge/host/harness_addrs.py`
  — `autodetect_port()` (SCRATCH round-trip probe)
- `rapids_characterization/flows-rapids-beats/host/rapids_char_io.py`
  — `autodetect_port()` (CSR_ID 'RAP1' probe)
- `cdc_counter_display/host/cdc_demo.py`
  — `autodetect_port()` (BUILD_ID 'CDC1' probe)

Each becomes a thin wrapper over `uart_link.find_port(probe=...)`, exactly as
`ddr2_char.autodetect_port` now is. New callers should prefer
`Board.find_uart_port(probe=...)`, which also filters by USB serial.

**Still duplicated (6 remaining copies of program_fpga.tcl):**
`flows-litedram-uart`, `flows-rapids-beats`, `flows-stream-bridge`,
`flows-stream-monitor`, `flows-vivado-mcdma`, `timing_characterization/fpga`.
Each flow Makefile drops its inline `program:` recipe and instead sets
`BITSTREAM` + `RDS_ROOT` and includes the global `make/fpga_flow.mk` (the
[[test-runner]] `make/tests.mk` pattern, applied to board handling); the
per-flow tcl is then deleted. Note `flows-stream-bridge` also switches bitstream
name on `BOARD=genesys2` — fold that into the Makefile, not the tcl.

**Then:** consider moving the Vivado build targets (`project`/`synth`/
`bitstream`/`utilization`/`timing`) into `make/fpga_flow.mk` too — they are
near-identical across all seven flows. Deliberately left out of the first pass
so adopting the file could not break a working build. Overlaps NEXYS-001.

**Sequences:** consider `projects/fpga-systems/<board>/<component>/bin/` sequence areas
for rapids/stream, mirroring `projects/fpga-systems/NexysA7/pumice/bin/`.

**Pumice area (build-perf migrated 2026-07-31):** the component lives at
`projects/fpga-systems/NexysA7/pumice/`. `bin/` (sequences) and `build-perf/`
(the whole pumice-on-DDR2 harness) are POPULATED; the former
`projects/NexysA7/ddr2-characterization/flows-ours-uart/` no longer exists.
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
- `flows-litedram-uart/{rtl,constraints,tcl}` -> `pumice/build-litedram/`
  (`litedram_hp.yml`, `regen.sh`, `README.md`, `HARNESS_PLAN.md` at its root).

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

### NEXYS-005: One name per quantity — BYTES_PER_AXI_BEAT / BYTES_PER_DFI_BEAT / DRAM_BL

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

### NEXYS-006: RISC-V SoC on pumice, running memory-controller stress benchmarks

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
  ([[PUMICE-013]]) if anything does.
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
