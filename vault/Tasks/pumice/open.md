<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# pumice — Open (accepted, not started)

---

## PUMICE-030 — read latency is ~2x LiteDRAM's, and it caps small-burst reads
**Status:** open 2026-09-10  **Priority:** P1 — the largest identified defect left

**The bug: ~49 MC cycles of read latency against LiteDRAM's 24.7** on the same
board, the same PHY and the same harness. Roughly 24 cycles of extra pipeline
for the same DRAM access. Neither 2026-09-10 bandwidth fix (the intake admit
stage, the return-ring depth) moved it.

**Why it matters beyond latency: it caps small-burst read BANDWIDTH.** Reads at
AxLEN 1/2/4 reach 16%/31%/60% of peak while writes hold 95% on the same
addresses. This was previously written off as "per-transaction overhead, a
mechanism nobody has identified". It is identified: **Little's law**, against
the read generator's 8-outstanding-burst budget.

Model: `min(8 x AxLEN / (read_latency + AxLEN), 0.95) x 8 B x 75 MHz`

| AxLEN | predicted MB/s | measured MB/s |
|---|---|---|
| 1 | 96.1 | 96.2 |
| 2 | 184.6 | 188.1 |
| 4 | 369.2 | 359.9 |
| 8 | 570.0 | 570.5 |
| 16 | 570.0 | 570.7 |

Five points inside 2%, board-measured with `bin/axlen_sweep.py`.

**Two things this rules out.** It is NOT a scheduling bug, and specifically it
is NOT "the read cannot be scheduled until the write is consumed on AXI" (a
reasonable guess, checked and discarded): the characterization runs a write
phase to completion and THEN a read phase, so no writes are in flight while the
reads are measured. It is also not the return ring -- the shortfall did not move
between depth 32 and 64.

**Why writes are immune.** pumice returns B at CAM commit, not after a DRAM
round trip, so a write burst retires in a fraction of a read's time and the same
8-burst budget is ample.

**The fix is the latency, and it closes the bandwidth gap with it.** At
LiteDRAM's 24.7 cycles the same 8-burst budget covers AxLEN 4 (8x4/28.7 = 1.11,
i.e. no longer binding) and the shortfall vanishes from AxLEN 4 upward.
Raising `GEN_MAX_OUTSTANDING` in the harness would ALSO move the numbers, but
that is moving the measurement, not fixing the controller -- a real master with
few outstanding reads would still see the latency.

**Where to look.** The read path crosses intake -> rd CAM -> arbiter -> DFI ->
PHY -> aligner -> return ring -> R channel. `ch01_overview/04_pipeline_latency.md`
in the MAS has the per-stage flop counts from the elaborated netlist; compare
that budget against the measured 49 and find the stages LiteDRAM does not have.
The AR-order return ring and the reorder CAM are the obvious suspects, and both
are research features -- this may be a deliberate cost rather than a defect,
but nobody has done the accounting to say which.

---

## PUMICE-029 — pumice is AT REST: what a future session needs to know
**Status:** open 2026-09-10 (informational; do not close, it is the handover)
**Priority:** read before touching pumice

pumice met its targets on 2026-09-10 and was deliberately put down. This block
is the handover, not a work item.

**Where it landed.** Nexys A7, 75 MHz / DDR2-300 / BL4 on x16, peak 600 MB/s:
write 570.3, read 571.3, concurrent read+write 570.1 total (2.00x LiteDRAM
through the identical harness). 14/14 integrity, WNS +0.285 ns on 94 060
endpoints, 219 controller tests plus the 31-test char gate green. Board build:
`PUMICE_SYS_75=1 make bitstream` in `build-perf` (WITHOUT that define you get
66.67 MHz and every number is wrong).

**The three things most likely to waste a future session:**

1. **The sim cannot run the board's geometry** ([[PUMICE-028]]). The core suite
   is BL8 / 64-bit beat / device == beat, so one DRAM burst is FOUR bus beats
   and any per-sub-command rate limit is divided by four before a bandwidth
   assertion sees it. That is precisely how a 2x read throttle shipped green.
   If a board number and a sim number disagree, suspect this FIRST.
2. **Two writers is unsafe in the char harness** ([[PUMICE-027]]). pumice
   returns B out of AW order across masters; the generated write bridge routes
   by FIFO position. Single-writer results are fine. Do not "fix" the bridge
   without deciding whether pumice should guarantee AW-ordered B instead.
3. **The spec collateral dates instantly.** The design/ tables and waves were
   written mid-campaign and asserted a 15%-of-peak controller with five live
   defects long after the board reached 95%. Both halves are now gated
   (`docs/check_kmap_rtl_sync.py`, `design/check_waves.py`) and the generators
   refuse to emit on failure -- but the gates only cover what they cover. Date
   every claim, or re-run it.

**Known-open performance items, none blocking:**
* Read latency ~49 cycles vs LiteDRAM's 24.7 -- now filed as [[PUMICE-030]],
  the largest identified defect left. It also explains the small-burst read
  shortfall (AxLEN 1/2/4 at 16/31/60% of peak): Little's law against the read
  generator's 8-burst budget, five points predicted within 2%.
* The three runtime axes are characterized but NOT tuned -- nobody has picked
  defaults per workload class from the sweep ([[PUMICE-013]]).
* Area: pumice_top is 12 224 LUT / 7 878 FF, ~5x LiteDRAM's controller+PHY for
  equal streaming bandwidth. That is the deliberate research-controller trade
  and is now stated at the top of AT-A-GLANCE.md; it is the obvious target if
  anyone ever wants a product part.

**Operational traps that cost real time here:**
* `PUMICE_SYS_75=1` or the build is 66.67 MHz.
* `ddr2_char_macro` did not thread `RD_RET_DEPTH`; board default is now 64 via
  `PUMICE_RD_RET_DEPTH`. Check a parameter is actually PASSED before believing
  the flow sets it.
* `ddr2_char.num_gen` defaulted to 1 while the board carries 2 per direction.
  Call `sync_gen_config()`; never trust a hardcoded count.
* The char-framework sim is the board gate before any pumice RTL commit
  ([[PUMICE-023]]).

Related: [[project_pumice_read_ceiling_fixed]],
[[project_litedram_same_harness_ab]], [[project_pumice_char_suite]].

---

## PUMICE-028 — the pumice sim has never run the board's DRAM geometry
**Status:** open 2026-09-10  **Priority:** P1 — this is why a 2x read throttle shipped green

`dv/tests/top/test_pumice_core_dfi.py` ran at DRAM_BEAT=64 / BL8 / device==beat,
so **one DRAM burst is 4 AXI beats**. The board is DRAM_BEAT=32 / BL4 / x16,
where **one DRAM burst is 1 AXI beat**. Any per-sub-command rate limit is
therefore divided by four before a bandwidth assertion can see it: the read
intake's admit gate (PUMICE-025, fixed) supplied 2 beats/cycle at the sim
geometry and looked healthy, while on the board the same gate WAS the
bandwidth. Every read/write ceiling test passed throughout.

The geometry is now env-overridable (`TEST_DRAM_BEAT` / `TEST_DRAM_BL` /
`TEST_DRAM_DEVICE_W`, defaults unchanged) and `pumice_core_tb_top` takes
`DRAM_DEVICE_WIDTH`. **But the board point does not yet run clean**, so it is
not wired into the suite:

- `read_ceiling` at board geometry trips `pumice_dfi_rd_return_checker` --
  "32 reads outstanding for 512 cyc with no return".
- `write_ceiling` at board geometry stalls W for 1409 cycles (max run 19),
  while the real board sustains 95% of peak on writes. So the failure is the
  testbench or its DFI model, not the DUT.

**Do:** make `TEST_DRAM_BEAT=32 TEST_DRAM_BL=4 TEST_DRAM_DEVICE_W=16` a clean,
routinely-run configuration of the core suite (the write ceiling is the
control: it must reproduce the board's ~95%), then add it to the regression so
board geometry is covered by default. Until then `[[project_pumice_char_suite]]`
board numbers are the only place these limits are visible.

**Why it matters:** the handbook rule is already "match the FPGA exactly in
sim"; this is the case that proves the cost of not doing it. A suite that
cannot express the shipping geometry cannot gate it.

---

## PUMICE-027 — write responses leave pumice out of AW order; the char write bridge routes B by position
**Status:** open 2026-09-10  **Priority:** P2
**Found by:** `test_ddr2_char_macro[bank_parallel]` (the only multi-writer scenario), once the
macro suite could compile again (the `-Wno-PINMISSING` waiver for the bridge regen's
`unmapped_*` ports). Fails identically on HEAD's inline macro and on the extracted
`char_engine_block`, so it predates the refactor.

**Symptom:** `pumice_wr_adapter.sv:168` BRIDGE-010 `$error` at ~31 us: "slave returned B out of
AW order".

**Be precise about where the gap is — the per-generator B handling IS built and
is correct.** `bridge_ddr2_char_wr_xbar.sv:222-224,413-415` steers B to the
owning master by `bid_bridge_id` and gates each master's `bready` so only the
owner's ready reaches the slave; the master-side adapters pass their own B
through. That is exactly the queued-B, per-generator-ready design, and none of
it is the problem.

The problem is the **KEY the ownership lookup indexes on**. `pumice_wr_adapter.sv:99-129`
pushes the issuing master's `bridge_id` into `wr_fifo` at AW accept and reads it
at the HEAD: `bid_bridge_id = wr_fifo[rd_ptr]`. So "who owns this B" resolves to
"whoever issued the OLDEST outstanding AW", not "whoever issued the AW whose ID
this B carries". When pumice returns B out of AW order the head names the wrong
generator, and then the otherwise-correct per-master handshake completes cleanly
against it. The steering works; it is aimed by position.

Worth noting for the fix: the adapter ALREADY records the AWID per slot
(`wr_id_fifo`, :156) — but only inside `ifndef SYNTHESIS`, purely to drive this
assertion. The information needed to route by ID is being captured in
simulation and thrown away in synthesis. Routing by ID means searching the FIFO
for the matching entry instead of taking the head, i.e. a small CAM over
`WR_FIFO_DEPTH`. pumice's write CAM commits in FR-FCFS order (oldest schedulable per row, not
global AW order), so with two writers interleaving, a younger writer's B can come back before an
older one's. The check is sim-only (`translate_off`); on the board the B would silently reach the
WRONG generator (its bresp/count is credited to the other gen). AXI4 permits the slave's
reordering between IDs, so this is a system contract gap, not a protocol violation.

**Not affecting the numbers taken so far:** every board characterization run drives generator 0
alone (one writer, one reader), where position routing cannot misroute. Only bank_parallel /
multi-generator runs are exposed.

**Fix options (decide, do not patch blind):**
1. pumice: return B in AW order -- the write-side twin of `pumice_rd_return_ring` (the read
   path already holds R returns to AR order). Costs a small ticket ring; keeps the bridge
   position-routed as generated.
2. bridge: regenerate `bridge_ddr2_char_wr` with ID-based B routing (each generator already
   owns a distinct AWID space in bank_parallel). The converters/bridge family is in-order by
   design, so this is a generator feature.
3. Test-only: run bank_parallel with `SCHED_POLICY.order_mode=1` (in_order) -- confirms the
   mechanism, does not fix the board exposure.

Of the three, (2) is the smallest change and matches what the crossbar already
wants to do: the per-master steering and ready gating stay exactly as they are,
only the lookup changes from "head of the FIFO" to "the entry whose AWID equals
this BID". Option (1) is the bigger statement -- it would make pumice's write
responses AW-ordered like its reads, which is a controller guarantee rather
than a harness fix and would suit any position-routed interconnect downstream.

Also note the BRIDGE-010 message prints the ID strings garbled (`%0h` applied to the message
continuation) -- cosmetic, in the generated adapter template.

---

## PUMICE-026 — finish the LiteDRAM same-harness A/B (it is already ~80% built)
**Status:** open 2026-09-10  **Priority:** P2
**Intent (Sean):** "drop liteddr into the pumice harness so testing is the same."

**START HERE, DO NOT REBUILD:**
`projects/fpga-systems/NexysA7/pumice/ddr2-characterization/flows-litedram-uart/`

That flow already exists and is documented as **WIRED** in its `HARNESS_PLAN.md`:

- `rtl/char_engine_harness.sv` — DUT-agnostic harness (engines + perf meters +
  bandwidth timer + harness_csr + UART bridge) exposing an AXI4 master.
  Verilator-lint-clean standalone.
- `rtl/litedram_char_top.sv` — board top: `litedram_core` + the harness on
  `user_clk`, `init_done`-gated, AXI user port wired.
- `rtl/filelists/litedram_char_harness.f`, `constraints/litedram_char.xdc`,
  `tcl/build_all.tcl`, `tcl/program_fpga.tcl`, `Makefile`, `regen.sh`,
  `litedram_hp.yml`, and a generated `build_board/gateware/litedram_core.v`.
- A `litedram_hp.yml` deliberately mapped onto a high-perf pumice preset, with
  the mapping table written out in its README.

**Progress 2026-09-10 (commit fdaa7db37):**
- ~~regen with BIOS~~ **DONE.** Core regenerated with a functional BIOS (63 KB
  ROM) and `litedram_hp.yml` moved to **75 MHz / 1:2 / 300 MT/s**, matching the
  point pumice is measured at. The stock 100 MHz / 1:4 would have voided the
  comparison.
- ~~XDC reconcile~~ **NOT NEEDED.** The regenerated core xdc has no ddram pins;
  the harness keeps its pin map.
- Five flow bugs fixed to get synthesis running: `REPO_ROOT` two levels short
  (the `../` count was correct at the pre-move path), `CONVERTERS_ROOT` not
  exported, the tcl filelist reader expanding only `$REPO_ROOT`, `.vlt` lint
  waivers handed to Vivado, and `VexRiscv.v` pinned to a path inside the LiteX
  venv. `regen.sh` no longer hardcodes a `/tmp` venv either.

**DONE 2026-09-10 — measured.** Timing-clean LiteDRAM bitstream (WNS +0.195, after
adding the core's CRG reset-strobe false path), `--char-profile matrix --char-scale 1000`,
14/14 integrity, saved as `docs/char_results/litedram_2026-09-10_matrix.csv` with the
write-up `FINDINGS_litedram_ab_2026-09-10.md`. Headline: LiteDRAM reads 564-579 MB/s
(94-97% of peak) through the identical harness where pumice reads 291.7; writes equal
(~554-569 vs 551-570). The read ceiling is pumice's, not the operating point's -- see
PUMICE-025. Ready to close (move the block to closed.md).

**Progress 2026-09-10 (later) — item 0 DONE, harness matches build-perf:**
Sean asked for the LiteDRAM harness to match the current one; the chosen
route was to extract a shared engine block. `char_engine_block.sv` (chargen
regs + generator array + crossbars + perf, one AXI4 master) is pulled out of
`ddr2_char_macro.sv`, which now wraps pumice around it; `char_engine_harness.sv`
is build-perf's `ddr2_char_harness` minus the controller (same UART bridge,
same `bridge_ddr2_char_axil` address map with `ddr2_apb` terminated, same
`harness_csr` with BUILD_ID "LDR2", same timer/LEDs). `make lint` clean;
Makefile on `make/fpga_flow.mk`; `host/host_litedram_char.py` is the pumice
host with the pumice-CSR surface as no-ops. `FPGA_CLK_HZ` in the top was still
100 MHz after the 75 MHz regen (UART divisor wrong) -- fixed. Bitstream build
in flight; then program, `--char-profile matrix --char-scale 1000`, save CSV.

**Was BLOCKING (now resolved as above).** Synthesis reached the harness and
stopped on **41 port mismatches**: `char_engine_harness.sv` is wired
to a `harness_csr` that no longer exists. The whole per-generator config
surface (`o_cfg_wr_*`, `o_cfg_rd_*`, the start pulses, the CRC readback) moved
out of `harness_csr` into `chargen_regs` when the char framework went to a
16-generator array; `harness_csr` is now 75 ports of global/PHY config only.

Rewire `char_engine_harness.sv` against the current framework — `harness_csr`
for the global surface, `chargen_regs` (`chargen_regs.rdl`) for per-generator
config, and the generator array instead of one wr + one rd engine. The pumice
flow's `ddr2_char_macro.sv` is the reference for how the array is driven today.

Then: host variant (copy `ddr2_char.py` + `pumice_master.py`, drop the
pumice-CSR `set_controller_cfg` writes since LiteDRAM self-configures, keep
engine cfg + perf/timer readout; `harness_csr` is at base 0 here), then
`make bitstream && make program && make characterize`.

**RESOLVED 2026-09-10:** `build-litedram/` was an empty duplicate scaffold
(the never-executed destination of a NEXYS-003 move). It cost this session a
rebuild-from-scratch of the LiteX tooling before the real flow surfaced. It is
now DELETED and every reference points at `flows-litedram-uart/`.

**Tooling notes that ARE new and worth keeping** are in
`flows-litedram-uart/2026-09-10_tooling_notes.md`, with two working scripts
beside it (`bin_nexys_bist_soc.py`, `bin_litedram_bist_run.py`): install LiteX
from git not PyPI (PyPI +
Python 3.12 breaks every target on a migen bytecode-inference bug); the RISC-V
toolchain is already at
`/tools/Xilinx/2025.1/gnu/riscv/lin/riscv64-unknown-elf/bin`; PyPI
`pythondata-software-picolibc` ships incomplete sources so the BIOS build
fails; and `--cpu-type=None` yields a clean timing-met bitstream whose BIST
returns garbage because LiteDRAM's DDR2 init and levelling live in the BIOS.
That last point is why item 1 above says `--bios`.

**Why it matters:** LiteDRAM's read is also ~47% of the raw ceiling while its
write reaches 88%; pumice is at 48.6% / 95.0%. Two independent controllers at
the same read fraction on the same board is the strongest evidence that the
read ceiling is a property of this operating point rather than a pumice defect
(PUMICE-025). Same-harness confirmation would redirect or justify that work.

## PUMICE-025 — read bandwidth was pinned at 48.7% of peak (FIXED: now 95%, write parity)
**Status:** open 2026-09-10  **Priority:** P1 — the last gap to the 450 MB/s read target
**Found by:** PUMICE-022 board characterization (see closed.md for the full table)

Read bandwidth on silicon is **291.7-292.2 MB/s against a 600 MB/s peak** and
does not move with burst length, access pattern, paging mode or scheduling
mode. Write on the same runs reaches 574.0 MB/s (95.7% of peak).

**What the invariance rules out.** bl4 / bl8 / bl16 measure 290.8 / 291.7 /
291.7 -- identical. If the limit were the number of transactions in flight
(generator `GEN_MAX_OUTSTANDING`, ring `RD_RET_DEPTH`, or a Little's-law
round-trip bound) then doubling the bytes per transaction would raise
bandwidth. It does not, so the limit is a per-cycle rate below the transaction
layer, not a concurrency limit. Read latency is a flat 49.2 cycles throughout.

**2026-09-10 ROOT-CAUSED AND LARGELY FIXED: the read intake admitted one
sub-command every TWO cycles.** `pumice_rd_intake` held a single `r_armed` bit
on the AR skid head to mark "the registered snarf probe belongs to this AR".
The bit was cleared by its own admit and could only be re-set the cycle after,
so admits were capped at 0.5/cycle. One admitted sub-command is exactly one
DRAM burst, and on this board (BL4 on x16, 32-bit beat) one burst is ONE AXI
beat -- so the gate was the bandwidth: 0.5 x 8 B x 75 MHz = 300 MB/s, against
291.7 measured (97% of it). Writes have no such stage (`pumice_wr_intake`
runs AW straight from the meta-FIFO head) which is the entire read/write
asymmetry.

Fixed by staging the AR: the skid head is the AR being probed, a new stage
holds the AR being admitted, and the two advance together (1 admit/cycle).
While the stage is held the probe re-points at the stage, so the hit driving
an admit is never more than one cycle old -- the same RAW-forwarding exposure
the arm bit had, rather than a latched hit that would go stale.

Board result (`board_2026-09-10_read_intake_fix.csv`, 14/14 integrity):

| scenario | read before | read after |
|---|---|---|
| row_major_bl8 | 291.8 | **470.9** |
| row_major_bl16 | 291.8 | **471.0** |
| incremental_bl8 | 291.7 | **463.7** |
| row_major_bl4 | 290.8 | **360.4** |

48.6% of peak -> 78.5%. Writes unchanged (551/570). Timing IMPROVED: WNS
+0.285 ns vs +0.039 before, 0 failing of 94060; area +102 LUT / +35 FF.

**SECOND LIMIT, ALSO FIXED: the read return ring was 32 tickets and the board
build never even set it.** `ddr2_char_macro` did not pass `RD_RET_DEPTH`, so
every board bitstream ran the controller default of 32 regardless. Sustained
read rate is bounded by depth / (ticket alloc -> R drain), and this board's PHY
read latency is ~49 MC cycles, so 32 tickets cap reads near 0.78 of the DRAM
rate -- exactly the 78.5% left after the intake fix. Threaded the parameter
from `ddr2_char_top` through the harness and macro, exposed
`PUMICE_RD_RET_DEPTH` as a build define, and set the board default to **64**.

Board sweep (`board_2026-09-10_read_fixed_ring64.csv`, 14/14 integrity):

| scenario | read @ ring 32 | read @ ring 64 | write |
|---|---|---|---|
| row_major_bl8 | 470.9 | **571.3** | 570.2 |
| row_major_bl16 | 471.0 | **571.3** | 570.3 |
| incremental_bl8 | 463.7 | **556.9** | 551.3 |
| row_major_bl4 | 360.4 | 360.4 | 570.3 |

**Reads now match writes** (571.3 vs 570.2, both ~95% of the 600 MB/s peak) and
are within 1.4% of LiteDRAM's 579.5 through the same harness. Timing +0.283 ns,
0 failing of 94415; ring 64 costs ~158 LUT over ring 32.

**2026-09-10 CONCURRENT LOAD -- the workload where pumice's area pays off.**
Every measurement before this ran a write phase then a read phase, so
read/write turnaround was never paid. Running both directions in one window
(new `concurrent` / `multigen` profiles, disjoint regions, both controllers
through the identical harness):

| scenario | pumice total | LiteDRAM total | ratio |
|---|---|---|---|
| row_major bl8, 1w+1r | **570.1** | 285.6 | **2.00x** |
| incremental bl8, 1w+1r | **552.6** | 247.5 | **2.23x** |
| row_major bl8, 1w+2r | **570.2** | 316.4 | **1.80x** |

pumice holds 95% of peak with one, two and three concurrent generators;
LiteDRAM sits near half peak and its read latency rises from 24.7 to 94.5
cycles on incremental. The global FR-FCFS window batches same-direction
columns and amortises tWTR/tRTW; per-bank round-robin pays it per switch.
Files: `board_2026-09-10_{pumice,lite}_{concurrent,multigen}.csv`.

Not measurable this way: `col_major` / `col_major_interleaved` span the whole
device so generators cannot be placed adjacently, and those rows fail
integrity on BOTH controllers (the wrapped-walk hash artifact `strides_for`
documents). `incremental` under multigen likewise falls back to a far-apart
split that measures page thrash. Only bounded-wrap families place adjacently,
so row_major is the trustworthy multi-generator row.

**What is left.** AxLEN=4 still reads 360.4 while writing 570.3, and it did not
move with ring depth, so it is a third and separate mechanism (per-AR overhead
rather than per-column). Read latency is also still ~49 cycles against
LiteDRAM's 24.7 -- bandwidth is fixed, latency is not. Neither blocks the
bandwidth target; track them here rather than reopening the ceiling story.

**(Earlier) SAME-HARNESS A/B DISPROVED THE OPERATING-POINT THEORY BELOW.** LiteDRAM
behind the identical `char_engine_block` / bridge / host, at the identical 75 MHz / 1:2 /
MR0=0x0432 (BL4, CL3) point, reads 564.1 (incremental) / 579.5 (row_major) MB/s and
writes 554/569 -- `docs/char_results/litedram_2026-09-10_matrix.csv`,
`FINDINGS_litedram_ab_2026-09-10.md`. So a column every MC cycle IS sustainable on
this bus for reads: the 48.6% ceiling is pumice's read command path, not BL4. Writes
already match LiteDRAM, which localises it to AR-accept -> column-issue -> R-return
(return ring / rd CAM / AR-order commit). LiteDRAM's read latency is 24.7 cycles vs
pumice's 49.2: ~25 cycles of extra pipeline per access is the other half of the same
story. The analysis below stands as the description of the write path; its
conclusion about reads does not.

**(Superseded framing) Burst length is the fundamental constraint, and it is NOT read-specific.**
The board runs BL4 (host forces `MR0=0x0432` and `bl=4`; the RDL default is
BL8/0x0433). On a x16 device BL4 is 4 transfers = 8 bytes, and 4 transfers at
300 MT/s is 2 CK = exactly ONE MC cycle at 75 MHz. So sustaining 600 MB/s
demands a column command EVERY MC cycle, on a single-issue command bus: 100%
of command slots must be columns, leaving ZERO for ACT, PRE or REF. Every
activate or precharge costs a full column slot -- 8 bytes -- one for one. That
is why the measured split is binary (570 page-open vs 34 page-closed) with
nothing in between, and it caps how much any scheduler can ever recover.

BL8 would halve the command pressure: 16 bytes per column, each burst
occupying 2 MC cycles, so a column every OTHER cycle saturates and the other
half is free for ACT/PRE/REF. That is the single biggest architectural lever
available and it is worth a build.

**Runtime BL8 does NOT work and needs a rebuild.** Tried 2026-09-10 with
`TEST_MR0=0x0433 TEST_DRAM_BL=8` on the BL4 bitstream: a 16 MB memtest passed
4/4 clean, but the characterization workload was **0/8 integrity** and
bandwidth did not move. The simple memtest is not a sufficient check for this
change. `DRAM_BL` is a compile-time parameter in `ddr2_char_top.sv`
(BURST_LEN_MULTIPLE, harness sizing, column stride) as well as a runtime CSR,
so BL8 requires rebuilding the bitstream with `DRAM_BL = 8`, not just an MR
write. Board was restored to BL4 and re-verified clean afterwards.

But note that BL4 does NOT explain the read/write asymmetry: both directions
need the same one-column-per-cycle rate, and writes achieve 95% of it while
reads achieve 49%. The asymmetry below is still an implementation property.

**Hypothesis:** the read return path delivers one AXI beat every other cycle
where the write path delivers one per cycle. 292/600 = 48.7% is close enough to
exactly half to be worth confirming. With the generator ruled out (below), the
limit is inside the controller's return path. Candidates:
1. ~~The char harness's read CRC-check engine consuming R at half rate.~~
   **RULED OUT 2026-09-10 by measurement.** `axi4_master_rd_crc_check` at fub
   level, across all seven slave timing profiles, holds `rready` asserted on
   **100% of run cycles** (140/140, 269/269, 388/388, 325/325, 201/201,
   1925/1925 ...) with a back-pressure count of **exactly zero** in every
   profile, and transfers 128/128 beats each time. With a backtoback slave
   every beat-to-beat gap is 1 cycle. The generator never throttles R, so the
   ceiling is NOT in the harness. Guarded permanently by the
   `rready_never_throttles` scenario in
   `val/amba/test_axi4_master_rd_crc_check.py`.
2. `pumice_rd_return_ring` drain -- one beat per cycle through the BRAM skid
   vs. the write path's rate.
3. `pumice_dfi_rd_aligner` / `pumice_dfi_cdc` read FIFO width or pop rate.
4. `pumice_rd_intake` R-channel assembly.

The latency view (`rtl/schematics/gen_latency.py`) prints per-path flop counts
and names the combinational feedthroughs for each of these blocks, which is the
fastest way to compare the read and write drain structures side by side.

Do NOT start by tuning the scheduler: every scheduling and paging mode gives
the identical 291.7, so the scheduler is not the constraint.

## PUMICE-006 — QoS + advanced scheduling (post-cleanup)
**Status:** MECHANISMS COMPLETE 2026-08-27 — all three axes implemented
(Axis 1 scheduling, Axis 2 paging, Axis 3 refresh), every mode OFF by
default and mutation-proven. Characterization/tuning split to
[[PUMICE-013]]. Holds open only for mechanism gaps 013 reports back.

**Progress:**
- Step 1 (e64c824b): full mode-select CSR surface + *_STATS telemetry
  registers, defaults bit-identical.
- Axis 2 partial: `pumice_page_policy` fub — modes 1/2 (static ap override),
  3 `fixed_open` (per-bank idle-timeout close via a new lowest-priority
  arbiter PRE branch, JEDEC-gated like the conflict-PRE path) and
  4 `adapt_time` (Happy adaptive-timeout TR/MC walk) + the always-on page
  hit/miss/empty + ACT/PRE/REF counters feeding the *_STATS CSRs.
  Directed test `test_pumice_core_fixed_open` is self-checking both ways
  (mode-0 inertness arms) and mutation-proven (w_timeout_on=0 → RED).
- Axis 2, modes 6/7 `rbl_static`/`rbl_dyn` landed: new `pumice_rbl_table` fub
  (per-set-associative row miss-counter table, tag=row, true-LRU, runtime
  ways/sets shape from PAGE_RBL_CFG, epoch counter clears, mode-7 divider-free
  hill-climb on hit fraction with direction memory). Verdict latched per bank
  at ACT time → page_policy turns the mask into per-bank auto-precharge.
  Directed `test_pumice_core_rbl`: arm A mode-0 thrash baseline, arm B
  thresh=2 static (conflict-PRE suppression < half of baseline + friendly-row
  zero-reACT check), arm C dyn smoke + disarm. Mutation-proven (verdict
  forced 0 → arm B RED: 13 vs 11 PREs, no suppression). Gate tier after:
  fub 40 / macro 3 / top 57.
- Axis 2, mode 5 `adapt_access` landed — AXIS 2 COMPLETE. New
  `pumice_row_pred_table` fub (Happy "Hybrid"): tagless direct-mapped 2-bit
  saturating counters, {bank, XOR-folded row} index; explicit-PRE closes teach
  from accesses-per-activation (<=1 -> close-friendly, >=2 -> open-friendly),
  auto-precharge closes are judged by same-row premature reopen (decrement).
  PAGE_POLICY_CFG.ctr_open_max/ctr_init wired (0 = defaults 2 / weak-open 1;
  init applies while the mode is disabled). LESSON captured in the RTL
  comment: the scheduler's exported row-active bit clears at PICK time, a
  cycle before the PRE issues — the first cut guarded PRE-learning on
  row-active and learned NOTHING (found via $display trace, "PRE bank=4
  act=0"); the open-row IMAGE stays valid, the active bit does not.
  Directed `test_pumice_core_acc` (single-access thrash — a write+read pair
  is 2 accesses and correctly teaches OPEN, so the rbl thrash pattern does
  not transfer): mode-0 baseline, mode-5 suppression < half, golden readback,
  friendly-row zero-reACT, ctr_init=3 cold-table <=1 PRE, disarm. Mutation-
  proven (verdict forced 0 → arm B RED: 12 vs 11 PREs).
  MAS 08_page_policy / design-requirements / HAS open-issue 5 updated to the
  as-built modes 5/6/7.
- Axis 3 step 1: REF_CTRL postpone/pullin JEDEC +-8 credits landed
  (refresh_ctrl v3). Backlog + pull-in credit as one next-state evaluation;
  postpone clamped to 7 so the saturating-8 backlog always forces under
  demand; pull-in runs ahead only on CONFIRMED idle (16-cycle hysteresis
  over scheduler CAM occupancy — micro-gaps must not release postponed
  refreshes). TWO integration traps found and fixed in the same change:
  (1) drain_active gated on refresh_req_o, else the arbiter's drain
  preemption defeats postponement entirely; (2) the tREFI counter reloads
  only on expiry, so a runtime t_refi poke takes effect after the STALE
  period elapses once (test waits it out — this also bit the first test
  run as a false "refresh gated" red).
  Directed test_pumice_core_refresh_credit (timed demand windows, not
  write counts — 40 b2b writes span <2 ticks): strict red-guard, postpone
  zero-leak + forced ceiling + drain conservation, pull-in run-ahead +
  refresh-free demand window + golden readback, disarm. DOUBLE
  mutation-proven: postpone gutted -> arm B RED (6 leaked); pull-in
  gutted -> arm C RED (tick-rate only).
- Axis 3 step 2: refpb_rr landed (REF_CTRL.mode=2, LPDDR2-only with DDR2
  degrade + perbank_supported strap). RDS-DV model first (041ddc3):
  dram_state.on_refresh_bank with device-internal rotor, per-bank tRFCpb
  recovery, bank-aware cmd_during_refresh (other banks accessible), 6 unit
  tests; slave routes decoded all_banks=False to it. RTL: arbiter 2b branch
  (PRE rotor bank only -> OP_REFPB; rank-wide-ACT-block-during-tRFCpb
  conservative v1), refresh_ctrl tREFIpb mux + rotor mirror.
  TWO REAL BUGS found by the directed test's zero-data reads:
  (1) LATENT DOUBLE-ISSUE: every refresh fired TWICE (grant->req-drop is
  2 cycles; the 2nd command registers before rfc_busy loads). Benign-
  looking for REFab (a silent tRFC-between-REFs violation, present in
  every prior build INCLUDING board bitstreams) but fatal for REFpb —
  each command advances the device rotor -> mirror desync -> wrong-bank
  precharges -> rows silently closed -> no_act_before_rd zero reads.
  Fix: !r_grant in w_ref_safe/w_refpb_safe.
  (2) rotor-mirror sampling: grant fires at the arbiter's FIFO-PUSH, so
  grant_was_pb must sample the ARBITER-side a_cmd_op, not cmd_op_o (the
  FIFO HEAD = an older command; sampling it stalled the mirror).
  LESSON: the fub arbiter test's refresh poll (2-edge settle stride) had
  been passing BECAUSE of the double-issue — the bug kept REF visible for
  two cycles and the sampler always caught the second one. Single-issue
  made the 1-cycle REF invisible to the stride; the poll now samples
  every edge. A test that samples slower than the event it checks can be
  green only in the presence of the bug it should catch. (The SAME
  stride bit AGAIN in the Axis-1 fub arm: with static vectors the picks
  alternate RD/ACT at period 2 and settle()'s 2-edge stride phase-locked
  onto the non-RD cycle — hours chasing phantom "livelocks" before the
  mask probe showed the RD firing all along. Order-mode polls are now
  per-edge too.)
  Directed test_pumice_top_refpb (LPDDR2 top TB): strap check, REFab
  red-guard (refpb_total==0), full rotation >=8, BFM traffic golden
  THROUGH the refpb stream, zero refresh-class model violations, disarm.
  Mutation-proven: mode gate gutted -> arm B RED (0 REFpb).
  AXIS 3 REMAINING: none in the commodity plan (per-bank ref_credit
  steering + ACT-during-tRFCpb overlap are cataloged optimizations).
  ALSO NOTE: the editable RDS-DV install was silently replaced by the
  0.6.5 wheel at the release pin-bump — [[reference_dv_framework_repos]]
  has the recovery (rm the site-packages copy, pip install -e, verify
  __file__).
- Axis 1 step 1: ORDER_MODE landed (SCHED_POLICY.order_mode 1=in_order /
  3=age_threshold + age_thresh; 0/2 = FR-FCFS default). CAMs export a
  per-entry 1-bit aged flag + head relative age (numeric ages never leave
  the CAM); the arbiter overlay only NARROWS the FR-FCFS class masks.
  A REAL PRE-EXISTING BUG found by the directed test's parked-victim
  pattern (same-bank conflict read held while row-hits stream): a
  conflict-PRE fires in a column-readiness gap, then a COLUMN picks
  against the 2-cycle-stale row-open image and lands on the closed row —
  its data never returns and the rd reorder CAM's AR-order drain WEDGES
  forever (rd-return checker DROP). Reproduced on pristine HEAD RTL
  (bisect harness), latent since the bank-parallel refactor. Fix =
  PRE-only THREE-cycle column guard (w_pre_col_guard; PRE-only because
  the general w_guarded also covers RD/WR fires and would throttle
  same-bank column streaming — the first broad fix broke the fub
  CLOSE->WRA arm; three deep because the bank image is up to 3 cycles
  stale end-to-end and the 2-deep version still wedged).
  A SECOND pre-existing bug behind the residual deterministic wedge: the
  DFI READ-RETURN PATH SILENTLY DROPPED BEATS — dfi_rddata_valid is
  fire-and-forget (no PHY backpressure) and the rd aligner forwarded
  beats into the return CDC FIFO with ready gating only its capture
  counter; a beat arriving while the 16-deep FIFO was full was simply
  gone (probe: 4 beats lost), the burst went short, and the AR-order
  drain wedged behind it. Fix = RD_FIFO_DEPTH 16 -> 32 (sizing contract:
  the return FIFO must cover the whole admission domain = rd-CAM depth x
  BL_WORDS = 32 beats) + a HARD ASSERTION in the aligner so any future
  valid-with-full cycle is an $error, never silent data loss.
  TWO design lessons: (a) the rd reorder CAM releases AXI reads in AR
  order BY DESIGN, so completion order at the core level can NEVER show
  scheduling differences — order-mode semantics are verified at the FUB
  arbiter level (hand-driven vectors, scenario 11), the core test is the
  wedge/integrity sentinel across modes; (b) age_threshold's boost must
  trigger on the aged entry's EXISTENCE, not its candidacy — a
  guard-blocked PRE never becomes a candidate while the competing column
  keeps firing and re-arming that same guard (self-sustaining starvation
  of the anti-starvation mechanism). Mutation-proven (overlay gutted ->
  in_order arm RED).
- Axis 1 step 2: ROW_SEL/COL_SEL most/fewest_pending landed
  (SCHED_POLICY.row_sel/col_sel). Per-entry pending population = 8x8
  same-{bank,row} match triangle per CAM (the paper's "expensive
  counters" are trivial at CAM depth 8); arg_sel picks population-first
  with OLDEST tie-break, composing under the ORDER_MODE narrowing;
  row_sel steers ACT, col_sel steers COLUMN, PREs stay oldest. Fub
  scenario 12 (hot-row-vs-lone-old vectors, per-edge polls) proves all
  three encodings both directions; mutation (selector forced to oldest)
  -> RED by drain-loop timeout. Core sentinel sweep extended with
  most/most + fewest/fewest arms.
- Axis 1 step 3: ACCESS_PREF landed (SCHED_POLICY.access_pref: 0/1
  column_first = legacy order bit-identical, 2 row_first, 3
  precharge_first). Class chosen first from the (ORDER_MODE-narrowed)
  per-class picks, read-over-write within. TESTING LESSON: the first fub
  scenario (poll-for-op over static self-refilling vectors) PASSED ITS
  OWN MUTATION -- fired picks arm guards, the preferred class blanks a
  cycle, and every class appears in the alternation, so any op is
  findable under any preference. Rewritten as ONE-SHOT candidates with
  FIRE-ORDER asserts (deterministic total order per preference) + a
  4-cycle inter-arm pipeline flush (registered picks straddle arm
  boundaries and get booked to the wrong arm). Mutation now properly
  RED (pref dead -> column-first order under the row_first arm).
- Axis 1 step 4: write batching landed (SCHED_WR_WM.wr_high_wm/wr_low_wm
  hysteresis on wr-CAM schedulable occupancy; while draining, writes
  outrank reads in every class; 0 = disabled bit-identical). Fub
  scenario 14 (fire-order: wm off -> RD first; 3/1 -> two WRs front-run
  the read), mutation-proven (drain forced off -> RD-first RED).
- Axis 1 step 5: prio_sub landed (SCHED_POLICY.prio_sub: 0/2
  load_over_store default bit-identical, 1 none = per-fire direction
  toggle, 3 age_boost = an aged write winner pierces read priority via
  the age_thresh flags). Per-class write-first decision with precedence
  drain > prio_sub. Fub scenario 15 (fire order: default RD-first,
  none = both fire, age_boost aged-WR-first + unaged RD-first),
  mutation-proven (decode dead -> age_boost arm RED).
- Axis 1 step 6: QoS landed (SCHED_POLICY.qos_en) — AXIS 1 COMPLETE.
  AxQOS now carried AR/AW -> intake -> CAM entry -> per-entry sch_qos
  vector (it previously died at the burst chopper); with qos_en each
  class narrows to its max-QoS candidates BEFORE the population/oldest
  select, making QoS the outer key with the existing selects as the
  inner tie-break. Fub scenario 16: qos_en=0 picks the oldest (slot 5),
  qos_en=1 picks the OLDEST OF THE MAX-QOS SET (slot 6, not the younger
  slot 7) — proving both the outer key and the surviving age tie-break.
  Mutation-proven (narrowing dead -> picks slot 5, RED).
  ALL of PUMICE-006's three axes are now implemented: Axis 1
  (scheduling), Axis 2 (paging), Axis 3 (refresh).
  **MECHANISM WORK COMPLETE 2026-08-27.** Characterization and tuning of
  the landed modes is a large body of work in its own right and moved to
  [[PUMICE-013]] (Sean, 2026-08-27). 006 now covers only the RTL
  mechanisms + their directed/mutation-proven mode tests; it closes when
  013 has no mechanism gaps to report back.
- Direction (Sean, 2026-08-25): RETIRE the legacy HAPPY_HYBRID predictor —
  the new Happy-derived modes are its successors; docs to describe the
  actual implementation.

The original framing ("once pumice is CLEAN, layer in the sophisticated
features") is satisfied: the advanced-mode catalog in
`projects/components/memory-controllers/ADVANCED_MODES_ROADMAP.md` and the
design-requirements doc (FR-FCFS variants, paging/refresh policy modes, QoS)
is implemented end-to-end, each mode OFF by default with encoding 0 = build
default and every mechanism mutation-proven at the fub level.

**Entry gate (met):** tiny-tREFI soak 0-dirty on the rebuilt bitstream
(PUMICE-004).

---

## PUMICE-013 — characterize + tune the advanced modes (all three axes)
**Status:** open 2026-08-27 (split out of PUMICE-006 at Sean's direction —
"move characterization to its own task as that is a big one")

PUMICE-006 delivered the MECHANISMS: every mode of all three axes is
implemented, OFF by default (encoding 0 = build default, bit-identical),
and mutation-proven at the fub level. What it deliberately did NOT do is
answer *which settings are actually good* on real traffic. That is this
task, and it is a large body of work: a mode-cross characterization
campaign in sim and on the board, plus the tuning defaults that come out
of it.

**The surface to sweep** (all runtime CSR, no rebuilds):
- **Axis 1 (scheduling)** — `SCHED_POLICY.order_mode` (in_order /
  fr_fcfs / age_threshold + `age_thresh`), `row_sel` / `col_sel`
  (oldest / most_pending / fewest_pending), `access_pref` (column /
  row / precharge first), `prio_sub` (load_over_store / none /
  age_boost), `qos_en`, and `SCHED_WR_WM.wr_high_wm/wr_low_wm`.
- **Axis 2 (paging)** — `PAGE_POLICY_CFG.policy_mode` 1..7 with
  `PAGE_TIMEOUT_CFG` (fixed_open/adapt_time TR bounds + step),
  `PAGE_ADAPT_CFG` (MC thresholds, check interval),
  `PAGE_POLICY_CFG.ctr_open_max/ctr_init` (adapt_access), and
  `PAGE_RBL_CFG` (miss threshold, ways/sets, epoch).
- **Axis 3 (refresh)** — `REF_CTRL.mode` (REFab / refpb_rr),
  `postpone_limit` / `pullin_limit`, `REF_TIMING_PB` (tREFIpb, tRFCpb).

**What makes this big (and why it is not just "run the matrix"):**
1. The cross is combinatorially large — sweep one axis at a time against
   a fixed baseline first, then the promising pairs; do NOT brute-force
   the full product.
2. The measurement path is changing underneath it: the bespoke harness
   meters/hists are being retired for the external observer
   ([[PUMICE-016]]), and the 1:1 accounting check moves with them. Land
   016 first or the numbers carry the AMBA-HISTCH1 accounting error.
3. The interesting telemetry already exists in-controller and should be
   the primary signal per Sean's direction (cheap counters stay in
   pumice): PAGE_STATS hit/miss/empty, SCHED_STATS act/pre,
   REF_STATS_REF, OBS_ROW_HIT per bank, refresh-defer histograms.
   [[PUMICE-015]] (greppable structure trackers) is the sim-side
   companion for understanding *why* a setting wins.
4. Board and sim disagree by construction — the DFI loopback models no
   page timing, so ordering/paging wins only show up on silicon or
   against a timing-faithful model. Sim runs prove mechanism + integrity;
   the board run produces the numbers.

**Deliverables:** a per-axis sweep report (BW, latency histogram, page
hit rate, ACT/PRE/REF counts per setting), recommended defaults per
workload family (streaming / random / mixed / page-hostile), and any
mechanism gaps found reported back to PUMICE-006 before it closes.

**Stimulus + measurement that already exists (audited 2026-08-27):**
- `pumice_char.py` families ARE the paging grade: `row_major` is
  contiguous WRAPPED INSIDE A PAGE (every burst a HIT), `col_major` walks
  rows in one bank (every burst a MISS), `incremental` marches
  contiguously (hits until each row crossing). row_major reaches sim via
  the `matrix`/`full` profiles; `smoke` only crosses incremental +
  col_major, so the hit case is missing from the quick profile.
- Sim tests have page-hit stimulus but do NOT grade it: `row_hit_pattern`
  walks columns in one {bank,row} (all hits, 6/16/32 bursts, data-only
  check); `engine_mirror` streams contiguous bursts but runs
  page_policy=CLOSE by design, so it is a throughput test, not a paging
  one. NOTHING reads PAGE_STATS -- `grep hit_rate` across all three
  tiers is empty.
- NEW: `AxiChanTracker` (PUMICE_TRACKERS=1) writes `axi_util.out` with
  per-channel utilization in axi_bus_meter buckets + handshake run
  lengths. MEASURE ON THE BFM TOP TB (masters at the `backtoback`
  randomizer profile), never the hand-driven core TB -- Sean 2026-08-27:
  "set the masters delay profile at b2b, this is the only meaningful way
  to test this".
  MEASUREMENT (top engine_mirror N=1024, backtoback, 62135 cycles):
    chan   util%   bp%   starv%  max_run  runs
    axiaw   1.65   0.0    98.35        1  1024 x1
    axiw    6.59   0.0    93.41        1  4096 x1   <-- writes NEVER stream
    axib    1.65   0.0     0.05        1  1024 x1
    axiar   1.65   0.0    98.35        1  1024 x1
    axir    6.59   0.0    50.36        4  1023 x4   <-- reads hold a full burst
  Self-consistent (axiar 1024 == camrd 1024 INSERTs; axiw 4096 == 1024
  bursts x 4 beats), so these are trustworthy.
  TWO FINDINGS worth chasing in this task:
  (a) the W channel's max_run is 1 -- write data beats never go
      back-to-back even with a zero-delay master, while R sustains a
      full 4-beat burst. Worth understanding before any write-side
      perf claim.
  (b) bp=0% everywhere with ~60 cycles/burst means the DUT never
      stalled the master: the remaining limiter is OUTSTANDING DEPTH
      (one burst in flight), not inter-beat delay. Fixing the delay
      profile was necessary but not sufficient -- a driver that waits
      for each completion still starves the DUT.

**Existing collateral to build on:** `pumice_char.py` (families,
RUN_PROFILES, the `multiid_min` repro profile), `pumice_master.py --char`
with `--char-configs` / `--char-level` / `--char-scale`, and the board
recipe in [[project_pumice_board_perf_char]] (the runtime page-policy
result — OPEN giving 8.8x on streaming, 12.7 -> 112 MB/s — is the
template for what a good characterization finding looks like).

## PUMICE-016 — adopt axi4_intf_master_observer (APB-configured) for perf observation
**Status:** ACTIVE 2026-08-26 — now the DIRECTED path, not a nicety.
Sean's direction: "don't have any monitor logic or perf logic inside
pumice — I have an external block that does just this. However, keep
tracking things like paging results and anything else that is easy but
interesting." So: the char harness's hand-rolled bus meters + latency
hists are to be RETIRED in favor of this observer (which also sidesteps
the AMBA-HISTCH1 shared-primitive bug the bespoke path sits on — the
observer instantiates the hist at NUM_CHANNELS=8); pumice keeps only the
cheap counters (PAGE/SCHED/REF *_STATS, OBS_ROW_HIT, refresh-defer
histograms). PUMICE-020 closed onto this task; the 1:1 accounting check
moves to the observer path when it lands.

pumice rolls its own perf observation: `perf_rd_prod/bp/starv/idle`,
`perf_rd_hist_count/total`, `perf_clear`, `perf_freeze` wired out of the harness
and read back through harness CSRs. The stream flows use
`axi4_intf_master_observer`, an inline pass-through meter over the same primitives
(`axi_bus_meter`, `axi_perf_latency_hist`) that also emits monbus packets.

**What changed that makes this worth doing (2026-08-04):** the observer now
carries its OWN APB config regblock (`obs_regs`) instead of exporting 29 `cfg_*`
ports for the instantiating harness to tie off, and it moved to
`projects/components/misc/rtl/` so it is reachable from any board flow:

    -f $MISC_ROOT/rtl/filelists/axi4_intf_master_observer.f

So adopting it costs one bridge APB slave and one instantiation, not 29 tie-offs
and a harness that has to know the block's internals. Registers are by name via
the generated regmap (see [[registers-by-name]]).

**Why bother:** pumice and stream currently measure throughput with different
code, so their numbers are not strictly comparable — which matters because the
pumice-vs-LiteDRAM A/B and the stream characterization both report MB/s. One
meter means one definition of a stalled cycle, and pumice would inherit the
latency histogram and the monbus packet path for free.

**Scope note:** the observer is an AXI4 pass-through meter (it was called
`axi4_dma_observer` until 2026-08-04; the DMA in the name was always wrong). pumice's interesting
traffic is on the DFI side, so this covers the AXI front-end (host -> pumice_top)
rather than DRAM-side behaviour; the DFI meters stay as they are.

**Not urgent.** Do it when the pumice harness is next opened for other reasons,
not as a standalone change — it touches the bridge map and the harness CSR
readback, and pumice bitstreams are on the critical path for the DDR2 work.

## PUMICE-023 — the char-framework sim is the board gate and must run before any pumice RTL commit
**Status:** open 2026-09-08  **Priority:** P1

`ddr2_char_framework/dv/tests` (test_ddr2_char_uart + test_ddr2_char_char) is
the only suite that builds the board's x16 / strict-timing configuration. The
arbiter fix passed all 213 pumice fub/macro/top tests and failed 7 there
(write side, fixed by the write-staged gate). Its Makefile `run-all-*` targets
were being swallowed by the `run-%` pattern into a nonexistent test id, so the
area had silently stopped gating; aliases added 2026-09-08. Pre-existing
failures to triage: `smoke_rate2_faithful`, `smoke_rate2_rdphase1`,
`smoke_rate2_strict`, `pagehit_rate2_x16_free_earlyen` (all fail at
79fb58a66, before this session). Add this directory to the pumice regression
convention (`regressions` skill) and to the components master Makefile.

## PUMICE-CLEANUP — doc + filelist cleanup (push from workstation)
**Status:** open 2026-07-24 — deferred (project cleanup; see TOOL-010)
**Priority:** P2

Apply the RTL-area cleanup pattern to pumice: doc placement ([[doc-placement]])
and filelist consistency ([[filelists]] — the `dv/tb/*_tb_top.f` move into a
`filelists/` dir co-located with the testbench).

**⚠️ Pushing: Sean pushes pumice from the workstation, NOT from the agent
environment (Sean, 2026-07-24).** Make and commit the pumice changes here if
working, but leave the push to Sean. Do not `git push` pumice work from this
box. (Reason per Sean — workstation is where pumice is pushed from.)

Gated behind the RTL area completing (Tasks/INDEX.md sequencing).

## PUMICE-KMAP — real K-maps for the scheduler, CAMs and DFI layer
**Status:** CLOSED 2026-09-10  **Was blocked on:** [[TOOLING-KMAP]] items 1-4

All six criteria of [[signal-contracts-and-kmaps]] are discharged across the 17
computed maps, the artifacts are consolidated, and both halves are gated so they
cannot silently rot again.

**One workbook, one generator.** Four workbooks from three generators across two
directories became `docs/pumice_signal_contracts.xlsx` from
`docs/gen_pumice_signal_contracts.py`, verified to reproduce all 18 original
sheets cell-for-cell. The old flow LOADED the workbook and appended rows, so
re-running duplicated them (the committed Scheduler sheet had 8 such rows); the
new one builds from scratch and is idempotent. An INDEX sheet separates SPEC
tables from COMPUTED grids and opens with the measured RTL status, so the book
cannot be read as a bug list for a controller that meets its targets.

**Criterion 1 (computed, not drawn) was FALSE for four maps**, now gated.
`rd_col_m`/`wr_col_m` modelled 7 terms against 13; `w_ref_safe`, `w_guarded`,
`w_drain_active` each dropped one. `docs/check_kmap_rtl_sync.py` requires every
RTL identifier on a signal's RHS to be NAMED in the documented expression (folds
stay legal, the fold equation is in [brackets]). **16 of 17 machine-checked, 0
drifted**; the generator REFUSES to write on drift.

**Criteria 3/4/5/6.** Axis-term tables with file:line on the four maps whose axes
are folds; relations on all 17 (constraint or explicit independence note); 38
don't-care cells from cited invariants; Quine-McCluskey implicants printed beside
the documented equation on every map.

**Waves: audited, corrected, extended, RENDERED, in the MAS.** The set was drawn
at tCCD=2 with streams captioned "~100% util" -- impossible, and the RTL settles
it (BURST_WORDS=1, so a column every cycle, which is the measured 571.3 MB/s).
Added seven performance diagrams: 13-17 bad-but-correct (admit gate, ring bound,
page thrash, turnaround thrash, refresh storm) and 18-19 pathological, each
captioned with the board number it produced. `design/check_waves.py` found **11
real defects** in the pre-existing diagrams, five of them labels attached to a
logic level instead of a bus slot (WaveDrom silently shifts every label in the
row onto the wrong segment). `design/render_waves.py` produces SVG+PNG for all
19 and **MAS Chapter 7** embeds every one. Rendering itself exposed that every
caption (101-431 chars) overflowed the image and 23 group labels overlapped --
neither visible in the JSON, neither ever seen because nothing had been rendered.

**The lesson.** A spec written during a debugging campaign dates instantly and
silently: these artifacts asserted a 15%-of-peak controller and five live
defects while the board ran at 95% in both directions. Mechanical checks, not
review, are what keep hand-built collateral honest -- every check added here
failed on its first run.

