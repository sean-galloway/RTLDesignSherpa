# TASK-025: adopt axi4_intf_master_observer (APB-configured) for perf observation

> **Migrated from `PUMICE-016`** on 2026-09-27, when this area's flat
> `dropped.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-016` reference resolves. Body below is verbatim from the flat page.
>
> Lane chosen by reading this item's own Status line and opening, not its title:
> a keyword pass over the 35 items misclassified 14 of them.



**Status:** DROPPED 2026-09-23 — every premise was re-verified and none holds.

The task was investigated in full before dropping: five premises checked against
the tree, two out-of-context syntheses on the real part, and the one piece of
open work it carried re-run in sim. The conclusion is that adopting the observer
here costs 3x the area of what it replaces and buys no measurement pumice does
not already have. Recorded in detail so it is not re-proposed on the same
reasoning.

**Premise by premise, verified 2026-09-23:**

1. "the char harness's HAND-ROLLED bus meters + latency hists" — FALSE.
   `char_engine_block.sv:608-712` instantiates `rtl/amba/shared/axi_bus_meter.sv`
   and `rtl/amba/shared/axi_perf_latency_hist.sv` directly: the SAME shared
   primitives `axi4_intf_master_observer` wraps internally. Nothing here is
   bespoke. The observer is a packaging of those two blocks plus a monbus tap
   path, not a different meter.

2. "sidesteps the AMBA-HISTCH1 shared-primitive bug (the observer instantiates
   the hist at NUM_CHANNELS=8)" — NEVER TRUE, and now moot. The observer passes
   NUM_CHANNELS straight through (`axi4_intf_master_observer.sv:1567`, `:1597`);
   it does not force 8. STREAM passes 8; pumice has no channel concept and would
   pass 1, landing on the identical code path. The premise described STREAM's
   parameterization, not a property of the block. Moot because AMBA-HISTCH1 is
   CLOSED — fixed at source in `axi_perf_latency_hist.sv:136-138` (44ba2eea3,
   2026-08-27) — so the direct instantiation already carries the fix.

3. "it touches the bridge map" — STALE. The `obs_apb` slave (0x00090000, APB,
   4 KB) is already generated in BOTH harness bridges, reserved 2026-08-28 for
   exactly this adoption. No bridge regen was ever going to be needed, in either
   the pumice build or the LiteDRAM A/B harness.

4. Sean's direction, "don't have any monitor logic or perf logic inside pumice"
   — ALREADY SATISFIED. A grep for meter/hist/monbus across the pumice
   controller RTL returns nothing. The meters live in the char HARNESS, which is
   exactly where an external observer would sit. The direction was never
   violated, so adoption does not bring the design into compliance with it.

5. "one meter means one definition of a stalled cycle" — ALREADY SATISFIED. The
   same primitive counts on both sides, so the stalled-cycle definition is
   already identical between pumice and STREAM; and the pumice-vs-LiteDRAM A/B
   shares one `char_engine_block`, so that comparison was never measured with
   two different meters either.

**Measured cost** (OOC synth, xc7a100tcsg324-1, Vivado 2025.1, 2026-09-23):

| block | LUTs | FFs |
|---|---|---|
| current perf path: 2x `axi_bus_meter` + 2x `axi_perf_latency_hist` (PIW=8, ch1, MAX_OUTSTANDING=32) | 2030 | 4253 |
| `axi4_intf_master_observer`, smallest legal config (1rd+1wr, ch1, ID=8, `ENABLE_MON_TAPS=0`) | 6253 | 5438 |
| delta | **+4223 (+208%)** | **+1185** |

The extra 4.2k LUTs are the monitor CAM taps, `monbus_arbiter`,
`monbus_axil4_axi4_group` and its regblock. None of them is parameter-removable
— only `ENABLE_BUS_METER` and `ENABLE_LATENCY_HIST` are generate-gated, and the
taps/arbiter/group are unconditional — and none is wanted here: the pumice
harness has no memory ring for the dump master, so it would be tied off. They
buy no additional measurement. pumice would read the same four numbers, through
APB instead of a harness CSR. Against a build at 38481/63400 LUTs (60.7%) with
WNS +0.082 ns ([[feedback_pumice_aggressive_timing]]), that is ~6.7% of the
device for zero capability.

**Not a blocker, recorded to close the question:** the observer's monitor taps
hard-`$error` above ID_WIDTH 8 (`axi_monitor_trans_mgr.sv:284` — `bus_transaction_t.id`
is an 8-bit field). That does NOT bite here: `ddr2_char_macro.sv:190` sets
`PIW = AXI_ID_WIDTH` = 8 ("always 8", `:514`). The `id_width = 9` in the bridge
tomls belongs to the generated bridge slave port, which `char_gen_unit` replaced
in the data path ([[project_ddr2_char_gen_unit_direct]]). The OOC figures above
are at 8, the width the build actually uses.

**PUMICE-020's residue is DISCHARGED, not lost.** [[PUMICE-020]] closed onto this
task with its multiid arm parked red "until the observer adoption replaces the
bespoke hist". Both of its root causes were since fixed independently:
MAX_OUTSTANDING 8 -> 32 (72a0a951e, 2026-09-10) and the HISTCH1 channel decode
(44ba2eea3, 2026-08-27). Re-run 2026-09-23 at BOARD geometry, clean build,
`TEST_CHAR_PROFILE=multiid_min` on `test_ddr2_char_char_families_x16`, 350.59 s
wall clock, 1 passed against the UNGUARDED 1:1 assert at
`test_ddr2_char_char.py:300`:

```
baseline/col_major_bl8_multiid  ok=True mism=0  blen=8 txn=64
  RD hist(total=64) = [0,0,0,0,0,1,1,2,60,0,0,0,0,0,0,0]
```

64 of 64, bins summing to exactly 64 — against 168409 vs 64000 on the board and
33/64 in sim before the fixes. Both fixes predate the current bitstream
(2026-09-21), so the board-side check needs no rebuild to confirm the same.

**Consequence:** this task was recorded as GATING [[TASK-002]] on the grounds
that until it landed "the perf numbers carry the AMBA-HISTCH1 accounting error".
That gate is lifted — the accounting error is fixed at source and measured clean
above. TASK-002 is unblocked.

**If the observer is ever wanted here anyway** (uniformity with STREAM, or the
monbus packet path becomes useful), nothing in the tree blocks it: the
`obs_apb` slot is live, the filelist is `-f $MISC_ROOT/rtl/filelists/axi4_intf_master_observer.f`,
and the cost is the table above. It is an area decision, not an engineering one.

<details><summary>Original entry</summary>

**[archived heading] PUMICE-016 — adopt axi4_intf_master_observer (APB-configured) for perf observation**
**[archived] Status:** ACTIVE 2026-08-26 — now the DIRECTED path, not a nicety.
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


</details>

---
