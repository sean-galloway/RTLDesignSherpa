<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# What Is Inherited, and the Ten Areas That Change

## The inheritance, stated once

Twelve of scoria's twenty-six FUB files carry over with no functional change,
plus the top, geared wrapper, core and AXI4 macro — Chapter 2.3 lists them and
the count is reconciled there. This chapter covers only what changes: ten
areas, absorbed by a modified set of a dozen blocks and three new ones. The
list is short by design, and it is an argument, not a convenience — the
inherited blocks carry scoria's verification evidence (221 tests, 9 formal
blocks at last measure), and re-deriving them would discard it.

**Important — inherit `global_timers` in its FIXED form.** scoria's timers
carry pumice's next-state-function fix (pumice ISSUE-018: readiness flags one
cycle late, which permitted tCCD and tRTW violations). andesite inherits the
fixed form; a fresh implementation from a behavioural description would
reintroduce the defect, because the description does not mention the flop.
Copy the module.

## The changes, in one table

The ten areas the bootstrap spec settled, with the blocks that absorb them:

| # | Delta | Blocks | Marking |
|---|---|---|---|
| 1 | Bank groups: tCCD_L/S, tRRD_L/S | `addr_mapper`, scheduler/`cmd_arbiter`, `global_timers` | MODIFIED |
| 2 | Command encoding: ACT_n 5th pin, BG0/1; LPDDR4 6-bit CA bus | `dfi_cmd_formatter` | MODIFIED / NEW (LPDDR4 path) |
| 3 | Init: reset procedure, MR0–MR6, gear-down + parity enable | `init_sequencer`, `mode_register` | MODIFIED |
| 4 | Refresh: FGR 1x/2x/4x (MR3); LPDDR4 controller-directed per-bank | `refresh_ctrl` | MODIFIED (inherits scoria's landed TASK-001 modes A/B/C as the policy base) |
| 5 | ZQ: DDR4 keeps ZQCS/ZQCL; LPDDR4 calibration via MPC | `zq_ctrl` | INHERITED / NEW (LPDDR4 path) |
| 6 | Training: read leveling (MPR), LPDDR4 CA/WDQ training | new training blocks + `wrlvl_ifc` | NEW / MODIFIED (search in firmware, per D2 precedent) |
| 7 | Datapath: DBI via DFI 4.0 `dfi_dbi_*`; write CRC excluded v0.1 with named unblock condition | dfi datapath blocks | MODIFIED |
| 8 | CA parity + `alert_n`; gear-down handshake | formatter/sequencer + new parity/alert handling | MODIFIED / NEW |
| 9 | Dynamic ODT: RTT_NOM/WR/PARK + ODT latencies (scoria holds ODT static — insufficient) | new `odt_ctrl` | NEW |
| 10 | LPDDR4 per-chapter deltas: no bank groups, 8 banks/channel, 2-channel x16, MPC bus, DSM power states (deferred, named condition) | as above | as above |

: Table 3.0: The ten delta areas, verbatim from the bootstrap spec

The command encodings, decode maps, MR maps, ODT policy, and FGR select named
by the ten areas above are pinned table-by-table in the generated kmap book
([`../../kmaps/generated/`](../../kmaps/generated/)). The DDR4 command table's
expected values feed the Chapter 6 verification item 6 checker.

## The ten areas, one paragraph each

**1 — Bank groups.** DDR4 partitions its banks into groups, and command
spacing becomes a function of which group a command targets: tCCD_S/tRRD_S
across groups, tCCD_L/tRRD_L within one. The address mapper grows the BG0/BG1
decode, the arbiter learns same-group versus cross-group issue, and the
global timers take the long/short pairs on as first-class counters. All four
timings are runtime CSRs. LPDDR4 has no bank groups — its pair collapses to
L = S, which the arbiter must degenerate to gracefully, not special-case.
**Blocks:** `addr_mapper`, `cmd_arbiter`, `global_timers`,
`mem_cmd_scheduler` — all MODIFIED (Ch 3.1).

**2 — Command encoding.** DDR4 makes ACT a five-pin command: `ACT_n` plus
RAS/CAS/WE, and carries BG0/BG1 on the address pins during activate. The
formatter's truth table changes shape, and the command path widens to carry
the new pins. LPDDR4 is the bigger change inside the same block: a 6-bit
double-data-rate CA bus with commands taking two cycles, implemented as a NEW
submodule so the DDR4 path stays reviewable on its own. **Blocks:**
`dfi_cmd_formatter` MODIFIED with a NEW LPDDR4 CA submodule (Ch 3.2, 3.6).

**3 — Init.** DDR4 brings a RESET# pin, a seven-register mode-register set,
gear-down entry and parity enable into one ordered sequence. scoria's lesson
applies twice over: the MR order is JEDEC's, not ours. **Blocks:**
`init_sequencer`, `mode_register` — MODIFIED (Ch 3.2).

**4 — Refresh.** DDR4's fine-granularity refresh (1x/2x/4x, selected in MR3)
adds a density dimension; LPDDR4 makes per-bank refresh the commodity default
and — unlike LPDDR2/3 — lets the controller name the bank. scoria's landed
TASK-001 modes (elastic refresh, TCR, ZQCS placement) stay the policy base.
**Block:** `refresh_ctrl` MODIFIED (Ch 3.4).

**5 — ZQ.** DDR4 keeps `ZQCS`/`ZQCL` exactly as scoria issues them — the
block is inherited unchanged for DDR4. LPDDR4 moves calibration onto the MPC
command, a NEW submodule beside the inherited core. **Block:** `zq_ctrl`
INHERITED / NEW LPDDR4 path (Ch 3.2).

**6 — Training.** Write leveling's interface is inherited; read leveling
(MPR-based) and LPDDR4 CA/WDQ training are new interfaces in the same
family — handshake, MR/MPC paths, timing windows, telemetry, and **no search
loop anywhere** (D2 precedent). **Blocks:** `wrlvl_ifc` MODIFIED; `rdlvl_ifc`,
`ca_train_ifc` NEW (Ch 3.3).

**7 — Datapath.** DFI 4.0's `dfi_dbi_*` wires pass Data Bus Inversion through
the read and write paths. Write CRC is excluded from this edition with a
named unblock condition below. **Blocks:** `dfi_rd_aligner`,
`dfi_wr_serializer`, `dfi_layer` — MODIFIED (Ch 3.5, 4.1).

**8 — CA parity and gear-down.** DDR4 CA parity adds a counting/checking
obligation and the `alert_n` return path; gear-down halves the CA rate after
init with a controller/PHY handshake. Parity machinery splits between the
formatter (counting) and the sequencer (enable at init); `alert_n` handling is
a NEW submodule at the DFI boundary. Scope split between hardware and
firmware is an open question (Ch 6). **Blocks:** `dfi_cmd_formatter`,
`init_sequencer` MODIFIED; NEW `alert_n` handling (Ch 3.2, 4.1).

**9 — Dynamic ODT.** DDR4's termination is dynamic: RTT_NOM, RTT_WR during
write bursts, RTT_PARK when idle, with ODT-pin latencies around each
transition. scoria holds ODT static — that is insufficient the moment writes
and reads interleave, and the policy decisions (which ranks terminate when)
need a home. **`odt_ctrl` is NEW** (Ch 3.5).

**10 — LPDDR4 per-chapter deltas.** LPDDR4's deltas ride the chapters above
rather than forming an eleventh area: no bank groups (area 1), the CA bus
(area 2), MPC-carried ZQ (area 5), CA/WDQ training (area 6), controller-
directed refresh (area 4), MR-programmed termination (area 9), and DSM power
states deferred with the condition below. Chapter 3.6 collects them as a
reading aid.

## The full reuse table

Every scoria module, its andesite marking, and its cause. This table and
Chapter 2.3 carry the same markings; where they disagree, one of them is
wrong and both get fixed.

| scoria module | Marking | Cause | Where |
|---|---|---|---|
| `scoria_top` | INHERITED | structure unchanged | Ch 2.3 |
| `scoria_top_geared` | INHERITED | the host/DRAM width-gearing wrapper, unchanged | Ch 2.3 |
| `scoria_core` | INHERITED | core assembly unchanged | Ch 2.3 |
| `scoria_axi4_ifc` | INHERITED | the AXI4 host side is untouched by this generation | Ch 2.3, 4.2 |
| `scoria_mem_cmd_scheduler` | MODIFIED | L/S admission alongside scoria's ZQ maintenance admission | 3.1 |
| `scoria_dfi_layer` | MODIFIED | DFI 4.0 control surface and DBI wires | 4.1 |
| `scoria_addr_mapper` | MODIFIED | bank-group decode | 3.1 |
| `scoria_cmd_arbiter` | MODIFIED | L/S-aware issue | 3.1 |
| `scoria_global_timers` | MODIFIED | the long/short pairs | 3.1 |
| `scoria_dfi_cmd_formatter` | MODIFIED | ACT_n, BG0/1, CA parity; NEW submodule: LPDDR4 6-bit CA path | 3.2, 3.6 |
| `scoria_init_sequencer` | MODIFIED | reset procedure, MR0-MR6 order, gear-down entry, parity enable | 3.2 |
| `scoria_mode_register` | MODIFIED | MR0-MR6 field maps per memtype | 3.2 |
| `scoria_zq_ctrl` | INHERITED | DDR4's ZQCS/ZQCL exactly as built; NEW submodule: LPDDR4 MPC calibration | 3.2 |
| `scoria_refresh_ctrl` | MODIFIED | FGR 1x/2x/4x on the inherited elastic/TCR/placement base | 3.4 |
| `scoria_dfi_cmd_path` | MODIFIED | ACT_n, BG and parity wires ride the command path | 4.1 |
| `scoria_dfi_rd_aligner` | MODIFIED | DBI read path | 3.5 |
| `scoria_dfi_wr_serializer` | MODIFIED | DBI write path | 3.5 |
| `scoria_wrlvl_ifc` | MODIFIED | training-interface family grows; contract and no-search rule unchanged | 3.3 |
| `scoria_powerdown_ctrl` | DORMANT | carried dormant, condition below | below |
| `scoria_dfi_signal_pack` | DORMANT | carried dormant, condition below | below |
| (new) `odt_ctrl` | NEW | dynamic ODT | 3.5 |
| (new) `rdlvl_ifc` | NEW | MPR read-leveling interface | 3.3 |
| (new) `ca_train_ifc` | NEW | LPDDR4 CA/WDQ training interface | 3.3 |

: Table 3.1: The complete reuse table — every scoria module with its andesite marking

Twelve further FUBs are inherited unchanged and live in Chapter 2.3's prose:
`bank_timer`/`bank_timers`, `page_policy`, `rd_cmd_cam`, `wr_data_cam`,
`rd_intake`, `wr_intake`, `wr_splitter`, `rd_return_ring`,
`axi_burst_chopper`, `dfi_cdc`, and `cmd_history_checker` (whose
spacing-parameter set grows DDR4's pairs — a parameter change, not a
mechanism change). The CSR block's generation flow is INHERITED; its contents
grow and Chapter 5 owns that.

## Dormant: `powerdown_ctrl` and `dfi_signal_pack`

Both are carried dormant, the same disposition scoria reached for the same
pair, with the condition named rather than implied. **Waking condition:** a
board target exists for andesite, or the LPDDR4 DSM work below un-defers —
whichever comes first. Until then both files are kept in the tree as the
starting point for that work, worth more dormant than deleted.

The reasoning splits by memtype. For DDR4, power-down is CKE plus
`SRE`/`SRX`, and the sim-only design point exercises neither meaningfully —
the DRAM simply stays in normal operation, which is parity with the
references this design point is verified against. For LPDDR4 the pair is
load-bearing: deep-sleep states need the DRAM clock stopped
(`dfi_dram_clk_disable`), and that is `dfi_signal_pack`'s one function the
phase-multiplied buses don't cover. LPDDR4 *exists* for power; deferring its
sleep states is a scope decision, not a judgment that they don't matter.

## Deferred, with named conditions

Three items are deliberately out of this edition, each with the condition
that un-defers it recorded so the parking is a decision rather than neglect:

| Deferred item | Condition that un-defers it |
|---|---|
| Write CRC (DDR4, datapath) | A characterization or board campaign that needs end-to-end write protection; the addition is bounded to the write datapath and its CSRs |
| LPDDR4 DVFS / deep-sleep states | A low-power consumer and a target that can measure power; wakes the dormant pair above |
| Self-refresh scheduling as a policy | Same waking condition as the dormant pair, plus a workload whose idle behaviour makes the policy a question worth answering |

: Table 3.2: The deferred list

**A note on the cleverer refresh schemes.** Out-of-order per-bank refresh,
write-refresh parallelisation, refresh pausing and SARP/DSARP are surveyed in
andesite TASK-001 (it predates this book and its roadmap is the
`ADVANCED_MODES_ROADMAP`); this edition implements commodity refresh only and
leaves the survey's research items where they are.
