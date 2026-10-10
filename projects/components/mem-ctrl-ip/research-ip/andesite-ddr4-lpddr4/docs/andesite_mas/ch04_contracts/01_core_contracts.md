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

# Core Signal Contracts

## What a contract is here

A signal contract in this repo is a machine-checkable statement of what a
signal is allowed to do: a term list with its defining `file:line` citation,
the invariants between terms, and a decision table whose forbidden rows are
marked `ILLEGAL`. The canonical methodology is
`vault/handbook/design/signal-contracts-and-kmaps.md`; the shared generator
machinery is `bin/kmaps/`, and the andesite kmap book
(`../kmaps/`, andesite TASK-004) builds its contract sheets from the anchors
this chapter names.

## Pre-RTL citation posture

At MAS v0.1 there is no RTL, so every contract below cites the MAS ch02 page
where the intended expression is written verbatim — the fenced anchors. When
the first RTL lands, each citation is re-pointed at the corresponding
`.sv` file and line, and the generator's citation gate then enforces that
the workbook and the RTL agree; a drift fails the run. The anchor map:

| Contract domain | Defining anchors (file:line, at v0.1) |
|---|---|
| DDR4 command decode | [01_cmd_formatter.md](../ch02_blocks/01_cmd_formatter.md) — truth table fence |
| Activate field packing | [01_cmd_formatter.md](../ch02_blocks/01_cmd_formatter.md) — activate form fence |
| LPDDR4 CA encodings | [01_cmd_formatter.md](../ch02_blocks/01_cmd_formatter.md) — placeholder table, pinned by the kmap book |
| Init FSM ordering | [02_init_sequencer.md](../ch02_blocks/02_init_sequencer.md) — DDR4 and LPDDR4 state-list fences |
| Address decode structure | [04_addr_mapper.md](../ch02_blocks/04_addr_mapper.md) — decode fence |
| Scheduler admission | [05_scheduler.md](../ch02_blocks/05_scheduler.md) — admission-rule fence |
| FGR interval arithmetic | [06_refresh_ctrl.md](../ch02_blocks/06_refresh_ctrl.md) — interval fence |
| MPC calibration FSM | [07_zq_ctrl.md](../ch02_blocks/07_zq_ctrl.md) — MPC FSM fence |
| ODT policy states | [08_odt_ctrl.md](../ch02_blocks/08_odt_ctrl.md) — policy-state fence |
| Training flows and telemetry | [09_training.md](../ch02_blocks/09_training.md) — MPR/CA/WDQ flow fences, four-state encoding fence |
| DFI datapath pin set and DBI | [10_dfi_datapath.md](../ch02_blocks/10_dfi_datapath.md) — pin-set and DBI fences |
| LPDDR4 CA encodings | [generated/02_lpddr4_ca_command_table.md](../../kmaps/generated/02_lpddr4_ca_command_table.md) — TBC JESD209-4 |
| Address decode | [generated/03_addr_decode_maps.md](../../kmaps/generated/03_addr_decode_maps.md) — design-point decode maps |
| MR programming | [generated/04_mr_programming_maps.md](../../kmaps/generated/04_mr_programming_maps.md) — MR0-MR6 / LPDDR4 MRW |
| ODT truth | [generated/05_odt_truth_table.md](../../kmaps/generated/05_odt_truth_table.md) — termination policy |
| FGR select | [generated/06_fgr_refresh_map.md](../../kmaps/generated/06_fgr_refresh_map.md) — refresh granularity |

: Table 4.1: Anchor map — the kmap generator cites these file:line pairs

The line numbers are captured at authoring time by the generator's citation
gate; the table above names the fences, and `verify_citations` pins the
exact lines on every run.

## Contract: DDR4 command decode (the formatter's core)

**Terms.** `ACT_n`, `RAS_n`, `CAS_n`, `WE_n` (DFI command pins, source
[01_cmd_formatter.md](../ch02_blocks/01_cmd_formatter.md)); `CS_n` (select);
`AP` (the auto-precharge address bit, A10).

**Invariants** (each renders ILLEGAL rows impossible, per the truth-table
anchor):

1. Exactly one of the anchored encodings holds whenever `CS_n = 0`; the
   fence's rows are exhaustive and mutually exclusive.
2. `ACT_n = 0` marks exactly three rows in the anchor: ACT (with `RAS_n=1,
   CAS_n=1, WE_n=1`), MRS (`RAS_n=0, CAS_n=0, WE_n=0`) and REF (`RAS_n=0,
   CAS_n=0, WE_n=1`) — no other pin combination may carry `ACT_n = 0`.
3. `AP` is an address input: it never appears in the pin-level table; the
   variants (RDA/WRA, PREA, ZQCL) are the RD/WR/PRE/ZQ rows qualified by
   `AP = 1`.
4. Parity (`dfi_parity_in`) is generated only when `parity_en_i = 1`, and
   `parity_en_i` may only be set after the init sequence has programmed
   parity mode (HAS Ch 3.2 dependency).

**Decision table.** One row per (command, AP) combination the controller
issues; forbidden rows — commands outside the anchored set, or any command
while `parity_en_i` disagrees with the MR image — are `ILLEGAL`. The
minimized qualifier SOPs for this table are the kmap book's DDR4 command
table (andesite TASK-004 output); the workbook and this contract must always cite the
same anchor lines.

## Contract: maintenance request/grant

**Terms.** `req`/`gnt` between `refresh_ctrl`, `zq_ctrl` (both cores),
`odt_ctrl` turnaround notices, and the scheduler (source
[05_scheduler.md](../ch02_blocks/05_scheduler.md)).

**Invariants.**

1. A maintenance source raises `req` and waits; it never asserts its command
   onto the bus without `gnt` (family doctrine 2, quoted in full in the
   family docs).
2. `gnt` is exclusive: at most one maintenance source holds the bus in any
   cycle.
3. A refresh of either granularity and a ZQ calibration of either form are
   ordinary occupants of the banks they touch: the bank timers own those
   banks for the operation's duration (HAS Ch 3.4 requirement 4).

**Decision table.** One row per (source, state) pair; rows where two sources
hold `gnt`, or a source issues without `gnt`, are `ILLEGAL`.

## Contract: training four-state telemetry

**Terms.** The 2-bit status and counters per interface (source
[09_training.md](../ch02_blocks/09_training.md)).

**Invariants.**

1. The status is exactly one of {never attempted, converged, timed out, no
   result in window}; a detector that has never fired is not evidence of
   anything, so "never attempted" must be representable and is the reset
   state.
2. A timeout is distinguishable from a no-result: the CSR-defined timeout
   with its distinct status bit is the family's rule (HAS Ch 3.3), and the
   two states may not share an encoding.
3. No interface state performs a search: the state lists contain no
   delay-walk states, and the host-visible counters only count attempts,
   results, and timeouts.

**Decision table.** One row per (interface, status) pair; any row pairing a
search behaviour with a legal status is `ILLEGAL`.

## Regenerating the workbook

```
cd projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4
python3 docs/kmaps/gen_andesite_kmaps.py
```

The generator writes `docs/kmaps/andesite_cmd_kmaps.xlsx` and the
`docs/kmaps/generated/*.md` renderings. Do not hand-edit the `.xlsx`; it is
a build artifact of the generator, and the citation gate fails the run if
any `file:line` citation drifts from this book.

For every contract the verdict is `NOT CHECKED` until RTL exists — the
correct pre-RTL posture, identical to the bch MAS's. The verdict becomes
meaningful once `rtl_sop` can be diffed against the derived minimal cover.
