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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# ODT Controller (`andesite_odt_ctrl`)

**Module:** `andesite_odt_ctrl` (planned)
**Location:** `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/`
**Category:** termination policy / rank control
**Parent:** `andesite_top` / scheduler boundary
**Status:** specified — no RTL exists (HAS v0.1 posture)

## Purpose

`odt_ctrl` turns DDR4's termination schedule into a per-rank ODT pin policy.
The DRAM exposes three termination values — RTT_NOM, RTT_WR, and RTT_PARK —
and a set of latencies that say when each one takes effect. This block watches
the scheduler's grant stream, decides which rank should terminate how, and
drives the ODT pins with the right delay. It is a tap, not an arbiter; it
never stalls a command to make a termination point.

## Parameters

| Parameter | Type | Range | Default | Meaning | PRD |
|---|---|---|---|---|---|
| `NUM_RANKS` | int | 1..4 | 1 | ranks sharing the DQ bus | A1 |
| `RTT_NOM_IMG` | CSR field | vendor-defined | TBD | MR1 RTT_NOM image for this board | A2 |
| `RTT_WR_IMG` | CSR field | vendor-defined | TBD | MR2 RTT_WR image for this board | A3 |
| `RTT_PARK_IMG` | CSR field | vendor-defined | TBD | MR5 RTT_PARK image for this board | A4 |
| `ODTLon_CSR` | CSR | speed-bin range | TBD | assertion latency from command to ODT active | A5 |
| `ODTLoff_CSR` | CSR | speed-bin range | TBD | de-assertion latency from command to ODT inactive | A6 |
| `ODT_TURN_CSR` | CSR | speed-bin range | TBD | write-to-read ODT turnaround value | A7 |
| `tADC_CSR` | CSR | speed-bin range | TBD | command-to-ODT-change delay for transitions | A8 |

: Table 2.8.1: `odt_ctrl` parameters

The numeric values behind these CSRs come from the selected JESD79-4 speed bin
at CSR-derivation time (HAS Ch 5; numeric constants are HAS open question Q1).

## Interface

| Signal | Direction | Width | Description |
|---|---|---|---|
| `grant_rank` | in | `log2(NUM_RANKS)` | rank selected by the scheduler grant |
| `grant_cmd` | in | cmd enc | command type of the granted beat (RD, WR, or other) |
| `grant_valid` | in | 1 | the grant is valid this cycle |
| `odt_pin` | out | `NUM_RANKS` | per-rank ODT pin toward the PHY/DRAM |
| `rtt_nom_img` | in | CSR width | MR1 RTT_NOM field image |
| `rtt_wr_img` | in | CSR width | MR2 RTT_WR field image |
| `rtt_park_img` | in | CSR width | MR5 RTT_PARK field image |
| `odtlon` | in | CSR width | ODTLon value |
| `odtloff` | in | CSR width | ODTLoff value |
| `odt_turn` | in | CSR width | write-to-read ODT turnaround |
| `tadc` | in | CSR width | tADC value |
| `init_done` | in | 1 | ownership transfers from `init_sequencer` to `odt_ctrl` |
| `init_odt` | in | `NUM_RANKS` | ODT value held by `init_sequencer` until handoff |
| `hist_state` | out | packed | per-rank ODT state history for telemetry |
| `trans_count` | out | packed | per-rank transition counters for telemetry |

: Table 2.8.2: `odt_ctrl` ports

## Microarchitecture internals

### Policy state table

The termination policy is per-rank. Each rank is in one of three policy
states, selected from the grant stream:

```text
state        | RTT applied   | entered when
IDLE         | RTT_PARK      | no rank selected (park policy)
RD (other)   | RTT_NOM       | a read granted to any rank
WR (self)    | RTT_WR        | a write granted to this rank
(per-rank; values are the MR1/MR2/MR5 images, CSR-programmed)
```

`RD (other)` means a read to any rank makes the rank that is *not* reading
present RTT_NOM. `WR (self)` means a write to a rank makes that same rank
present RTT_WR. A single-rank design point exercises IDLE and WR; the
multi-rank coupling is already in the structure and is not special-cased away.

### Command-stream tap

`odt_ctrl` consumes the scheduler's grant stream: which rank won, and whether
it won with a read or a write. That is all the block needs. It does not
arbitrate, it does not back-pressure, and it does not modify the command
stream. The HAS requires this explicitly (HAS Ch 3.5, requirement 3): ODT
transitions never stall commands.

### Pin timing

ODT assertion and de-assertion are delayed from the command by the ODTL
family. ODTLon governs how many clocks after a write command the ODT pin
asserts; ODTLoff governs how many clocks after the burst the pin releases.
The write-to-read ODT turnaround is the gap when switching from a write
termination picture to a read termination picture, and tADC is the command-to-
ODT-change interval used for rank-to-rank transitions. All four are runtime
CSRs, named by their JEDEC symbols, initialised from the JESD79-4 speed bin at
CSR-derivation time (HAS Ch 5; numeric constants are HAS open question Q1).

A small counter per rank loads the relevant latency when the grant decodes to
a state change and counts down to the pin edge. The counter can be shared
between assertion and release because the block never has overlapping state
machines on the same rank in this policy.

### The init seam

Until `init_done`, the ODT pin belongs to `init_sequencer`. The init sequence
programs MR1/MR2/MR5 and holds ODT per the JEDEC initialization constraint; after
the final mode-register writes it waits at least tMOD before raising
`init_done`. At that cycle ownership transfers to `odt_ctrl`: the block
samples `init_odt` as its starting pin value and from then on drives the pin
from its own policy state. The handoff is a named, bounded seam.

### LPDDR4 delta

LPDDR4 has no ODT pin. DQ ODT is programmed in the LPDDR4 mode-register set at
init and held static this edition — it lives in `mode_register`'s LPDDR4 maps
and in the init sequence, not in `odt_ctrl`. The dynamic machinery above is
DDR4-scoped; the block's structure keeps that scoping explicit rather than
pretending a pin LPDDR4 doesn't have.

### Telemetry

`odt_ctrl` records state history and transition counts so a termination policy
sweep is measurable (HAS Table 3.7). The telemetry exposes:

- a per-rank rolling history of the policy state (IDLE / RD / WR)
- counters for IDLE→RD, IDLE→WR, RD→IDLE, WR→IDLE, and RD↔WR transitions
- a sticky "PARK never left" indicator for the single-rank case

## FSM policy

The block permits either a small policy FSM per rank or a counter-plus-compare
implementation. The states are IDLE, RD, and WR as shown in the policy table.
A pure combinational decode of `grant_cmd` is not sufficient: the ODTL delays
need a time reference, so every output change is launched from a loaded
counter, not from the decode alone. In practice this means the FSM's next-
state logic feeds a counter load, and the pin flips on counter expiration.

## Timing

- ODTLon: runtime CSR, assertion delay from write command to ODT active.
- ODTLoff: runtime CSR, de-assertion delay after burst end to ODT inactive.
- Write-to-read ODT turnaround: runtime CSR, gap between write and read ODT
  pictures.
- tADC: runtime CSR, command-to-ODT-change interval for transitions.
- tMOD: enforced at the init seam by `init_sequencer` before `init_done`
  rises.
- All numeric values are runtime CSRs, initialised from the JESD79-4 speed bin
  at CSR-derivation time (HAS Ch 5; numeric constants are HAS open question
  Q1).

## Notes

- The single-rank design point exercises IDLE and WR only; RD is reachable in
  multi-rank builds but the structure is the same.
- Rank coupling is built in, not bolted on: the "other rank terminates" rule is
  just the per-rank state table evaluated for every rank each cycle.
- No command ever waits for `odt_ctrl`. If a latency cannot be met because the
  scheduler changed its mind, the block follows the most recent grant; the
  scheduler's timing rules must already guarantee that the DRAM can absorb the
  command.
