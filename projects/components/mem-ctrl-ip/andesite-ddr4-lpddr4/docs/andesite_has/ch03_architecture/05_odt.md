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

# ODT: Dynamic, with a New odt_ctrl

## Why static ODT doesn't survive DDR4

scoria holds ODT static: RTT_NOM is programmed in MR1 at init, the ODT pin
is held at a fixed level through initialization, and nothing changes at
runtime. That was defensible at DDR3-800 with one rank, and scoria's book
says so plainly. It is insufficient for DDR4, for two reasons the standard
builds in:

1. **RTT_WR.** DDR4 expects the termination to switch to a write-appropriate
   value *during write bursts* and back after them (JESD79-4). A static
   programming either over-terminates reads or under-terminates writes.
2. **RTT_PARK.** DDR4 adds a parked termination value (MR5) applied when no
   rank is selected — the idle state's impedance is a policy decision the
   standard exposes and boards exploit.

On top of the values, the **ODT pin itself is timed**: assertion and
de-assertion follow the command stream with defined latencies (the ODTL
family and the ODT turn-around timings, all named per JESD79-4 and all
runtime CSRs). Termination on DDR4 is not a setting; it is a schedule.

## What `odt_ctrl` owns

`odt_ctrl` is NEW. It is a policy block, not a datapath block — it touches
no DQ bits; it decides what the DRAM's termination does and when, and it
drives the ODT pin(s) accordingly.

| Responsibility | Detail |
|---|---|
| Policy state | current RTT selection per rank: NOM / WR / PARK, CSR-programmed values at init, runtime-selectable policy |
| Write-burst coupling | on the scheduler's write grants, switch the writing rank's termination to RTT_WR for the burst and back after — the coupling is a command-stream tap, not a datapath tap |
| Pin timing | the ODTL assertion/de-assertion latencies and ODT turn-arounds as runtime CSRs, enforced on the pin |
| Rank coupling | multi-rank ODT (the rank not being accessed terminates per policy) — exercised when `NUM_RANKS > 1`, dormant at the single-rank design point but not special-cased in structure |
| Scheduler interface | ODT decisions ride the same request/grant channel as other maintenance-class traffic — odt_ctrl never blocks a command to make a termination point |
| Telemetry | ODT state history and transition counts, so a termination policy sweep is measurable |

: Table 3.7: `odt_ctrl` responsibilities

**The init seam.** During initialization the DRAM holds ODT high-impedance
until CKE is registered active, then static — the init sequencer owns ODT
through that window exactly as scoria's does, and hands ownership to
`odt_ctrl` at the ready-for-operation boundary. Which block drives the pin in
which state is a named, bounded seam the MAS pins.

**LPDDR4.** LPDDR4 has no ODT pin; its termination (DQ ODT) is programmed
through the mode registers and is intentionally static for this edition —
absorbed into `mode_register`'s LPDDR4 maps and the init sequence. The
dynamic machinery above is DDR4-scoped, and the block's structure keeps that
scoping explicit rather than dead-genericing over a pin LPDDR4 doesn't have.

## Requirements

1. RTT_NOM, RTT_WR and RTT_PARK values are CSR-programmed at init from the
   board's decided values; the *policy* of when each applies is the block's
   logic.
2. Every ODT latency is a runtime CSR, named per JESD79-4, initialised from
   the design point's speed bin at CSR-derivation time (Ch 5).
3. ODT transitions never stall the command stream: the block consumes the
   schedule, it doesn't arbitrate it.
4. Telemetry distinguishes the policy states over time, so "dynamic ODT is
   on" is observable, and so is a policy that never leaves PARK.
5. Write CRC's exclusion (Ch 3.1) is recorded here too: CRC would couple to
   the write datapath and DM/DBI pins; its unblocking condition is named
   there.

## The one-sentence summary, because it is easy to miss

`odt_ctrl` is the smallest new block in this book and the most policy-shaped:
it watches the command stream and keeps each rank's termination pointed at
the right value at the right time — nothing more, which is exactly the
problem DDR4 sets.
