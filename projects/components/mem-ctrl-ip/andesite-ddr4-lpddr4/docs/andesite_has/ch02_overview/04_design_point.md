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

# The Target Design Point

## Named as of v0.1

There is deliberately no board. The 7-series targets this repo's boards carry
do not support DDR4, and a named board would be a promise this generation
can't keep. So the design point is stated as a **simulation target**: the
geometry, the data rates and the DFI boundary the parameters are chosen for,
verified against a DFI v4.0 bus functional model (Chapter 6). What follows is
what a future board target must match, not a claim that a bitstream exists.

| Item | Value | Source |
|---|---|---|
| DRAM, DDR4 side | DDR4-1600 x8, 4 bank groups × 4 banks = 16 banks, MT40A1G8-class | bootstrap spec §2 design point |
| DRAM, LPDDR4 side | LPDDR4-1600 x16, 8 banks per channel — ungrouped; the package offers two x16 channels | bootstrap spec §2; JESD209-4 |
| Data rate | 1600 MT/s both memtypes — 800 MHz CK, tCK 1.25 ns | arithmetic from the rate |
| PHY boundary | DFI v4.0, frequency ratio 1:4 carried from scoria | Ch 4 |
| Verification | DFI v4.0 BFM in simulation (BFM acquisition/study = andesite TASK-005) | Ch 6 |
| **Theoretical peak, DDR4 side** | **1600 MB/s** per x8 device — 1600 MT/s x 8 bit / 8 | arithmetic; the denominator for any bandwidth claim |
| **Theoretical peak, LPDDR4 side** | **3200 MB/s** per x16 channel — 1600 MT/s x 16 bit / 8 | arithmetic; same rule |

: Table 2.4: The target design point

**The denominator rule applies from this page on.** Any bandwidth figure
quoted anywhere in this book or its successors carries the theoretical
maximum beside it. pumice learned this twice — a byte counter that was
per-phase, and a percentage with no peak beside it — and the family doctrine
keeps the lesson.

## What this fixes

Build-time parameters the architecture left open now have values; everything
else stays a runtime CSR:

| Parameter | Value | Why it is forced |
|---|---|---|
| DFI frequency ratio | 1:4 | carried from scoria — the datapath's phase structure transfers at the gear it was verified at |
| DDR4 geometry | per Table 2.4 | the DDR4 design point; build-time because it sizes decode, not because it varies |
| LPDDR4 geometry | per Table 2.4 — ungrouped | the LPDDR4 design point; same rule |
| DQ width | x8 (DDR4) / x16 (LPDDR4) | the design point's devices |
| `NUM_RANKS` | 1 | single-rank design point, as scoria's was |

: Table 2.5: Build-time parameters fixed by the design point

Note what is *not* in the table: every timing. tCCD_L/S and tRRD_L/S are
runtime CSRs exactly like their plain ancestors, and the JEDEC speed-bin
values that initialise them belong to the CSR derivation (Chapter 5), cited
to JESD79-4 / JESD209-4 — the standards live in cold storage, not the repo,
per the house rule.

**The 1:4 ratio is the same happy accident scoria had.** pumice and scoria
both run four DFI phases, so the inherited DFI datapath — the async-FIFO CDC,
the per-phase pipelines — transfers at the gear it was built and verified at.
DFI 4.0's frequency-ratio options beyond 1:4 are named in Chapter 4 and left
for a board PHY to justify.

## What is still open

Nothing in the design point itself. Three adjacent choices are recorded as
open questions in Chapter 6 rather than decided here: CA-parity scope
(hardware counter vs firmware assist), the gear-down coverage scope for the
BFM, and LPDDR4 channel count beyond the one-channel design point.
