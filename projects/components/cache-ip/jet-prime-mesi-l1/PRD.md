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

# jet-prime — Product Requirements

**Version:** 0.1 (2026-11-12)
**Status:** inherits every DECIDED row of [jet's PRD](../jet-mesi-l1/PRD.md)
(J1–J10) and, through it, amber's. This file carries only what jet-prime
adds. Unreleased: stays at one revision while the design is being thrashed
out.

## 1. Purpose

Make the lockup-free MESI L1 faster than OpenHW HPDcache on the house
single-cache rig without giving up anything jet proved: coherence, the ACE
snoop side, MonBus observation, golden-model parity, the FULL soak grid.
jet is frozen as the measured baseline; jet-prime carries the change.

## 2. Requirements jet-prime adds

| ID | Requirement | Status |
|---|---|---|
| JP1 | Cycles per transaction below HPDcache's at every depth 1..16 on `r64k_we64` and `r64k_we255` on the reference rig (same injector, memory, bridge, UART, 100 MHz). | open |
| JP2 | Resident hits stay at 1.0 cycle per transaction from depth 4; hit latency stays at jet's 3 cycles at depth 1. | open |
| JP3 | Several fills in flight per cache (one AXI ID per outstanding miss, R demuxed by ID); the response order contract (J4) unchanged. | open |
| JP4 | The pair fabric serializes per line, not globally: distinct lines proceed concurrently; same-line conflicts keep grant-after-completion. | open |
| JP5 | jet's FULL grid, pair-rig DV and `jet_control` formal (prove, prove-live, cover) stay green on the fork at every step; new concurrency gets its own pair-rig scenarios and a formal safety argument for JP4. | open |
| JP6 | Genesys2 at 100 MHz with positive slack on the reference-rig build and the pair-rig build. | open |

## 3. Non-goals

- Changing the shared common-ip core (`l1_*`); if a step needs it, it is a
  common-ip task with its own scope confirmation.
- Beating HPDcache on area. jet-prime carries a snoop side and monitors the
  references do not; the area row is reported, not targeted.
- Touching jet. Its lanes are closed and its numbers are the baseline.
