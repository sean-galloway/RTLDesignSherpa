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

# JEDEC generation deltas

**Version:** 0.1 (stub)
**Date:** 2026-10-04
**Status:** v0.1 stub — purpose and pointers only, per the docs tranche plan.
The DDR2→3→4 / LPDDR2→3→4 reuse tables land once the andesite HAS ch03
delta work exists to summarize.

## What this will own

The family-level reuse argument across the JEDEC generations: which DRAM
behaviors survived each generation jump unchanged (and therefore ride in the
shared core), which ones moved into the shared timing-struct inventory, and
which ones are genuinely per-generation. This is the document that answers
"why does one engine cover both DDR and LPDDR?" for a reader who wasn't in
the room.

## Pointers until then

- scoria's foundation document is the worked example of a generation delta:
  `scoria-ddr3-lpddr3/docs/design-requirements.md` (the delta analysis against
  JESD79-3F, JESD209-3C, DFI v3.1 and v2.1.1, with decisions D1–D3).
- scoria's HAS ch03 carries the same argument in book form, block by block:
  `scoria-ddr3-lpddr3/docs/scoria_has/ch03_architecture/`.
- The andesite study book on LPDDR4 (referenced, not rewritten by the
  tranche) is under `andesite-ddr4-lpddr4/docs/simplified_lpddr4/`.
- The advanced-modes roadmap — what the generations add beyond the commodity
  baseline — is `vault/Tasks/projects/components/mem-ctrl-ip/memory-controllers/ADVANCED_MODES_ROADMAP.md`.
