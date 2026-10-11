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

# Characterization

**Stub: open until RTL exists and success criterion 5 can be measured.** This chapter records the cost targets from the PRD. No characterization numbers exist at 0.1.

## Targets

Per PRD success criterion 5:

- Synthesis and implementation numbers (LUT/FF/RAM, fmax) on **Nexys A7** and/or **Genesys 2**.
- Results recorded in `docs/` the way `pumice` characterized.

## What must be measured

| Metric | Why it matters |
|---|---|
| LUT | Combinational cost of the decoder, serializer, fanout/gather, and adjudication logic. |
| FF | State for outstanding transactions, gather entries, serializer linked lists, and credit counters. |
| RAM | Any table storage (directory-lite if D3 chooses it), scoreboard, or gather buffer implemented in shared `sdpram_core`. |
| fmax | Timing closure on the house fabric at the target frequency. |

## Dependency on open rows

The exact cost cannot be estimated until D3 (broadcast vs directory-lite), D4 (gather mechanism), and D5 (serializer structure) close. The characterization plan will be added after the architecture is fixed.

## Status

No characterization numbers recorded. RTL and the open D-rows must land before this chapter can be filled.
