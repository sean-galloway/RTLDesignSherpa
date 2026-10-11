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

# Future Hooks

The following items are explicitly out of scope for jet v1.0 but are recorded as hooks so the architecture does not accidentally close them off.

| Hook | Why it is future work | How jet leaves the door open |
|---|---|---|
| Speculative prefetching | jet PRD non-goal | MSHRs and the fabric master stack can accept prefetch fills as additional miss entries; prefetch training discipline is §13.4 of Chinnakonda. |
| Hit predictor | timing/power optimization, not a v1 requirement | The tag array and hit path remain modular; §9.14 of Chinnakonda describes the predictor structure. |
| Tag-less cache | power/area optimization, not a v1 requirement | The tag array interface is preserved; §9.13 of Chinnakonda describes the TLB-integrated valid-bit approach. |
| Mem-copy interaction | streaming benchmark optimization | The MSHR file and victim buffer can be bypassed or hinted once mem-copy detection is added; §11.1–11.3 of Chinnakonda describe the L1/L2 tradeoffs. |
| Multi-banked parallelism | Beyond what MSHRs imply | The single cache core boundary is preserved; banking is a later core refactor. |

: Table 6.0: Future hooks

## Closing J1–J7

Closing the open J-rows will produce either a revised HAS or the MAS, depending on whether the decisions stay at architecture level or move into micro-architecture. Until then, the current directions are recorded in the stub chapters of this book.
