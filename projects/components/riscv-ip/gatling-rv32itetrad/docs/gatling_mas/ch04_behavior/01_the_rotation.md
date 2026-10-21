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


# Micro-Architecture Behavior

## The rotation, cycle by cycle

```
cycle     t     t+1   t+2   t+3   t+4   t+5   t+6
F        c0    c1    c2    c3    c0    c1    c2
D              c0    c1    c2    c3    c0    c1
X                    c0    c1    c2    c3    c0
W                          c0    c1    c2    c3
```

Context c0's instruction i is fetched at t, decoded at t+1, executed at t+2 (its PC written at the end of t+2) and retired at t+3 (its register written at the end of t+3). Instruction i+1 is fetched at t+4 from the PC written two cycles earlier, and reads its registers at t+5, two cycles after the write. Consecutive retirements of one context are exactly four cycles apart; with all four running, retirements follow the rotation order, one per clock.

A context that is held or halted leaves its slot empty: the other contexts are not shifted into it, so each still retires once per window. This is measured: in DV every context's consecutive beats are checked to be four cycles apart, and on gatling_mem_bram a context's CYCLES/INSTRET is 4.000.

## Taken branches cost nothing

The branch decision and target are known in X and written to the context's PC at the end of X, two cycles before that context's next fetch. There is no wrong-path fetch to cancel, so no bubble, no flush and no prediction.

## Stopping and restarting a context

`hart_run[c]` low kills context c's instruction in whichever stage holds it -- the stage valid is re-qualified by `hart_run` everywhere -- and holds its PC at RESET_ADDR. Released, the context fetches RESET_ADDR in its next F slot with its retirement order at 0. DV stops a context at all four rotation phases (one per stage) and checks that nothing retires while it is held; a mutant that drops the qualification in W retires one leaked beat and is caught only by the stop in the W phase.
