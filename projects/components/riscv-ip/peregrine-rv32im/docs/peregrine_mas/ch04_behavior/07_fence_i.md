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

# fence.i

## The Problem

The D\$ is write-back. Code written by stores may sit dirty in amber, where an I\$ refill (which reads memory) cannot see it, and instructions already fetched behind the `fence.i` are stale. So `fence.i` must clean the D\$, invalidate the I\$, and refetch everything younger (PRD P10).

## The Cached Sequence

1. `fence.i` reaches MEM with no exception and no interrupt: the core raises `fencei_req` (`mem_fencei_pend`).
2. `peregrine_top` holds the core (`mem_wait`, through "fence.i busy") and asks the clean engine for a clean-all. When nothing is outstanding the engine presents `{maint = 1, we = 0}` to amber; amber writes back every dirty line (WriteClean) and responds after the last B. `r_fi_clean_done` sets.
3. The wrapper raises the I\$ `inv_req`; the I\$ takes it when no refill is in flight, clears every valid bit and pulses `inv_ack`. `r_fi_done` sets.
4. The hold drops. The core commits `fence.i` like an ordinary instruction and redirects to its `pc + 4`, flushing IF/ID, ID/EX and the instruction leaving EX, all fetched before the invalidate.
5. `r_fi_clean_done` and `r_fi_done` clear when the core commits.

`fence.i` is also one of the instructions the interrupt lock protects: it has presented a request (the clean) during the hold.

## The Cacheless Build

There is nothing to clean: `fencei_req` stays 0. `fence.i` still commits in MEM and redirects to `pc + 4`, flushing the younger instructions (owner, 2026-11-25). Without the redirect, instructions already in the pipeline ran stale and riscv-arch-test `Zifencei` failed 2 of 6 signature words on the cacheless build.

## The External Clean

`dc_clean_req` uses the same engine: a TB raises it after the `tohost` store so the arch-test signature can be read from memory; `dc_clean_done` rises when the clean finishes. The core is held while it is pending. One clean satisfies every source pending when it finishes.

## Prediction

`fence.i` redirects, so the next instruction is fetched after it resolves; the TB's predictor model counts it as a redirect when it works out which predictor states a prediction may come from.

---

**Last Updated:** 2026-11-25
