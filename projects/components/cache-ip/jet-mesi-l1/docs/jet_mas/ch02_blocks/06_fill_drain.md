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

# Fill and Drain Engines

**Status:** planned contract. Both engines are the unchanged amber FUBs;
this chapter records how jet drives them differently, not new engines.

## `l1_fill` under MSHRs

- `jet_control` (via `jet_mshr`) launches a fill when an entry allocates;
  the engine's AR goes out as soon as the AXI4 read channel accepts it.
- **Single AXI4 read ID (v1):** ARs issue in alloc order and R beats return
  in the same order — the memory side serializes fills (design spec §2).
  MSHR concurrency is still what the experiment measures: hits proceed
  under fills and merges remove duplicate fetches entirely.
  **Task-8 landing note:** the landed `l1_fill` is single-outstanding
  (F_IDLE→F_AR→F_R→F_DONE) with no accept output, so `jet_top`'s launch
  adapter serializes the launches — one fill in the engine at a time, the
  next launch accepted the cycle after `fill_done`, and never while a
  victim capture streams (the cap_busy contract, enforced at the launch
  since the engine cannot be gated — see ch02/01's Task-8 notes).  True
  AR pipelining remains the future step below.
- Each R beat writes the data array at top W-port priority and marks
  `beats_rcvd` in its MSHR entry (PF_GUARD feed). `fill_done` (last beat +
  response handshake) triggers the commit pipeline.
- **PassDirty (amber #106):** the fill's RRESP PassDirty flips the entry's
  install state to M before commit. Inherited unchanged.
- Parallel fills (multiple read IDs, out-of-order R) are a future step if
  the J7 sweep shows the memory port as the residual bottleneck; the MSHR
  file already records everything a multi-ID fill engine would need.

## `l1_drain` under the WB buffer

- The engine pulls the oldest valid WB entry whenever the AXI4 write
  channel is free: AW, W beats from the entry, BRESP retires it.
- Drains never wait on fills (independent channels, per the ACE-style
  two-channel rule — Chinnakonda §10.10) and never wait on snoops (snoops
  snarf from the buffer).
- **AWID:** the amber wrapper drives a single ID; drains serialize on the
  write channel, which the WB buffer's depth absorbs. The book's
  AWID-freelist scheme (§10.10.2) is the recorded upgrade path if drain
  bandwidth shows up in the sweep.

## Engine sharing corners

- A fill and a drain can both be in flight (different channels) — the J5
  decoupling's whole point.
- Write-back of a line whose fill is ALSO pending (the victim's line and
  the fill's line differ by construction — victim is in the fill's set, not
  the same line) cannot alias: the WB compare and MSHR CAM are both checked
  at lookup (the PoS sees both).
