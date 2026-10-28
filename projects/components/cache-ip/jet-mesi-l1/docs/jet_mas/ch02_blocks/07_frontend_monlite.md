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

# CPU Front End and l1_monlite

**Status:** planned contract.

## Front end (`l1_cpu_frontend` + `jet_rsp_seq`)

The amber GAXI slave latch is unchanged: request accept, response drive.
Jet inserts the sequence-tag stamp at accept and the release-pointer wait
at response drive (ch02/04). A request is accepted only when the lookup
stage can take it (not stalled per ch02/01's STALL classes); a stalled
request holds `req_ready` low — the GAXI contract's natural backpressure,
no new signaling.

## Observer (`l1_monlite`, extended)

The drop-and-count MonBus observer is inherited with new event classes for
the J7 measurement (the full map is ch04/01):

- MSHR `alloc` / `merge` / `retire` events (with class and set index);
- MSHR occupancy gauge (sampled on every alloc/retire);
- WB occupancy gauge (sampled on capture/retire);
- hit-while-misses-outstanding events (carry the outstanding count — the
  hit-under-miss latency correlate);
- stall events per STALL class (MSHR-full / WB-full / set-oversubscribed /
  cross-class wait).

Drop-and-count is unchanged: the observer never stalls the observed path;
dropped events bump the drop counter, which the characterization sweep
reports alongside the metrics.
