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

# MonBus Event Emission Points

**Status:** planned contract. Emission-point discipline is amber's
(ch03/05): events emit at the committing edge of the thing they describe,
never at request acceptance, so the tallies count completed behavior.

| Event | Emission point |
|---|---|
| hit (read/write) | response release at `jet_rsp_seq`, with the outstanding-miss count in the payload |
| miss alloc | MSHR entry alloc (carries class + set) |
| merge | merge-list append (carries the entry's alloc age) |
| fill commit / retire | tag install at the commit pipeline |
| stall | one event per STALL class per stall cycle window (MSHR-full / WB-full / set-oversub / cross-class) |
| victim capture | WB entry alloc |
| drain retire | WB entry free at BRESP |
| snoop service | CR launch, with the answer-source tag (array / pending-fill / WB-snarf) |
| state transition | every tag write, as amber |
| occupancy gauges | sampled on every alloc/retire/capture/drain event |

The drop-and-count policy is unchanged: a full observer FIFO drops the
event and bumps the drop counter; the observed path never stalls.
