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

# Build-Time Geometry

**Stub: open until D4, D5, and D11 close.** This chapter records the parameters that the architecture will expose. No parameter values or package structure are fixed at 0.1.

## Candidate parameters

| Parameter | Candidate range | Blocked on | Notes |
|---|---|---|---|
| `N_MASTERS` | 2–4 | D11 | Number of cache-side ACE ports. Culsans uses 2–4 CVA6 cores. |
| Line size / cache geometry | Locked to amber geometry vs independent | D11 | Whether onyx assumes the cache line size/profile of amber or parameterizes independently. |
| Gather window depth | TBD | D4 | Number of snoop responses the gather engine can track simultaneously. |
| Scoreboard depth | TBD | D5/D10.8 | Number of same-address or outstanding transactions the serializer can hold; sized by the loaded-latency / bus-width / efficiency math in Chinnakonda §10.8. |
| AWID width | TBD | D5 | Width of the memory-side AWID if the unique-AWID freelist candidate is chosen. |
| CD/CR credit depth | TBD | N4 | Credit/capacity reserved for the snoop-data return path. |

## What the decisions drive

D11 fixes the top-level array dimensions and the DV matrix. D4 and D5 fix the internal buffer depths and therefore the area/timing footprint. D10.8 gives the sizing rule: derive outstanding-access capacity from average loaded latency, bus width, cache line size, and expected efficiency.

## Background material

Chinnakonda, *Designing a Multiprocessor Cache Subsystem*, §10.8 gives a sizing example: for 200-cycle DRAM latency on a 1 GHz 16-byte bus, ≈40 outstanding reads and ≈40 outstanding writes are needed to sustain 16 bytes/cycle at 80% efficiency. The numbers scale with bus width, frequency, and latency. §10.1 notes that banks should be ≥ master count, supporting N=2–4.

## Status

No parameters fixed. D4, D5, and D11 must close before `onyx_pkg` can be defined.
