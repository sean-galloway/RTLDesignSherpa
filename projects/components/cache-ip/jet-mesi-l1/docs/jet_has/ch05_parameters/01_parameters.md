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

# jet_pkg and Build-Time Geometry

**Stub: open until J1 and J5 decide.** This chapter records the inherited parameter discipline and the pending jet additions. No parameter values are fixed here until J1 and J5 close.

## Inherited geometry

jet inherits the entire `amber_pkg` geometry. See [amber HAS ch05](../../../../amber-mesi-l1/docs/amber_has/ch05_parameters/01_parameters.md) for the core parameters, derived quantities, package contents, and the rule that the rig is not a parameter.

## Pending jet additions

The following parameters are jet-specific and cannot be defined until the named J-rows close:

| Parameter | Blocked by | What it controls |
|---|---|---|
| `MSHR_COUNT` | J1 | Number of outstanding misses the cache can track. |
| `MSHR_ASSOC` | J1 | Full-associative, direct-mapped-by-index, or CAM organization of the MSHR file. |
| `MERGE_POLICY` | J3 | Exact-line, range, or no merging. |
| `HIT_UNDER_MISS` | J2 | All resident lines, non-conflicting lines, or read-only. |
| `VICTIM_DEPTH` | J5 | Victim buffer depth for dirty evictions behind fills (0 = block like amber, 1–4 = decouple). |
| `RESPONSE_ORDER` | J4 | In-order CPU responses or out-of-order with ID tags. |
| `CONGESTION_POLICY` | J6 | Stall, drop-and-retry, or throttle when MSHRs are full. |

: Table 5.0: Pending jet parameters

## Status

No parameter values recorded. `jet_pkg` will extend `amber_pkg` after J1–J6 close. Until then, the amber_pkg defaults are the working baseline.
