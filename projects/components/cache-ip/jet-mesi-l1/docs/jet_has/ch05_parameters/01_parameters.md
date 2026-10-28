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

**Stub at 0.1–0.2; J1–J6 CLOSED 2026-10-28.** This chapter records the
inherited parameter discipline and the jet additions as decided.

## Inherited geometry

jet inherits the entire `amber_pkg` geometry. See [amber HAS ch05](../../../../amber-mesi-l1/docs/amber_has/ch05_parameters/01_parameters.md) for the core parameters, derived quantities, package contents, and the rule that the rig is not a parameter.

## Jet additions (decided 2026-10-28)

Only two of the once-pending rows remain elaboration parameters; the other
five decisions fixed BEHAVIOR, not knobs, and are constants in `jet_pkg`:

| Parameter | Range / value | What it controls |
|---|---|---|
| `MSHR_COUNT` | 2–16, default 8 (J1) | Number of outstanding misses; the J7 sweep knob. |
| `VICTIM_DEPTH` | 1–4, default 2 (J5) | Writeback-buffer depth for dirty evictions behind fills. |

| Fixed behavior | Value | From |
|---|---|---|
| MSHR organization | fully associative CAM by line address | J1 |
| Merge policy | exact-line aliases, no class escalation | J3 |
| Hit-under-miss | reads + writes to any resident line | J2 |
| Response order | out-of-order fills, in-issue-order responses | J4 |
| Congestion policy | strict stall; snoop priority over new CPU accepts | J6 |

: Table 5.0: jet parameters and fixed behaviors

## Status

`jet_pkg` extends `amber_pkg` with `MSHR_COUNT` and `VICTIM_DEPTH` plus the
MSHR-entry type definitions; the amber_pkg defaults remain the working
baseline for everything else.
