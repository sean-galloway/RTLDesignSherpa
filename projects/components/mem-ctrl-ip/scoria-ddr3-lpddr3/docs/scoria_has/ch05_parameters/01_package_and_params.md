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

# scoria_pkg, and Build-Time vs Runtime

## The package (decision D3)

scoria gets its own `scoria_pkg`, with a one-bit memtype enum:

```systemverilog
typedef enum logic {
    MEMTYPE_DDR3   = 1'b0,
    MEMTYPE_LPDDR3 = 1'b1
} memtype_e;
```

It does **not** extend `pumice_pkg`. That package's `memtype_e` is one bit wide
and already spent on `{DDR2, LPDDR2}`; adding two more members means widening the
field, which reaches pumice's RTL and its CSR — a measured, shipping design —
for the benefit of a controller with no RTL. The trade is wrong in that
direction.

**When this changes.** At the start of the DDR4/LPDDR4 controller, a shared
`mem_ctrl_pkg` with a two-bit memtype becomes worth the migration, and both
existing controllers move to it in the same pass. That is the right moment
because the cost is paid once with three members to amortise it.

**Note:** until then `scoria_pkg` and `pumice_pkg` carry near-identical type
definitions. The duplication is deliberate and time-boxed. It is recorded here so
that a later reader does not "fix" it by widening pumice's CSR — which is
precisely the thing this decision avoids.

**Inherited from pumice's package:** the row field is already 18 bits wide, with
the comment "DDR3 forward-compat". That was written in anticipation of this
controller and carries over as-is.

## The rule: timings are runtime, geometry is build-time

Inherited from pumice and restated because it is the single most load-bearing
convention in the family:

**Every enforced timing is a runtime CSR.** Not a parameter. A timing compiled in
cannot be swept, and a controller whose timings cannot be swept cannot be
characterized — which is how a controller ends up with numbers nobody can
explain.

**Build-time is reserved for what cannot be runtime:** bus widths, the DFI gear
ratio, CAM depths, bank and rank counts. The test is whether changing it changes
the amount of hardware.

| Kind | Build-time or runtime | Examples |
|---|---|---|
| Bus and geometry | build | data width, address width, `NUM_BANKS`, `NUM_RANKS`, CAM depths |
| DFI gearing | build | `DFI_RATE`, which must equal the PHY's phase count |
| Memtype | build | `MEMTYPE_DDR3` / `MEMTYPE_LPDDR3` |
| JEDEC timings | **runtime** | every command-spacing and recovery parameter |
| New DDR3 timings | **runtime** | `tZQinit`, `tZQoper`, `tZQCS`, `tWLMRD`, `tWLDQSEN`, `tWLO`, `tWLOE` |
| Policy selects | **runtime** | page policy, refresh mode (all-bank vs `REFpb`), ZQCS interval |

: Table 5.1: Build-time versus runtime

**Important — `DFI_RATE` must equal the PHY's phase count, set identically on
both sides.** This is inherited and it is not negotiable: a mismatch is not a
performance problem, it is a functional break, and it is the kind that presents
as data corruption rather than as an error.

## New CSR groups

The register set grows by three groups. Exact offsets are not fixed in this
edition — they come from the RDL, which is authored with the RTL — but the
content is specified:

| Group | Contents |
|---|---|
| ZQ | `tZQinit`, `tZQoper`, `tZQCS`, the ZQCS interval, and a count of calibrations issued |
| Write leveling | `tWLMRD` (with its controller-defined maximum as a timeout), `tWLDQSEN`, `tWLO`, `tWLOE`, per-CS result, and the `*_STATS` telemetry of Chapter 3.3 |
| Refresh mode | all-bank versus `REFpb` select, for LPDDR3 |

: Table 5.2: New CSR groups

**Note:** `tWLMRD`'s maximum is a *scoria* number, not a JEDEC one — JESD79-3F
declares it controller-dependent. It appears in the CSR as a timeout with its own
status bit, so that a leveling attempt which never reports is distinguishable
from one that reports no flip.
