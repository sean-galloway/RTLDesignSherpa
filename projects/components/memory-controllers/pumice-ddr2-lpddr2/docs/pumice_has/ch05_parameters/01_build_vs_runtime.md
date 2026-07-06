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

# Build-Time vs. Runtime Configuration

This controller distinguishes between **build-time parameters** that set the silicon footprint and **runtime CSR registers** that select behavior within that footprint. The two layers serve different purposes and should not be confused. This chapter applies the principle to every configurable knob in the design.

## Principle

| Layer | What it controls | Frozen at | Cost of changing |
|---|---|---|---|
| **Build-time parameter** | Synthesized silicon footprint: signal widths, table depths, queue sizes, instantiation counts, encoder selection, MAX bounds of runtime values | Elaboration time | Full RTL rebuild + place-and-route + tape-out (silicon) or bitstream rebuild (FPGA) |
| **Runtime CSR register** | Behavior selection *within* the synthesized footprint: policy choices, threshold values, on/off toggles, active counts up to the build-time MAX | Programmable any time the configuration quiet point is reached (typically during init or under SoC orchestration) | A single APB write |

The architectural rule is straightforward: **if a knob is changing silicon area, it must be build-time. If a knob is only changing behavior of already-synthesized hardware, it must be runtime.**

## Why This Distinction Matters

A controller designed without this distinction tends to collapse one of two ways:

- **Too much build-time** — every algorithmic choice is a parameter that requires a new bitstream / silicon revision to evaluate. Characterization becomes impossibly slow; post-silicon debug becomes impossible. Most academic prototype controllers fall here.
- **Too much runtime** — every option is always synthesized, including ones that will rarely be used. Area balloons; timing closure suffers; the design becomes harder to verify because every code path is live. This is the failure mode of "ultra-configurable" commercial IP.

This controller targets the middle: **build-time picks what's physically present; runtime picks what's active.**

## The Hybrid Pattern: "Build-Time MAX + Runtime Active"

Many of this controller's knobs follow a hybrid pattern where the build-time parameter sets a synthesized MAX, and a paired runtime CSR field selects the actually-used value within that MAX.

Concrete example for `LOOKAHEAD_DEPTH`:

```
Build-time:    LOOKAHEAD_DEPTH_MAX = 4
               → synthesizes 4 row-address comparators per bank machine

Runtime CSR:   sched_tuning.lookahead_active [3:0]
               → scheduler peeks min(LOOKAHEAD_DEPTH_MAX, lookahead_active)
                 same-bank requests per cycle

For debug:     Write lookahead_active = 0 to force pure HAPPY/page-policy mode
               Write lookahead_active = 4 to use the full synthesized window
               No rebuild required.
```

The same pattern applies to `TXN_QUEUE_DEPTH`, `AGE_MAX`, `REFRESH_DEFER_MAX`, `INIT_ZQ_RETRIES`, `ZQCS_FREQ_HZ`, and others — area is paid once at synthesis for the MAX; runtime selects how much of the synthesized hardware is actively gated.

## The "Build-Time + Runtime Mux" Pattern

For algorithmic choices where multiple alternatives have similar area cost, the build-time parameter selects **which** code paths are synthesized, and a runtime CSR field picks **which** of the synthesized paths is active.

Concrete example for `PAGE_POLICY`:

```
Build-time:    PAGE_POLICY = HAPPY_HYBRID
               → synthesizes OPEN, CLOSE, and HAPPY decision logic
                 (plus the HAPPY predictor table)

Runtime CSR:   refresh_tuning.page_policy_or [1:0]
               00 = use build-time default (HAPPY_HYBRID here)
               01 = force OPEN
               10 = force CLOSE
               11 = force HAPPY_HYBRID

For debug:     Sweep policies on real workloads with no rebuilds.
```

The build-time choice `PAGE_POLICY = OPEN` would have omitted the HAPPY predictor table from the synthesized design entirely, saving area but losing the ability to switch to HAPPY at runtime. The build-time choice `PAGE_POLICY = HAPPY_HYBRID` synthesizes everything, paying the area cost for the predictor table, in exchange for the ability to switch among any of the three at runtime.

The same pattern applies to `REFPB_POLICY`, `ADDR_MAP_SCHEME`, `SCHEDULER_MODE`, and HAPPY enable/disable.

## The "Runtime Only" Pattern

A small number of knobs have zero area cost and are runtime-only: simple counter compare values, timeout thresholds, retry counts. Examples include `ZQCS_FREQ_HZ`, `INIT_ZQ_RETRIES`, and the various observation-counter clear-on-read controls.

These have no build-time presence at all.

## Configuration Quiet Points

Runtime CSR writes that change scheduler or refresh-manager behavior take effect at the next **configuration quiet point** — defined as: no DRAM commands in flight, no refresh sequence in progress, and the relevant FSM in its idle state. The CSR slave does not enforce quiet-point writes; the SoC firmware is responsible for sequencing. Writing during normal operation is well-defined but the change does not apply until the next quiet point — which can be enforced by writing to the `CTRL.config_apply` strobe to force a brief drain.

Writes to register-file CSRs that have no FSM impact (timing parameter overrides, MR override values, observation counters) take effect immediately and have no quiet-point requirement.

## Summary

The following two chapters document this controller's complete configuration interface:

- **§5.2 Top-Level Parameter Table** — every build-time parameter, with its type, range, governing section, and (where applicable) the paired runtime CSR field.
- **§5.3 Characterization Knobs** — the subset of build-time + runtime knobs intentionally exposed for performance sweeping during silicon / FPGA characterization.

The full runtime CSR register map is in §6.3.
