# Test Methodology

This chapter describes what is exercised on the FPGA block (Figure 2.1) and how
the results are judged. CDC Counter Display is a **demonstration**, so the
"measurement" is a coherence test of the clock-domain-crossing readback rather
than a throughput sweep.

## What is under test

The four `cdc_counter_domain` value-readback paths, each selectable among five
CDC strategies (`CDC_MODE` 0–4) and driven by an asynchronous source clock whose
rate the host can sweep. The question under test: **does the multi-bit counter
value cross into `sys_clk` coherently?**

## What is measured, and how

| Quantity | How it is obtained |
|----------|--------------------|
| Value coherence | Read `VALUE` by name N times; compute min / max / number of unique samples |
| Press determinism | After `count` `HOST_PRESS` pulses, check `VALUE == INIT + count*INCREMENT` and `PRESS_COUNT` delta |
| Reload | `CFG_LOAD` reloads `VALUE` to `INIT` without disturbing `PRESS_COUNT` |
| Mode selection | Each `CDC_MODE` code round-trips through the CSR and selects a distinct path |

: What is measured

A run configures a counter (mode, init, increment, clock), injects stimulus
(`HOST_PRESS` or `AUTO_INC`), then samples `VALUE`/`PRESS_COUNT` over the
by-name bridge. In the "watch-fail" workload the counter is put in NO-CDC with
`AUTO_INC = 1` and its source clock is swept slow→fast; the **spread and unique
count of the `VALUE` samples** is the metric — a few unique values means clean
crossing, a wide 0x00–0xFF spread means multi-bit skew.

## Workloads

| Workload | Purpose |
|----------|---------|
| `press` | Deterministic increment check (safe CDC mode) |
| `cfg_load` | Reload semantics |
| `cdc_mode` | All five mode codes round-trip |
| `watch_fail` | Sweep an unsafe crossing slow→fast and watch it break |

: Demonstration workloads

## The oracle, and what sim can/can't show

The oracle is the arithmetic expectation (`INIT + presses*INCREMENT`) for the
safe modes. In Verilator the NO-CDC path reads the *true* value (no metastability
model), so the sim asserts exact values even in mode 0 — the analog "garbage" is
a silicon-only effect. That asymmetry is the point of the demo, not a defect
(Chapter 6, Sim Equivalence).

## Measurement pitfalls

- NO-CDC garbage at speed is **expected** — use a safe `CDC_MODE` (2/3/4) before
  asserting exact values.
- `PRESS_COUNT` always uses Gray-coded CDC and stays coherent regardless of mode;
  prefer it when you need a trustworthy count.
