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

# jet — Lockup-Free MESI Snoopy L1 Cache

Second IP of the [`cache-ip/`](../) gemstone family: the
non-blocking upgrade of [`../amber-mesi-l1/`](../amber-mesi-l1/). Everything
amber proves — MESI coherence, snoop transport, storage arrays, MonBus
observation, golden-model parity — carries over unchanged; jet adds
miss-status holding registers, hit-under-miss, and miss merging, and
measures what they buy. Jet-fast, same gemstone seam as amber (fossilized
wood).

## Status

**Scaffolded 2026-10-04** — README + PRD only. `rtl/`, `dv/`, `docs/` are
placeholders; no RTL, no testbench. Depends on amber: this IP starts the day
amber's PRD decisions are DECIDED, reusing its protocol and arrays.

## What it adds over amber

- **MSHRs** — a small table of outstanding misses, so the cache keeps
  serving hits (and new allocations) while fills are in flight.
- **Hit-under-miss** — reads to resident lines proceed during a fill.
- **Miss merging** — later misses to the same line join the outstanding
  entry instead of issuing duplicate memory traffic.
- **The measurement** — same traces, same board, same MonBus counters as
  amber: the pair's hit-latency and bandwidth delta is the research result.

## Layout

`rtl/`, `dv/`, `docs/` placeholders; same per-component layout and mandatory
rules as amber (see
[`../amber-mesi-l1/README.md`](../amber-mesi-l1/README.md)). Binding
requirements and open questions: [PRD.md](PRD.md).
