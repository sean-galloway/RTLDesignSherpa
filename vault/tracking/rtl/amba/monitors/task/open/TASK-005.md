# TASK-005: monitors accept a global usync timer so all packets share a unique stamp

**Priority:** P2
**Status:** OPEN
**Owner:** TBD (monitors)
**Filed:** 2026-10-19 (owner request; scoped 2026-10-19)
**Related:** rtl/common/counter_freq_invariant.sv (the timebase),
rtl/amba/ocelus/axi_monitor_timer.sv (the per-monitor local timestamp it replaces)

## What

Today every monitor runs its own timestamp: `axi_monitor_timer.sv`
free-runs a 32-bit `r_timestamp` from reset, so two monitors on the same
fabric stamp the same wall-clock moment with different values, and nothing
can correlate an error packet from one monitor with a timeout packet from
another, or with stream/rapids/bridge/delta traffic stamped elsewhere.

Add a global **usync timebase** to the whole Ocelus fabric — "Ocelus" here
means the monitor fabric in general, so the consumers are not just the
rtl/amba monitors but every instrumentation point: stream, rapids, bridge,
delta, and the rest as they come online. Every emitted packet/error/event
carries a stamp from the one shared counter and can be merged/compared
downstream with no per-source offset correction.

## Timebase: build on counter_freq_invariant

The source counter is based on `rtl/common/counter_freq_invariant.sv`:

- microsecond ticks, frequency-invariant via the `freq_sel` LUT — the same
  usync value means the same real time whether the fabric runs at 33 MHz
  on a NexysA7 or faster silicon;
- `sync_reset_n` gives a fabric-wide t=0 (assert, release, every arm
  counts from the same instant);
- decide the width for usync use: the default 16 bits wraps at ~65 ms,
  which is likely too short for correlation across a soak — 32 bits
  (~71 min) or wider is the expected pick. Record the decision in the
  Ocelus docs.

## Distribution is critical

One source, placed in the **middle** of the fabric, fanning out to
**~12 arms**. Each arm is a matched chain of **2–4 flop stages** carrying
the counter bus. Rules:

- **Every arm has the same flop depth.** All consumers then sample the
  identical (delayed) value on the same clock, so any two packets stamped
  in the same cycle agree everywhere.
- If a consumer is physically close and 4 stages is more than it needs,
  that is fine — over-depth is harmless, it is still in sync with the
  others. Mismatched depth is the failure mode, not extra latency.
- Treat the arms like a clock tree: source-centric placement, balanced
  routes, no logic in the arms.
- If any consumer ever sits in a different clock domain, gray-code the
  counter across that boundary with a proper synchronizer — do not sample
  the binary bus combinationally.

## What to change

- New usync source module (likely in rtl/common, wrapping
  `counter_freq_invariant`) + the matched-depth arm/distribution structure.
- Monitor base / lite / reporter path takes the usync value as an input
  port feeding the packet stamp field in place of the local `r_timestamp`.
- Keep the local timer as a parameter-selectable fallback so existing
  testbenches and standalone monitor use keep working unchanged.
- Stream/rapids/bridge/delta instrumentation gets the same input port as
  those blocks add stamping — port name and width fixed once, here, so
  every consumer matches.
- Update the Ocelus plane docs (error/perf/debug/output planes): one
  timebase, every plane, distribution rules written down.

## Done when

- [ ] usync source + distribution arms exist; a multi-consumer testbench
      shows every arm presenting the identical value on the same cycle
- [ ] monitor packets can be stamped from the usync input
      (parameter-selected); a two-monitor testbench shows both monitors'
      packets on one timebase
- [ ] default (local-timer fallback) behavior is bit-identical to today;
      existing `val/amba` monitor suites pass unchanged
- [ ] stamp width/units and the distribution rules are written down in the
      Ocelus docs
