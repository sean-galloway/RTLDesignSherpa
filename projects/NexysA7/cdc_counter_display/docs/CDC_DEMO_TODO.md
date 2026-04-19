# CDC Demo Project — TODO

**Parent:** `projects/NexysA7/cdc_counter_display/`
**Status:** Planning
**Purpose:** Turn this demo into a teaching vehicle that shows (1) when to use each of the four CDC primitives in this repo, (2) what goes wrong without CDC, and (3) the "it works in simulation / sometimes in silicon" cases that trap beginners.

---

## 1. The Four CDC Primitives

| # | Module | Location | One-line purpose |
|---|---|---|---|
| 1 | `cdc_synchronizer`          | `rtl/amba/shared/cdc_synchronizer.sv`          | 2- or 3-FF synchronizer for a single quasi-static control bit. |
| 2 | `cdc_2_phase_handshake`     | `rtl/amba/shared/cdc_2_phase_handshake.sv`     | Toggle / NRZ handshake for word-at-a-time data with throughput focus. |
| 3 | `cdc_4_phase_handshake`     | `rtl/amba/shared/cdc_4_phase_handshake.sv`     | Req/ack level handshake — classic, conservative, debug-friendly. |
| 4 | `fifo_async` / `fifo_async_div2` | `rtl/common/fifo_async*.sv`               | Gray-pointer asynchronous FIFO for sustained streaming data. |

Supporting primitives (not counted as top-level "types" but worth noting):
- `sync_pulse.sv`   — edge-to-pulse converter built on a synchronizer.
- `reset_sync.sv`   — specialization of `cdc_synchronizer` for async-assert / sync-deassert resets.
- `bin2gray` / `gray2bin` — used internally by `fifo_async`.

---

## 2. Selection Guide — When to Use Which

### Type 1 — `cdc_synchronizer`
**Use for:** a single-bit control/status signal that is *quasi-static* or where occasional missed pulses are acceptable.

Examples:
- An enable/mode bit written once at boot.
- An interrupt request line that stays high until acked.
- A reset signal (use `reset_sync` variant).

**Do NOT use for:**
- Multi-bit buses (bit skew across the synchronizer will produce Franken-values).
- Short single-cycle pulses where a lost pulse is unacceptable (use `sync_pulse` or a handshake).
- Data that changes faster than `SYNC_STAGES` destination clocks.

### Type 2 — `cdc_2_phase_handshake`
**Use for:** transferring a multi-bit data word, one beat at a time, when throughput matters and the two clocks are unrelated.

Examples:
- Configuration register writes from a slow APB domain into a fast datapath domain.
- Occasional descriptor handoffs between a control plane and a data plane.
- Interrupt payload delivery (interrupt ID + vector data).

**Trade-off:** Half the round-trips of 4-phase → roughly 2x throughput. Edge-detection logic is slightly more complex to reason about.

### Type 3 — `cdc_4_phase_handshake`
**Use for:** same problem space as 2-phase, but when you want the textbook level-based protocol — easier to debug in a waveform viewer, tolerant of most review/lint tools, and the safer default for a first implementation.

Examples:
- First cut of any word-at-a-time CDC before optimizing.
- Protocols where reviewers / formal engineers expect classic req/ack waveforms.
- Designs where the extra latency does not matter.

### Type 4 — `fifo_async` (gray-pointer async FIFO)
**Use for:** sustained streaming data between clock domains with bursts, backpressure, and throughput requirements.

Examples:
- UART RX bytes streaming from a serial clock domain into a system clock domain.
- Video pixel stream from a pixel clock into a memory-controller clock.
- Any producer/consumer where instantaneous rates differ but average rates are compatible.

**Cost:** Highest resource usage of the four (dual-port memory + gray pointer encoders + synchronizers on both sides). Overkill for single-word occasional transfers.

### Quick Decision Tree

```
Is the signal 1 bit?
├── Yes → quasi-static or OK to miss pulses?
│       ├── Yes → cdc_synchronizer (or reset_sync for reset)
│       └── No  → sync_pulse (edge pulse synchronizer)
└── No (multi-bit):
    ├── Sustained streaming / burst traffic?  → fifo_async
    └── One word at a time, occasional?
        ├── Throughput matters         → cdc_2_phase_handshake
        └── Debug/clarity matters more → cdc_4_phase_handshake
```

---

## 3. What Happens If You Skip CDC

Four failure modes, in order of how often they trap people:

### 3a. Metastability
A destination-domain flop samples a source-domain signal during its setup/hold window. The flop output hovers at an analog intermediate voltage for an unbounded (but probabilistically decaying) time. Downstream logic sees either `0` or `1` — or, worse, different fan-out endpoints see different values.

**Symptom:** intermittent, non-reproducible bugs that survive reset and only appear at certain junction temperatures or voltage corners. Classic "works on my bench, fails in the field."

### 3b. Multi-bit Bus Skew (re-convergence)
A multi-bit bus is routed across clock domains with individual flops per bit. Each bit's metastability resolves independently, so for one destination clock edge half the bits have the new value and half have the old value. The sampled word is a **value that was never present on the source side**.

**Symptom:** one-off values appearing in FIFOs, counters jumping to impossible states, addresses decoding to unallocated slaves.

### 3c. Protocol-level Deadlock
A "synchronizer" is applied to both halves of a handshake (req and ack) independently, without the protocol that makes them safe together. The receiver sees req asserted, asserts ack, but the source never sees the ack because the synchronizer delay lands the ack observation in the same cycle the source drops req. The whole protocol wedges.

**Symptom:** works most of the time, hangs permanently after some number of transfers.

### 3d. Async FIFO Pointer Corruption (using binary pointers)
Someone "saves area" by using a binary counter for the async FIFO's read and write pointers and synchronizing both. Multi-bit skew (3b) on the pointer comparison logic means `full` / `empty` flags transiently report wrong values. Reads past empty return garbage; writes past full corrupt the newest entries.

**Symptom:** silent data loss or duplication in streaming data paths.

---

## 4. When a Broken Design "Just Works" (The Trap)

Beginners often write code that crosses clock domains without any CDC primitive, run a testbench, see it pass, and conclude the design is fine. It isn't — they got lucky. The common reasons:

### 4a. Source signal is static
If the signal never changes during the test window (e.g., a register written once at power-up), there are no transitions that can be sampled mid-flight. Add a second write from the source domain and the bug appears.

### 4b. Frequency ratio is integer and phase-related
If `f_dst = N · f_src` and the clocks are derived from a common PLL, every source edge lines up with a destination edge — setup/hold is always met. Change the ratio to a non-integer (or use two independent oscillators) and the design breaks.

### 4c. Source clock is much slower than destination
If `f_dst >> f_src`, destination flops see a stable source value for many consecutive cycles. Even a naive crossing looks "safe" because the metastability window is a tiny fraction of any given sample. Swap the direction (slow destination, fast source) and it falls apart.

### 4d. Simulator assigns deterministic values
Pure RTL simulators do not model metastability at all — a flop that sees a setup-violating transition just takes the new value. You need a gate-level SDF simulation, or an explicit metastability injector in the testbench, to see the bug in simulation. **This is why RTL-only regressions will happily green-light broken CDC.**

### 4e. Test runtime is too short
Metastability failure is a probabilistic event. The MTBF (mean time between failures) for a single unsynchronized flop can be microseconds to years depending on technology. A 100 µs simulation may never hit the bug; a 24 h bench run will.

### 4f. Data is slow-changing compared to the test's observation window
A counter that ticks every 1 ms observed by a 100 MHz sampler has 99,999 cycles of stable value for every transition. The transition is statistically invisible in a short run.

**Lesson:** passing simulation is not evidence of CDC correctness. Correctness comes from structural rules (every crossing goes through a known-good primitive) and timing closure (SDC constraints). Simulation is, at best, a sanity check.

---

## 5. Demo Build Plan (concrete TODO list)

Five sibling top-levels (or one parameterized top with a `DEMO_MODE` generate), each driving the same 4-digit 7-segment display from a button-driven counter, but using a different CDC strategy. Each variant gets its own bitstream target and a waveform checklist.

- [ ] **`demo_1_synchronizer/`** — Sync a 1-bit "counter overflowed" flag from `btn_clk` to `disp_clk` via `cdc_synchronizer`. Display domain latches the flag and flashes all seven segments.
- [ ] **`demo_2_2phase/`** — Replace the counter-value CDC in the current top-level with `cdc_2_phase_handshake`. Add a cycle counter in each domain to measure round-trip latency vs 4-phase.
- [ ] **`demo_3_4phase/`** — Current implementation (baseline). Keep as-is for reference waveforms.
- [ ] **`demo_4_async_fifo/`** — Push every counter update into a small `fifo_async` and have the display pop one per display refresh. Deliberately stream faster than the display can consume to exercise backpressure.
- [ ] **`demo_5_broken_no_cdc/`** — Wire `r_count_value` directly across domains with no synchronizer. Document expected symptoms.

Plus two "lucky cases" that highlight the trap in Section 4:

- [ ] **`demo_5b_broken_but_static/`** — Same broken wiring as 5, but the counter is only updated once (by a single button press). Show that the display reads the correct value every time in simulation, then show the multi-bit skew in a gate-level run.
- [ ] **`demo_5c_broken_but_slow/`** — Same broken wiring, but `btn_clk` is divided down to 1 Hz. Show the design appearing to work on the bench and then constructing a scenario (cross-domain read during the ~1 ns setup window around a counter increment) where it fails.

### Per-variant deliverables
For each demo directory:
1. `rtl/*.sv` — the variant's top-level.
2. `sim/test_*.py` — a cocotb test that reproduces the variant's intended behavior.
3. `docs/README.md` — one page: what the variant demonstrates, expected waveform, expected failure mode (for 5/5b/5c).
4. XDC constraints for the Nexys A7 with the relevant `set_max_delay -datapath_only` entries for the CDC variants.
5. Optional: a GTKWave save file pinned to the signals the reader should watch.

### Cross-variant deliverables
- [ ] A top-level `docs/COMPARISON.md` with a table: variant → resource usage (LUT / FF / BRAM) → max throughput → latency → failure mode.
- [ ] A `sim/run_all_variants.sh` that runs each variant's cocotb test.
- [ ] A short lab write-up explaining how to observe failure on hardware: e.g., sweep the button press rate until the display shows impossible values in variant 5.

---

## 6. Open Questions

- Whether to combine variants into one parameterized top-level (`DEMO_MODE = 1..5c`) vs five sibling top-levels. Sibling dirs are clearer for readers; one parameterized top is less code to maintain.
- Whether the "broken" variants should be merged into a single `demo_broken/` with a `BROKEN_MODE` parameter, since their RTL differs only in one wire.
- Whether to include a metastability injector in `sim/` (a helper that on every clock edge randomly delays the source signal by a fraction of a destination clock) so the RTL sim can actually show failure in demos 5/5b/5c. Likely yes — this is the only way RTL-only regressions can demonstrate the bug.
- Power/area comparison needs Vivado synthesis — decide if that's in scope or a follow-up.

---

## 7. Not In Scope

- Formal verification of the CDC primitives themselves — they already live under `formal/amba/{cdc_handshake, ...}/`.
- New CDC primitives — this demo uses what the repo already has.
- Non-Nexys-A7 boards.
