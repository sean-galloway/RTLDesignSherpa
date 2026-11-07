# CDC failure modes, and why broken CDC passes

Background reading for the CDC counter display demo: what goes wrong when a
crossing has no CDC, and why a broken crossing so often passes simulation and
even a bench test. The demo board shows several of these live (table below).

**Which primitive to use** is not repeated here. The rtl-cdc book is the one
copy: [overview](../../../../../../docs/markdown/rtl-cdc/overview.md) for the
decision, [cdc.md](../../../../../../docs/markdown/rtl-cdc/cdc.md) for each
primitive (`cdc_synchronizer`, `cdc_2_phase_handshake`,
`cdc_4_phase_handshake`, `cdc_open_loop`, `fifo_async`, `sync_pulse`,
`reset_sync`), all under `rtl/cdc/`.

## What the demo shows

`CDC_MODE` per counter (`docs/HARNESS.md`):

| Failure or trap | Shown by | How |
|---|---|---|
| 3b multi-bit bus skew | mode 0 NO-CDC | `watch-fail`: garbage on the 7-seg as the source clock rises |
| 4c / 4f slow source looks safe | mode 0 NO-CDC | the slow end of the same sweep reads clean |
| "tuned to work" (a timing assumption, not a protocol) | mode 1 STRETCH (`cdc_open_loop`) | clean below its ~20-25 MHz design ceiling, broken above it |
| 4b integer, phase-related clocks | avoided by construction | the four counter clocks are MMCM outputs with co-prime divisors (11/29/67/128) |
| 4d the simulator cannot show it | the sim itself | the cocotb test passes in mode 0; the board does not |
| 3a metastability, 3c handshake deadlock, 3d binary-pointer FIFO | not demonstrated | described below only |

Safe modes 2 (`fifo_async`), 3 (`cdc_2_phase_handshake`) and 4
(`cdc_4_phase_handshake`) stay clean at every clock.

## What happens if you skip CDC

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


## When a broken design "just works" (the trap)

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
