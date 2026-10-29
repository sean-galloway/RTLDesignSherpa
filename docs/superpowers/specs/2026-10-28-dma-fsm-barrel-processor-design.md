# DMA FSM to Barrel RV32I Article Design

**Date:** 2026-10-28
**Status:** Implemented and validated, 2026-10-28
**Working title:** *When Should a DMA’s FSM Become a Processor?*

## Intent and audience

Write a Medium article for FPGA/ASIC designers and performance-oriented embedded engineers. The article is a measured cost/benefit analysis of replacing high-performance DMA scheduler FSMs with an N-context barrel-scheduled RV32I processor. It must help readers decide when that replacement fits their workload; it must not advocate universal replacement.

Use RAPIDS and rapids-g as the central case study, then generalize the lessons to other high-performance DMAs, including STREAM. The repository already contains register-compatible FSM and firmware implementations sharing a datapath, cycle-matched board results, scheduler-limit measurements, area/timing results, and equivalence/mutation evidence. This makes a measured comparison possible without inventing a hypothetical design.

## Terminology and thesis

“Barrel RV32I” means one RV32I datapath serving N independent hardware contexts in strict round-robin rotation. The core can issue one instruction per cycle in aggregate; each context issues at most one instruction every N cycles. It does not mean an N-wide superscalar processor or a general-purpose host CPU.

The thesis is workload-dependent replacement:

- Firmware sequencing pays when transfers or chains are large enough to hide per-descriptor work, or when evolving policy and field flexibility justify the overhead.
- Fixed FSMs or hardware assistance win for tiny descriptors, strict lone-channel latency, and operations that must complete at the engine rate, especially per-cycle EXT address generation.
- The correct boundary is not “hardware versus software”; it is policy and bookkeeping in firmware versus cycle-critical operations in hardware.

## Narrative and reader promise

Use “the crossover point” narrative. Start with this first-person origin story, correcting only spelling and the book title: “I made notes from *Computer Organization and Design* by Patterson and Hennessy. This was for a future project, but I wanted to try this out.” Then introduce two apparently contradictory measurements from the same 8-channel, 256-bit, 100 MHz RAPIDS comparison: firmware is within 0.2% of the FSM for large transfers, but takes 18 times as long in the one-beat scheduler-limit case. The article explains how both results are true and gives the reader a decision rule.

Target 2,100–2,500 words. Use a direct, technically precise Medium style: explain terms on first use, prefer measured examples over abstractions, and keep tables small enough to read in a browser. Do not use emoji.

## Approved outline

### 1. Notes for a future project, tried now

Open with the approved Patterson-and-Hennessy origin story. Then introduce the shared RAPIDS datapath and the 3,200 MB/s per-direction board peak. Present the large-transfer near-parity and one-beat 18x contrast. State the reader promise: the difference is control work per byte and whether other activity can hide that work.

### 2. What was actually replaced

Explain that descriptor validation, policy, state-transition commands, chaining, and EXT run-base calculations moved to firmware. Engine-rate counters, address advance within a run, timeouts, sticky errors, MonBus events, and the data engines stayed in hardware. Reset-to-idle and fatal-error-to-error remain hardware interlocks.

Explicitly reject the framing that a processor replaces the whole DMA. RAPIDS and rapids-g share the datapath, descriptor format, register map, and host-visible behavior.

### 3. Why a barrel processor fits

Explain strict rotation and the distinction between aggregate issue rate and per-context rate. One hart per channel is the default at 4 and 8 channels; 16 channels default to eight harts with two slots each. Use only the detail needed to explain why adding channels changes both throughput and idle-slot overhead.

Use the 16-channel example to illustrate slot sharing and area scaling: both 8- and 16-channel RAPIDS-G have one Gatling instance per direction, two instances total. The 16-channel build does not double the instance count; it serves two channels per context and its measured area grows roughly with channel count. Never describe the current design as scaling Gatling instances linearly.

Include a short historical attribution to barrel/fine-grained multithreading through the existing Gatling documentation and references. Do not imply the technique is new.

### 4. The benefits

Cover:

- policy changes in firmware rather than control-RTL redesign;
- writable-firmware builds for live measurement and ROM builds for final deployment;
- next-descriptor pre-validation and efficient chaining;
- register and descriptor compatibility with the FSM design;
- elimination of 64 DSPs at 8 channels and 128 DSPs at 16 channels by replacing hardware index-by-stride multiplication with firmware addition.

Treat flexibility and maintainability as qualitative benefits, not measured facts.

### 5. The bill

Present the out-of-context Kintex-7 results:

| Metric | rapids-8ch | rapids-g-8ch | rapids-16ch | rapids-g-16ch |
|---|---:|---:|---:|---:|
| LUTs | 69,184 | 77,975 | 126,820 | 141,067 |
| Registers | 56,105 | 58,837 | 101,808 | 104,738 |
| BRAM tiles | 64 | 70 | 128 | 134 |
| DSPs | 64 | 0 | 128 | 0 |
| WNS at 100 MHz | +0.684 ns | +0.533 ns | +0.079 ns | +0.050 ns |

State the LUT increases as 12.7% and 11.2%. Note the extra BRAM and reduced but still positive timing margin. Do not extrapolate these FPGA numbers to ASIC area or power.

Explain the per-descriptor firmware cost: about 90 clocks at 8 channels in the chained case, and why a context paying N clocks per instruction cannot replace a one-cycle operation for free.

Complete fresh same-image 8-channel scheduler-limit runs with 4 and 8 contexts for every existing scenario. Include the resulting 4-versus-8 table in the article and record it in the RAPIDS measurements chapter. The current RTL permits only 4, 8, or 16 contexts; state that 2 contexts is unsupported rather than inventing a measurement or implying a small RTL change is part of the article.

Use EXT as the distinct worst case: firmware needs about 15–35 instructions per generated base, each instruction taking NUM_HARTS clocks for that context, versus one cycle in the hardware generator. The measured scheduler-limit per-beat EXT case is 125x slower at 8 contexts. Do not conflate this result with linear descriptors or board-level throughput.

### 6. Firmware techniques that hide latency

Discuss the actual code techniques, not generic advice to “optimize the firmware”:

- **Pre-validate and pre-arm:** `STAGE_ARM` lets firmware stage the next descriptor before its predecessor completes, avoiding an approximately 25-instruction ARM path inside each descriptor. Before this optimization the 64-beat sink-chain case cost 672 clocks per descriptor; the current combined optimized path is about 90.
- **Put the chained-head fast path in the poll:** the one-slot poll recognizes `HEAD_SUM = 13` and performs `STAGE | STAGE_ARM | STAGE_ARM_NEXT` in four instructions. The one-slot chain loop reduced the measured cost from about 288 to about 90 clocks per descriptor.
- **Re-read `HEAD_SUM` after `SUMMARY`:** this closes the arrival race between the two reads. Present it as a correctness fix that also avoids falling into the slower service path, not as permission to remove the check.
- **Shorten the idle pass:** the seven-instruction one-slot idle pass recovered a 1–2% dip on short eight-channel single-descriptor points.
- **Specialize the two-slot poll:** `SUMMARY` first gives a two-instruction idle pass; unrolling the two slots and placing the chain hook in each slot’s branch reduced the two-slot chained cost from 184 to 103 clocks and improved the cited board point from 1,122 to 2,008 MB/s. An earlier HEAD_SUM-first alternative alternated between 36- and 156-clock waits and lost to the final ordering.
- **Keep handlers run-to-completion:** one handler per poll pass, no preemption, no stack, and no handler loop. This makes latency predictable and leaves other hardware contexts free to issue.

Explain that these techniques hide control work behind the current descriptor and other channels; they cannot make an individual context issue faster than once per N cycles. Mention custom DMA instructions only as a future EXT assist, with no measured benefit claimed.

### 7. The crossover

Use the measured cycle-ratio sweep to show why chains and other active channels hide firmware work. Include a compact selection from the characterization table:

| Shape | Busy channels | Within 5% | Within 1% |
|---|---:|---:|---:|
| Single descriptor, sink | 1 of 8 | 128 KB | 512 KB |
| Single descriptor, sink | 8 of 8 | 16 KB | 64 KB |
| Single descriptor, source | 8 of 8 | 16 KB | 128 KB |
| 16-descriptor chain, sink | 1 of 8 | 4 KB | 16 KB |
| 16-descriptor chain, interleaved sink | 8 of 8 | 512 B | 4 KB |

Explain that these are bytes per descriptor, with DATA_WIDTH 256 (32 bytes per beat). Chains overlap the next descriptor with the transfer in flight; a lone single descriptor has no work behind which to hide firmware. More active channels provide independent data movement that hides control latency.

Include the scheduler-limit anchor points: 131 versus 2,371 cycles for 16 one-beat descriptors on one channel, and 84,277 versus 84,443 cycles for two 1 MB descriptors on each channel. Clearly identify scheduler-only simulation and full-board measurements as different evidence classes.

### 8. Verification is part of the cost

Explain that the firmware image is part of the hardware deliverable. Cover side-by-side FSM/firmware equivalence, reuse of existing RAPIDS tests, mutation testing of firmware and RTL, hardware fault interlocks, and board-versus-simulation cycle matching. Mention that the comparison found and fixed two bugs in the original FSM implementation; do not claim this proves firmware is inherently easier to verify.

Use one short implementation anecdote only if it supports the central argument, such as an unreachable firmware policy path found by mutation or the need to align barrel phase in performance A/B tests.

### 9. Decision rule and conclusion

Recommend firmware sequencing when:

- descriptors or chains are large enough to amortize control work;
- multiple channels or chained work can hide firmware latency;
- descriptor policy is complex or expected to evolve;
- DSP removal and firmware programmability are worth additional LUTs, BRAM, and verification effort.

Recommend retaining FSMs or adding hardware assistance when:

- tiny descriptors dominate;
- lone-channel launch latency is a hard requirement;
- EXT or another address pattern needs new bases at the engine rate;
- the firmware toolchain and verification burden cannot be supported.

Closing idea: do not ask whether a CPU is better than an FSM; ask how much control work each descriptor requires, how often it must be completed, and what useful work can hide it.

## Visual design

Create one house-style Graphviz block diagram showing the firmware/hardware boundary and shared datapath. Follow `vault/handbook/authoring/block-diagrams.md`, render it, and inspect the final PNG at full resolution. Keep policy, data, and error/interlock flows spatially distinct; label every arrow.

Create one measured crossover chart using the existing sweep data. Use logarithmic descriptor size on the x-axis and RAPIDS/rapids-g cycle ratio on the y-axis, with 1.00 marked as parity. Limit the chart to a few clearly labeled cases, such as one-channel sink, all-channel sink, and all-channel interleaved chain. Label simulation data as simulation. Do not mix board and simulation points in one unlabeled series.

Place final images in `articles/assets/` and reference them as `assets/<file>` so Medium import works. Keep editable Graphviz source beside the block diagram.

## Sources and attribution

Primary measured source:

- `projects/components/dma-ip/rapids/docs/rapids_mas/ch05_rapids_g/05_verification_and_measurements.md`

Architecture and firmware sources:

- `projects/components/dma-ip/rapids/docs/rapids_mas/ch05_rapids_g/01_overview.md`
- `projects/components/dma-ip/rapids/docs/rapids_mas/ch05_rapids_g/02_scheduler_g.md`
- `projects/components/dma-ip/rapids/docs/rapids_mas/ch05_rapids_g/03_sequencer_and_firmware.md`
- `projects/components/dma-ip/rapids/docs/rapids_has/ch02_architecture/03_rapids_g.md`
- `projects/components/dma-ip/stream/docs/stream_mas/ch07_stream_g/01_overview.md`
- `projects/components/riscv-ip/gatling-rv32i/docs/gatling_has/ch01_introduction/01_introduction.md`
- `projects/components/riscv-ip/gatling-rv32i/docs/barrel_model/barrel_model.md`
- `projects/components/riscv-ip/references/README.md`

Opening attribution: David A. Patterson and John L. Hennessy, *Computer Organization and Design: The Hardware/Software Interface*. Do not invent an edition for the owner’s notes.

Link public claims to the repository’s rendered documentation or canonical source pages. Reuse existing verified historical references; do not add unverified citations or claim originality for barrel multithreading.

## Claims and scope boundaries

- This is a Kintex-7, 100 MHz case study, not a universal DMA benchmark.
- Do not make ASIC area, ASIC timing, energy, or power claims; none are measured here.
- Do not generalize the specific N-context barrel core into an arbitrary embedded CPU.
- Do not claim all FSMs or all hardware control disappeared.
- The 16-channel example illustrates slot sharing and area scaling, not linear growth in Gatling instance count.
- The current RTL supports 4, 8, and 16 contexts; 2 contexts is unsupported.
- Distinguish scheduler-only cycle counts, full-board throughput, and out-of-context implementation results.
- Do not treat flexibility as quantified unless a measurement supports it.
- Preserve the exact threshold direction: a 1% gap means rapids-g is within 1% of FSM performance, not 1% faster.

## Deliverables and validation

- Fresh same-image 4- and 8-context, 8-channel scheduler measurements recorded in the RAPIDS measurements chapter.
- `articles/2026-10-28-dma-fsm-barrel-processor.md` with required title, date, summary, and tags front matter.
- Crossover chart and house-style block diagram under `articles/assets/`, with editable diagram source.
- Passing `python3 articles/build_articles.py --check <output-dir>` validation.
- Visual inspection of both final figures and the built article.
- Final fact check of every number and threshold against the primary measured source.

The article will be committed to git and published to GitHub Pages through the normal repository flow only when requested. Medium publication uses the existing import-by-URL process and requires a separate owner request.
