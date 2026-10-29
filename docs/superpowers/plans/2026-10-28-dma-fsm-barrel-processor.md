# DMA FSM to Barrel RV32I Article Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce a validated 2,100–2,500-word Medium-ready article explaining, with measured RAPIDS evidence, when replacing DMA scheduler FSMs with an N-context barrel RV32I is beneficial.

**Architecture:** Use the approved crossover narrative and keep all factual claims anchored to RAPIDS/rapids-g measurements. Complete the missing 4-context data first, produce two reusable figures, draft the article with the firmware optimization and scaling evidence, then run a separate numerical/editorial audit and the repository’s article validator.

**Tech Stack:** Markdown, Python 3 with matplotlib 3.10.7, Graphviz `dot` 2.43, cocotb/Verilator, `bin/render_block_diagram.py`, `articles/build_articles.py`.

**Spec:** `docs/superpowers/specs/2026-10-28-dma-fsm-barrel-processor-design.md`

## Global Constraints

- Thesis: replacement is workload-dependent; do not advocate universal FSM replacement.
- Opening: “I made notes from *Computer Organization and Design* by Patterson and Hennessy. This was for a future project, but I wanted to try this out.”
- Scope: RAPIDS is the measured case study; generalize only to DMA control architecture, including STREAM where relevant.
- Barrel RV32I means one datapath serving N round-robin hardware contexts, not an N-wide superscalar CPU or host processor.
- The current RTL supports 4, 8, and 16 contexts; do not invent 2-context data.
- At 16 channels, illustrate two-slot sharing and area scaling; both 8- and 16-channel builds have one Gatling per direction, not linearly increasing instance counts.
- Discuss the measured firmware latency-hiding techniques and their limits, including STAGE_ARM, poll fast paths, HEAD_SUM re-reads, short idle passes, and two-slot chain hooks.
- Distinguish scheduler-only simulation, full-board throughput, and out-of-context FPGA implementation results.
- FPGA results are Kintex-7 at 100 MHz; make no ASIC area, ASIC timing, energy, or power claims.
- Cycle-ratio values below 1.00 mean rapids-g is slower; 1.00 is parity.
- Crossover thresholds are bytes per descriptor at DATA_WIDTH 256 (32 bytes per beat), not total bytes per run.
- Keep engine-rate hardware and fatal reset/error interlocks in the architecture; never claim all hardware control disappeared.
- Article length is 2,100–2,500 words, with no emoji and required title/date/summary/tags front matter.
- Reference article images only as `assets/<file>` and inspect both final images at full resolution.
- Stage only files owned by this article; leave unrelated active work untouched. Run normal commit hooks before considering any bypass.

## Review Focus

- **Ratio inversion:** a reader could interpret 0.50 as “twice as fast”; Task 5 checks every ratio and performance claim against the source direction.
- **Evidence-class mixing:** board MB/s, scheduler cycles, and implementation LUTs could appear interchangeable; Tasks 4 and 5 require local labels and a final evidence-class audit.
- **Threshold-unit errors:** beats, bytes per descriptor, and total chain bytes could be confused; Task 5 checks every threshold against DATA_WIDTH 256 and chain shape.
- **Hart/scaling confusion:** 4-versus-8 context data and 16-channel slot sharing could become unsupported 2-context or linear-instance claims; Tasks 1 and 5 pin the exact configurations and wording.
- **Optimization attribution:** combined firmware improvements could be credited to one change incorrectly; Task 5 checks each latency claim against the firmware chronology.
- **Overgeneralization:** FPGA LUT/DSP results could become unsupported ASIC or power claims; Task 5 scans the final article for those claims and removes them.
- **Incomplete replacement story:** “FSMs replaced” could hide the remaining scheduler core and safety interlocks; Task 3 traces them in the figure and Task 5 checks the prose.
- **Medium image portability:** local image paths could work in Markdown but fail in RSS; Task 5 validates absolute rewritten image URLs in the built article and feed.

---

### Task 1: Complete 4- and 8-Context Scheduler Measurements

**Files:**
- Create: `articles/assets/dma_fsm_barrel_hart_scaling.json`
- Modify: `projects/components/dma-ip/rapids/docs/rapids_mas/ch05_rapids_g/05_verification_and_measurements.md:170-204`
- Test: `projects/components/dma-ip/rapids/dv/tests/fub_g/test_rapids_g_equiv.py`

**Interfaces:**
- Consumes: The existing `cocotb_test_perf` scenarios at 8 channels, DATA_WIDTH 256, with NUM_HARTS 4 and 8.
- Produces: A same-image 4/8-context comparison used by Task 4 and audited by Task 5.

- [ ] **Step 1: Run both complete scheduler-limit configurations**

Run:

```bash
PATH=/mnt/data/github/RTLDesignSherpa/venv/bin:$PATH SIM=verilator /mnt/data/github/RTLDesignSherpa/venv/bin/python -m pytest -q \
  'projects/components/dma-ip/rapids/dv/tests/fub_g/test_rapids_g_equiv.py::test_rapids_g_equiv[func-8-256-4-perf]' \
  'projects/components/dma-ip/rapids/dv/tests/fub_g/test_rapids_g_equiv.py::test_rapids_g_equiv[func-8-256-8-perf]'
```

Expected: 2 passed. Both runs must include all eight scenarios and end with equivalent FSM/firmware command streams. Record the printed perf JSON paths; do not reuse the older partial 4-context figures as a substitute for this run.

- [ ] **Step 2: Preserve the normalized measurements**

Create `articles/assets/dma_fsm_barrel_hart_scaling.json` with the run metadata (`channels: 8`, `data_width: 256`, `simulator: verilator`, `firmware: committed executive image`) and both configurations. For every scenario record the descriptor count, FSM cycles, and 4-/8-context cycles exactly from the two run JSON files. Include the existing FSM values rather than rerunning a different benchmark.

- [ ] **Step 3: Update the RAPIDS measurement chapter**

Extend Table 5.5.5 with a 4-context column from the new run and keep the committed-executive 8-context column. Update the surrounding text with the measured one-channel/all-channel behavior and the large-transfer comparison. State explicitly that the current RTL permits 4, 8, or 16 contexts, so 2 contexts is unsupported; do not describe 4 and 8 as separate Gatling instances.

- [ ] **Step 4: Commit the measurements**

```bash
git add articles/assets/dma_fsm_barrel_hart_scaling.json projects/components/dma-ip/rapids/docs/rapids_mas/ch05_rapids_g/05_verification_and_measurements.md
git commit -m "docs(rapids): compare 4 and 8 contexts on 8 channels"
```

### Task 2: Measured Crossover Chart

**Files:**
- Create: `articles/assets/dma_fsm_barrel_crossover.png`
- Reference: `projects/components/dma-ip/rapids/docs/rapids_mas/ch05_rapids_g/05_verification_and_measurements.md:280-365`

**Interfaces:**
- Consumes: Tables 5.5.10 and 5.5.12 in the measured source.
- Produces: `assets/dma_fsm_barrel_crossover.png`, used by the article in Task 4.

- [ ] **Step 1: Extract and check the three simulation series**

Use DATA_WIDTH 256 and x values in beats. Preserve these exact `(beats, RAPIDS/rapids-g cycles)` series from the source:

- All-channel single-descriptor sink: `(1,0.57), (2,0.57), (4,0.59), (8,0.63), (16,0.67), (32,0.74), (64,0.81), (128,0.88), (256,0.93), (512,0.96), (1024,0.98), (2048,0.99), (4096,0.99)`.
- One-channel single-descriptor sink: `(1,0.27), (2,0.27), (4,0.29), (8,0.31), (16,0.34), (32,0.38), (64,0.45), (128,0.54), (256,0.67), (512,0.78), (1024,0.87), (2048,0.93), (4096,0.96), (8192,0.98), (16384,0.99), (32768,1.00)`.
- All-channel 16-descriptor interleaved-sink chain: `(1,0.52), (2,0.49), (4,0.60), (8,0.90), (16,0.95), (32,0.97), (64,0.98), (128,0.99), (256,0.99), (512,1.00), (1024,1.00)`.

Check that the chart data imply the article’s thresholds: all-channel sink is within 5% from 512 beats (16 KB) and 1% from 2,048 beats (64 KB); one-channel sink is within 5% from 4,096 beats (128 KB) and 1% from 16,384 beats (512 KB); the chain is within 5% from 16 beats (512 B) and 1% from 128 beats (4 KB).

- [ ] **Step 2: Render the chart with matplotlib**

Use a log2 x-axis labeled `Descriptor size (beats; 32 bytes per beat)` and a linear y-axis labeled `FSM / barrel-RV32I cycles (1.00 = parity)`. Limit y to 0.20–1.05 so the one-channel 0.27 point remains visible. Draw a horizontal parity line at 1.00 and a legend naming all three series. Title it `Firmware control catches up when transfers hide its work` and add `Scheduler comparison, simulation` inside the figure. Render a white-background PNG at least 1,600 pixels wide.

- [ ] **Step 3: Inspect the rendered chart**

Read `articles/assets/dma_fsm_barrel_crossover.png` at full resolution. Confirm that no series, label, tick, or legend is clipped; the parity line is visible; each line is distinguishable; and the one-channel and all-channel trends cannot be mistaken for board-throughput data.

- [ ] **Step 4: Commit the chart**

```bash
git add articles/assets/dma_fsm_barrel_crossover.png
git commit -m "docs(articles): add DMA firmware crossover chart"
```

### Task 3: Firmware/Hardware Boundary Diagram

**Files:**
- Create: `articles/assets/dma_fsm_barrel_control.dot`
- Create: `articles/assets/dma_fsm_barrel_control.png`
- Reference: `projects/components/dma-ip/rapids/docs/rapids_mas/ch05_rapids_g/01_overview.md:31-70`
- Reference: `vault/handbook/authoring/block-diagrams.md`

**Interfaces:**
- Consumes: The approved hardware/firmware split and the house diagram rules.
- Produces: `assets/dma_fsm_barrel_control.png`, embedded by Task 4.

- [ ] **Step 1: Draw the Graphviz source**

Create a top-down diagram titled `Replace descriptor policy, not the engine-rate datapath`. Show host descriptors entering the barrel RV32I policy path; firmware validation/chaining/run-base calculations; scheduler commands entering the shared `scheduler_core`; and the shared engines crossing one labeled engine-rate interface boundary. Keep write data top-down on a left route and read data returning upward on a right route. Show reset-to-idle and fatal-error-to-error as short, dashed, labeled interlocks that bypass firmware. Label every arrow with its payload and mark interface timing classes.

Use the current element key: registered blue double-border blocks, storage cylinders where applicable, green rounded interfaces, white combinational logic, dashed sideband edges, and green return-data edges. Do not draw a CPU replacing the entire DMA or route policy commands on a data arrow.

- [ ] **Step 2: Render through the house renderer**

Run:

```bash
/mnt/data/github/RTLDesignSherpa/venv/bin/python bin/render_block_diagram.py articles/assets/dma_fsm_barrel_control.dot
```

Expected: exit 0, a bold top title reported, and `articles/assets/dma_fsm_barrel_control.png` generated with only the classes and edge styles actually used in the key.

- [ ] **Step 3: Trace and inspect all flows at full resolution**

Read the final PNG. Trace descriptor policy top-down, write data on its own route, read data upward on its own route, and both fatal interlocks around firmware. Confirm one boundary bar, no unlabeled arrows, no shared command/data arrow, no text on lines, no overlapping labels, and a readable generated key. Re-rank and rerender until all checks pass; do not shrink text to hide a layout problem.

- [ ] **Step 4: Commit the diagram and source**

```bash
git add articles/assets/dma_fsm_barrel_control.dot articles/assets/dma_fsm_barrel_control.png
git commit -m "docs(articles): add DMA firmware boundary diagram"
```

### Task 4: Complete Article Draft

**Files:**
- Create: `articles/2026-10-28-dma-fsm-barrel-processor.md`
- Consume: `articles/assets/dma_fsm_barrel_crossover.png`
- Consume: `articles/assets/dma_fsm_barrel_control.png`
- Consume: `articles/assets/dma_fsm_barrel_hart_scaling.json`
- Reference: `docs/superpowers/specs/2026-10-28-dma-fsm-barrel-processor-design.md`

**Interfaces:**
- Consumes: Both figures, the 4/8-context measurements, and every measured value in the approved spec.
- Produces: The complete Medium-ready article for independent editorial review in Task 5.

- [ ] **Step 1: Write front matter and the opening**

Use:

```yaml
---
title: When Should a DMA’s FSM Become a Processor?
date: 2026-10-28
summary: Replacing DMA scheduler FSMs with a barrel RV32I can eliminate DSPs and make control programmable, but the benefit depends on descriptor size, chaining, channel activity, and address-generation rate.
tags: dma, riscv, fpga, computer-architecture, rtl
---
```

Start with: “I made notes from *Computer Organization and Design* by Patterson and Hennessy. This was for a future project, but I wanted to try this out.” Then present the same-design contrast: 131 versus 2,371 cycles for 16 one-beat descriptors on one channel, and 84,277 versus 84,443 cycles for two 1 MB descriptors on each channel. Label both as scheduler-only simulation. Explain that the article will resolve the contrast rather than declare a universal winner.

- [ ] **Step 2: Write the architecture and scaling sections**

Implement approved outline sections 2 and 3. Embed `assets/dma_fsm_barrel_control.png` after explaining the shared datapath. Define N-context round-robin issue, per-context N-cycle instruction cost, one hart per channel at 4/8 channels, and eight harts with two slots each at 16 channels. State that both 8- and 16-channel builds have one Gatling per direction; use the 16-channel example for slot sharing and area scaling, not linear instance growth. Include a short attribution to the existing Gatling historical references and link to the public architecture documentation.

- [ ] **Step 3: Write benefits and costs**

Implement approved outline sections 4 and 5. Include the exact 8/16-channel LUT/register/BRAM/DSP/WNS table from the spec, the 12.7% and 11.2% LUT increases, approximately 90 clocks per chained descriptor at 8 channels, and the EXT 15–35-instruction and 125x scheduler-limit warning. Add the new same-image 4/8-context scheduler table from Task 1 and state that 2 contexts is unsupported. Keep qualitative flexibility claims separate from measured benefits.

- [ ] **Step 4: Explain the firmware latency-hiding techniques**

Implement approved outline section 6 with the measured chronology: pre-validation and STAGE_ARM; the four-instruction one-slot chain hook; the HEAD_SUM re-read that closes the arrival race; the seven-instruction idle pass; two-slot SUMMARY-first polling, unrolling, and per-slot chain hooks; and run-to-completion handlers. Include the 288→90 and 184→103-clock improvements, the 672-clock pre-STAGE_ARM anchor, the 1,122→2,008 MB/s board improvement, and the failed 36/156-clock alternative. Explain what each technique hides and what it cannot overcome.

- [ ] **Step 5: Write crossover, verification, and decision sections**

Embed `assets/dma_fsm_barrel_crossover.png`, include the five-row threshold table from the spec, and explain why chains and multiple active channels hide firmware work. Implement the verification section with equivalence, reused tests, mutation, hardware interlocks, and board/simulation cycle matching. Finish with the two-sided decision checklist and the control-work-per-byte closing idea.

- [ ] **Step 6: Check length, links, and initial build**

Run:

```bash
/mnt/data/github/RTLDesignSherpa/venv/bin/python -c "from pathlib import Path; import re; p=Path('articles/2026-10-28-dma-fsm-barrel-processor.md'); print(len(re.findall(r'\b[\w’-]+\b', p.read_text())))"
/mnt/data/github/RTLDesignSherpa/venv/bin/python articles/build_articles.py --check sim_build/articles-task4
```

Expected: 2,100–2,500 words; validator exit 0 with no missing front matter or images. Revise length or structure now rather than adding filler during final review.

- [ ] **Step 7: Commit the complete draft**

```bash
git add articles/2026-10-28-dma-fsm-barrel-processor.md
git commit -m "docs(articles): analyze DMA FSM replacement with barrel RV32I"
```

### Task 5: Numerical, Editorial, and Publication Validation

**Files:**
- Modify: `articles/2026-10-28-dma-fsm-barrel-processor.md`
- Modify if inspection requires it: `articles/assets/dma_fsm_barrel_control.dot`
- Regenerate if its source changes: `articles/assets/dma_fsm_barrel_control.png`
- Regenerate if its data or presentation changes: `articles/assets/dma_fsm_barrel_crossover.png`
- Audit: `articles/assets/dma_fsm_barrel_hart_scaling.json`
- Audit: `projects/components/dma-ip/rapids/docs/rapids_mas/ch05_rapids_g/05_verification_and_measurements.md`
- Commit with the final article: `docs/superpowers/specs/2026-10-28-dma-fsm-barrel-processor-design.md`
- Commit with the final article: `docs/superpowers/plans/2026-10-28-dma-fsm-barrel-processor.md`

**Interfaces:**
- Consumes: The complete draft, final figures, spec, fresh 4/8 data, and primary measurement source.
- Produces: The validated article and planning records ready for the requested git/publishing flow.

- [ ] **Step 1: Audit every measured claim against the primary sources**

Check each number against `05_verification_and_measurements.md` and the new scaling JSON: 131/2,371; 84,277/84,443; 18x; 0.2%; every LUT/register/BRAM/DSP/WNS cell; 12.7%/11.2%; every 4/8-context cell; approximately 90 clocks; 15–35 instructions; 125x; and all five threshold rows. Confirm all ratio wording says values below 1.00 are slower and thresholds mean “within” rather than “faster by.”

- [ ] **Step 2: Audit optimization chronology and scaling claims**

Check the 672-clock pre-STAGE_ARM anchor, 288→90 one-slot improvement, 184→103 two-slot improvement, 1,122→2,008 MB/s board result, seven-instruction idle pass, HEAD_SUM re-read rationale, and rejected 36/156-clock alternative against the firmware and measurement chapters. Confirm 2 contexts is called unsupported and the 16-channel example says two slots per context and one Gatling per direction, not linear instance scaling.

- [ ] **Step 3: Audit evidence classes, units, and scope**

Verify every performance table or figure is locally identified as scheduler simulation, full-board MB/s, or out-of-context implementation. Check that crossover units are bytes per descriptor at 32 bytes per beat and chain rows say 16 descriptors. Remove any ASIC area/timing, power, energy, universal-DMA, arbitrary-CPU, or all-control-eliminated claim. Confirm flexibility remains qualitative.

- [ ] **Step 4: Review narrative and attribution**

Read the article aloud for flow and repetition. Confirm it starts with the approved Patterson-and-Hennessy note, answers the opening question, explains barrel scheduling accessibly, attributes historical barrel threading through the existing Gatling references, and concludes with both firmware and FSM/hardware-assist cases. Keep the final text within 2,100–2,500 words.

- [ ] **Step 5: Run the final article build and inspect publication output**

Run:

```bash
/mnt/data/github/RTLDesignSherpa/venv/bin/python articles/build_articles.py --check sim_build/articles-final
```

Expected: exit 0. Inspect `sim_build/articles-final/articles/dma-fsm-barrel-processor/index.html` and `sim_build/articles-final/articles/feed.xml`. Confirm the title, summary, date, both figures, absolute Pages image URLs, readable tables, working source links, and canonical-import-compatible asset paths. Reinspect any regenerated figure at full resolution.

- [ ] **Step 6: Run whitespace and scoped-link checks**

Run:

```bash
git diff --check -- articles projects/components/dma-ip/rapids/docs/rapids_mas/ch05_rapids_g/05_verification_and_measurements.md docs/superpowers/specs/2026-10-28-dma-fsm-barrel-processor-design.md docs/superpowers/plans/2026-10-28-dma-fsm-barrel-processor.md
/mnt/data/github/RTLDesignSherpa/venv/bin/python bin/check_broken_links.py --ratchet
```

Expected: no whitespace errors and no new broken links. If the global link gate is blocked by unrelated active work, identify the exact external failure and run the check again on a clean integration tree before claiming the article introduces no broken links; do not rebaseline or edit unrelated documents.

- [ ] **Step 7: Commit final review changes and planning records**

```bash
git add articles/2026-10-28-dma-fsm-barrel-processor.md articles/assets/dma_fsm_barrel_control.dot articles/assets/dma_fsm_barrel_control.png articles/assets/dma_fsm_barrel_crossover.png articles/assets/dma_fsm_barrel_hart_scaling.json projects/components/dma-ip/rapids/docs/rapids_mas/ch05_rapids_g/05_verification_and_measurements.md docs/superpowers/specs/2026-10-28-dma-fsm-barrel-processor-design.md docs/superpowers/plans/2026-10-28-dma-fsm-barrel-processor.md
git commit -m "docs(articles): validate DMA barrel-processor analysis"
```

Do not push, publish to Pages, or import to Medium without the owner’s explicit request.
