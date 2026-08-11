---
title: Design notes
summary: RTL rules with the failures that taught them.
---

# Design

- [[reset-and-clocking]] - reset macros, aresetn, clock conventions
- [[cdc]] - crossing rules, gray pointers, handshakes
- [[valid-ready-contracts]] - stability rules; who may stall whom
- [[streaming-no-fsm]] - the pipeline pattern for datapaths
- [[sram-and-memories]] - no-reset SRAMs, ram_style, array syntax
- [[sizing-invariants]] - shared-resource math; one source of truth
- [[priority-logic-depth]] - serialized scans vs parallel selects
- [[naming-and-style]] - module/signal conventions, headers
- [[signal-prefixes]] - r_ = flopped, w_ = combinational; what it promises and where it lies
- [[filelists]] - every module MUST have a .f and be registered; the two silent failures
- [[generated-rtl-discipline]] - fix the generator, not the generated .sv; regen-and-diff is the audit
- [[minimal-fsm]] - when an FSM is right, keep it minimal
- [[signal-contracts-and-kmaps]] - contracts workbooks; computed K-maps
