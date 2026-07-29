<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# STREAM tasks — open (not started)

### TASK-058: Signal contracts + K-maps for the significant STREAM signals (prove-by-construction)

**Priority:** High
**Status:** [ ] Open (2026-07-29)

**Goal:** Author explicit **signal contracts** and **Karnaugh maps** for all of
the significant control/handshake signals in STREAM — **especially in the read
and write engines** (`axi_read_engine.sv`, `axi_write_engine.sv`) and the
scheduler / descriptor-engine / SRAM-controller handshakes — so the design is
provably correct **by construction** rather than only by directed test.

**Why:** STREAM has already produced several *interaction* bugs that a per-signal
contract would have forbidden up front, not caught after the fact — the
WLAST/drain lost-beat deadlock, the SRAM drain double-count deadlock, and now
the extended chained-transpose corruption (TASK-059 / known_issues). Each was a
cross-block pipeline hazard: a signal asserted (or sampled) one cycle off, or a
shared config register aliased across descriptors. A written contract per signal
(producer, consumer, valid window, mutual-exclusion / one-hot invariants,
back-to-back and reset behaviour) plus a K-map for the combinational deciders
turns these into things that are wrong *on paper* before they ship.

**Scope (significant signals — at least):**
- Engine handshakes: `m_axi_*valid/ready`, `*last`, the SRAM `drain`/`valid`
  pair, per-channel `grant`/`req`, `w_active`/registered-valid gating.
- Scheduler FSM enters/exits and the write-completion timeout.
- Descriptor-engine prefetch + extended `chunk1` fetch (`w_want_ext`,
  `g_ext_fifo`) and the `stream_run_addr_gen` config-latch enables.
- Address generation stride/index/wrap deciders (K-map the mode selection:
  burst vs per-beat, wrap on/off).

**Deliverable:** a contract note per significant signal (table: producer /
consumers / valid window / invariants / reset) and K-maps for the combinational
deciders, landed under the STREAM docs tree (HAS/MAS or a dedicated
`signal_contracts/` area) and indexed. Cross-link each contract to the RTL line
and to any known_issue it would have prevented. Feeds directly into closing
TASK-059.

---

### TASK-059: Fix STREAM extended chained strided (transpose) descriptor corruption

**Priority:** High
**Status:** [ ] Open (2026-07-29) — bug FOUND + characterised, fix not started.

**Bug record:** `projects/components/dmas/stream/known_issues/active/extended_chained_transpose.md`

**Symptom:** With `USE_ROW_COL_MAJOR_ADDRESSING=1`, a strided/per-beat extended
(transpose) descriptor reached via `next_ptr` **chaining** reads the wrong
source, writes with holes, and corrupts the **preceding** descriptor's
last-touched beat. Silent — no error raised. A directly-kicked transpose and a
chained extended-**contiguous** descriptor both pass; only *chained + strided*
fails.

**Repro (already committed):**
`projects/components/dmas/stream/dv/tests/top/test_stream_top.py`
- `test_stream_top_extended` — the known-good mix (legacy→ext-contig chain +
  directly-kicked transpose), PASSES.
- `test_stream_top_extended_chained_transpose` — `xfail(strict=True)`; will
  **xpass** (failing the suite) the moment the RTL is fixed → drop the xfail then.

**Suspected root cause:** extended `chunk1` (stride config) fetch/apply on the
chained path aliasing with the descriptor engine's **prefetch** of the next
descriptor while the current transfer is in flight. Prime suspects:
`descriptor_engine.sv` (`w_want_ext` / `g_ext_fifo` + prefetch sequencing),
`scheduler.sv` (`w_is_ext_in`), `stream_run_addr_gen.sv` config latching.

**Approach:** best closed together with TASK-058 — write the signal contract for
the extended chunk1 fetch + prefetch interaction first, which should localise the
one-cycle/aliasing hazard, then fix and remove the xfail.
