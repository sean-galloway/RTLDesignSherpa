# gem5 Ruby protocol specs (reference extract)

Executable, state-table-style cache-coherence protocol specifications in
gem5's SLICC language, extracted verbatim from gem5 `master` at commit
`f5c5a6e390f55dd5984977815bf9d0bd05da6945` (2026-09-07) via sparse clone.

Two protocols, as requested for the cache-ip research library:

- **MESI_Two_Level** — classic snoopy MESI with a shared L2. The L1 cache
  controller (`MESI_Two_Level-L1cache.sm`) is the closest executable model to
  amber: every transient state (IS, IM, SM, S^I, M^I, ...) between a stable
  MESI state and a pending response is enumerated as an explicit state with
  its own transition table. `MESI_Two_Level-msg.sm` is the message-type
  contract (the shape a D4 snoop transport must express);
  `MESI_Two_Level-dir.sm` + `-L2cache.sm` show the point where a passive
  memory-side agent has to make coherence-visible decisions.
- **MOESI_CMP_directory** — the directory-based contrast set: what changes
  when a home/directory agent (not a broadcast medium) owns coherence
  serialization. Useful for ruling D4 options in or out with a working
  executable spec instead of prose.

**Why these exist here:** the Primer's MESI diagrams show only stable
states; most coherence bugs live in the transient states. These files are
the enumerated transient-state tables — the raw material for deriving
amber's `amber_pkg` state encoding and for building the Python reference
model the DV scoreboard replays against (amber D9, jet J7 cross-checks).

**License:** each `.sm`/`.slicc` file carries its complete copyright and
BSD-3-clause license header inline (ARM Limited; Mark D. Hill and David A.
Wood) — redistribution terms are inside the files themselves. `LICENSE` is
gem5's root file, an unrendered BSD-3 template, included as-shipped.

**Upstream:** https://github.com/gem5/gem5 (`src/mem/ruby/protocol/`).
This directory is a read-only extract; track upstream for changes.
