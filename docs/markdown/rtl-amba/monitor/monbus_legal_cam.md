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

# Monitor Bus Legal-Set CAM

**Module:** `monbus_legal_cam.sv`
**Location:** `rtl/amba/monitor/`
**Category:** Coverage / Observability
**Status:** Production Ready

---

## Overview

`monbus_legal_cam` is the legal-set match CAM used by
[`monbus_pkt_tally`](monbus_pkt_tally.md) in profile mode. A CSR-loaded set of
legal message identities (agent / protocol / packet-type / event-code keys) is
matched combinationally against an incoming key. A **hit** returns the entry's
**dense index** — used directly as the tally bin, so per-agent coverage is a
first-class count. A **miss** is reported so the caller can route the packet to a
single UNEXPECTED bin.

The point is density: the legal message space is ~1.2% of the full
`protocol × type × event` grid, and crossing it with `agent_id` would be ~99%
empty. Rather than a sparse direct-mapped SRAM, the legal set is enumerated into
`N_ENTRIES` dense bins, and everything else collapses to one UNEXPECTED bin —
which doubles as a spec-violation detector.

---

## Top-level Interface

| Signal | Dir | Description |
|--------|-----|-------------|
| `clk` / `rst_n` | in | Clock, active-low async reset |
| `load_clear` | in | Pulse: invalidate all entries |
| `load_we` | in | Pulse: write one entry |
| `load_addr` | in | `[IDX_WIDTH-1:0]` entry index to write |
| `load_valid` | in | Entry valid bit written with the key |
| `load_key` | in | `[KEY_WIDTH-1:0]` legal message-identity key |
| `lookup_key` | in | `[KEY_WIDTH-1:0]` incoming identity to match |
| `lookup_hit` | out | 1 when `lookup_key` matches a valid entry |
| `lookup_idx` | out | `[IDX_WIDTH-1:0]` dense index of the match (valid on hit) |

### Parameters

| Parameter | Description | Default |
|-----------|-------------|---------|
| `N_ENTRIES` | Legal-set capacity (dense bins `0..N-1`) | 64 |
| `KEY_WIDTH` | Message-identity key width | 32 |
| `IDX_WIDTH` | Derived: `clog2(N_ENTRIES)` | — |

The tally builds the key as
`{agent_id[15:0], protocol[3:0], pkt_type[3:0], event_code[7:0]}` (32 bits).

---

## Implementation

- **Valid** is a packed `N_ENTRIES`-bit vector, so its reset is a single-shot
  assign — no per-element delayed-array loop (avoids Verilator `BLKLOOPINIT`).
  Keys are gated by valid, so they need no reset.
- **Lookup** is a combinational parallel exact-match against every valid entry,
  priority-encoded to the low matching index. The host loads unique tuples, so at
  most one entry matches; the low index wins if a duplicate is ever loaded.
- A hit drives `lookup_idx` = the entry index; a miss (`lookup_hit = 0`) is the
  caller's cue to use its UNEXPECTED bin.

Area scales with `N_ENTRIES × KEY_WIDTH` comparators. When the full legal set
exceeds `N_ENTRIES`, the host loads a slice per run and reprograms for the next —
the CAM is CSR-loadable at runtime.

---

## Related Modules

| Module | Relationship |
|--------|--------------|
| [`monbus_pkt_tally`](monbus_pkt_tally.md) | The sole consumer; instantiates this in `PROFILE_MODE`. |
| [`monbus_cam`](monbus_cam.md) | The tally's separate LRU write-combining cache (unrelated role). |

Coverage design and the on-board scenario flow: `vault/handbook/fpga/monitor-board-coverage.md`.

---

## Test

Exercised through the tally's fub test (`val/amba/test_monbus_pkt_tally.py`,
profile-mode config): a legal set is loaded, matching and deliberately-illegal
packets are driven, and the dense bins + UNEXPECTED are cross-checked against a
Python golden.
