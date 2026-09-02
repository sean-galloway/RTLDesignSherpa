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

## Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| `N_ENTRIES` | int | 64 | Legal-set capacity (dense bins `0..N-1`) |
| `KEY_WIDTH` | int | 32 | Message-identity key width |
| `IDX_WIDTH` | int | derived | `clog2(N_ENTRIES)` |

The tally builds the key as
`{agent_id[15:0], protocol[3:0], pkt_type[3:0], event_code[7:0]}` (32 bits).

---

## Ports

| Port | Direction | Width | Description |
|---|---|---|---|
| `clk` | input | 1 | Clock |
| `rst_n` | input | 1 | Active-low asynchronous reset |
| `load_clear` | input | 1 | Pulse: invalidate all entries |
| `load_we` | input | 1 | Pulse: write one entry |
| `load_addr` | input | IDX_WIDTH | Entry index to write |
| `load_valid` | input | 1 | Entry valid bit written with the key |
| `load_key` | input | KEY_WIDTH | Legal message-identity key |
| `lookup_key` | input | KEY_WIDTH | Incoming identity to match |
| `lookup_hit` | output | 1 | 1 when `lookup_key` matches a valid entry |
| `lookup_idx` | output | IDX_WIDTH | Dense index of the match (valid on hit) |

---

## Functional Description

- **Valid** is a packed `N_ENTRIES`-bit vector, so its reset is a single-shot
  assign — no per-element delayed-array loop (avoids Verilator `BLKLOOPINIT`).
  Keys are gated by valid, so they need no reset.
- **Lookup** is a combinational parallel exact-match against every valid entry,
  priority-encoded to the low matching index. The host loads unique tuples, so at
  most one entry matches; the low index wins if a duplicate is ever loaded.
- A hit drives `lookup_idx` = the entry index; a miss (`lookup_hit = 0`) is the
  caller's cue to use its UNEXPECTED bin.

---

## Timing Characteristics

This module is **sequential**: it contains clocked logic (via `always_ff` or
the repository's `ALWAYS_FF_RST` macro) and therefore holds state. Outputs
driven from those blocks are registered and appear one clock after the inputs
that produced them.

Per-path cycle counts are not enumerated here; read the block that drives the
signal you care about. No synthesis frequency or area figures are quoted --
none have been measured against a target device.

Timing closure is therefore a question of the surrounding logic's slack, not of
this module's cycle count. No synthesis figures are quoted; none have been
measured.

---

## Usage Examples

Every parameter and port below is taken from the module declaration.

```systemverilog
monbus_legal_cam #(
    .N_ENTRIES             (64),
    .KEY_WIDTH             (32),
    .IDX_WIDTH             ((N_ENTRIES > 1))
) u_monbus_legal_cam (
    .clk                   (clk),
    .rst_n                 (rst_n),
    .load_clear            (load_clear),
    .load_we               (load_we),
    .load_addr             (load_addr),
    .load_valid            (load_valid),
    .load_key              (load_key),
    .lookup_key            (lookup_key),
    .lookup_hit            (lookup_hit),
    .lookup_idx            (lookup_idx)
);
```

---

## Design Notes

Area scales with `N_ENTRIES × KEY_WIDTH` comparators. When the full legal set
exceeds `N_ENTRIES`, the host loads a slice per run and reprograms for the next —
the CAM is CSR-loadable at runtime.

---

## Related Modules

| Module | Relationship |
|---|---|
| [`monbus_pkt_tally`](monbus_pkt_tally.md) | The sole consumer; instantiates this in `PROFILE_MODE`. |
| [`monbus_cam`](monbus_cam.md) | The tally's separate LRU write-combining cache (unrelated role). |

Coverage design and the on-board scenario flow: `vault/handbook/fpga/Genesys2/stream-mon/monitor-board-coverage.md`.

---

## Testing

Exercised through the tally's fub test (`val/amba/test_monbus_pkt_tally.py`,
profile-mode config): a legal set is loaded, matching and deliberately-illegal
packets are driven, and the dense bins + UNEXPECTED are cross-checked against a
Python golden.

---

## Navigation

- [Back to Shared Infrastructure Index](../_book_monitor_index.md)
- [Back to rtl-amba Index](../index.md)
