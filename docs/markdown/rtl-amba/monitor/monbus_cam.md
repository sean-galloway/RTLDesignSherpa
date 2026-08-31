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

# Monitor Bus LRU CAM

**Module:** `monbus_cam.sv`
**Location:** `rtl/amba/monitor/`
**Category:** Bulk-Trace Compression Infrastructure
**Status:** Reference design — superseded in-production by [`monbus_cam_pipe`](monbus_cam_pipe.md)

---

## Overview

> **Deprecation note.** `monbus_cam.sv` is the single-cycle reference
> design. The in-production CAM inside `monbus_compressor` is now
> `monbus_cam_pipe.sv`, a 2-cycle pipelined variant that splits the
> 49-bit compare → priority-encode → move-to-front chain into two
> stages so the path closes at 100 MHz on Nexys A7 (`f909f01f` /
> `0d1c0a1a`). The two share LRU semantics and per-entry storage, but they
> are **not** interchangeable in interface: `monbus_cam_pipe` adds a cycle of
> latency and has **no `ACTION_NONE`** — every `access_en` cycle is a commit,
> with TOUCH/INSTALL derived from hit/miss, because the commit lands before
> the tier decision exists. It also has **no skid and no credit logic**; the
> credit-gated result skid (`u_res_skid` / `r_credit`) lives in
> `monbus_compressor`, and it is what sets sustained tier-1 throughput. At
> `SKID_DEPTH = 3` (the current value) that is 1 record/cycle measured; at the
> earlier depth of 2 it measured 0.67. See
> [`monbus_compressor`](monbus_compressor.md). Both files are kept in tree: this single-cycle module
> serves as the executable spec for the LRU semantics and the
> compressor's CAM behavior, and is what the algorithmic tests
> (`test_monbus_cam.py`) target. New code should instantiate
> [`monbus_cam_pipe`](monbus_cam_pipe.md).

`monbus_cam` is a **true-LRU caching content-addressable memory** that defines
the template-index semantics the [`monbus_compressor`](monbus_compressor.md)
depends on (the compressor instantiates the pipelined
[`monbus_cam_pipe`](monbus_cam_pipe.md); this module is the executable spec).
It assigns 5-bit template indices
(`tmpl_idx`) to the 49-bit template keys it extracts from monitor packets.
"True LRU" means the eviction victim is the least recently *accessed* entry
(matched, touched, or installed) — not the least recently *inserted*. This
matters because the bulk-trace compression format relies on both encoder
and decoder maintaining identical CAM state from the slot stream alone; if
the two sides diverge on eviction order, the decoder produces garbage.

The module is a **bit-exact mirror** of the Python `Cam` class in
`bin/TBClasses/monbus/monbus_compressor.py`. Any divergence between the
two implementations is a regression.

At a glance:

- 32-entry capacity (locked by the bulk-trace format spec)
- 49-bit key, 64-bit payload (both parameterizable)
- **Per-entry timestamp storage** (`TS_WIDTH=24`) for per-template
  `delta_ts` — see the dedicated section below
- Single combinational access port: lookup + commit in one cycle
- True LRU eviction via **position-indexed storage** — the slot index IS the
  recency rank (slot 0 = MRU, slot `DEPTH-1` = LRU)
- 3 caller-driven actions: `NONE`, `TOUCH`, `INSTALL`
- Eviction pulse output for stats / instrumentation
- Simulation-only protocol assertions on the caller

---

## Parameters

The default values (`KEY_WIDTH=49`, `DATA_WIDTH=64`, `DEPTH=32`) are what the
compressor instantiates and what the locked format spec mandates. The
parameters exist so the module can be reused in other contexts (e.g. a smaller
on-chip event cache) but `monbus_compressor` itself doesn't override them.

| Parameter | Type | Default | Description |
|---|---|---|---|
| `KEY_WIDTH` | int | 49 | Template key width (locked by the format spec) |
| `DATA_WIDTH` | int | 64 | Payload width |
| `TS_WIDTH` | int | 24 | Per-entry `last_ts` width (per-template `delta_ts`) |
| `DEPTH` | int | 32 | Entry capacity (locked at 32 by the format spec) |
| `IDX_WIDTH` | int | `(DEPTH > 1) ? $clog2(DEPTH) : 1` | Derived index width |
| `CNT_WIDTH` | int | `$clog2(DEPTH + 1)` | Derived count width |

If you change `DEPTH`, the corresponding change in the Python golden's
`DEFAULT_CAM_SIZE` constant must happen in lockstep — otherwise the encoded
slot stream will diverge.

---

## Ports

```systemverilog
module monbus_cam #(
    parameter int KEY_WIDTH  = 49,
    parameter int DATA_WIDTH = 64,
    parameter int TS_WIDTH   = 24,   // per-entry last_ts width (per-template delta_ts)
    parameter int DEPTH      = 32,
    parameter int IDX_WIDTH  = (DEPTH > 1) ? $clog2(DEPTH) : 1,
    parameter int CNT_WIDTH  = $clog2(DEPTH + 1)
) (
    input  logic                  clk,
    input  logic                  rst_n,

    // Access port (one combinational lookup + one commit per cycle)
    input  logic [KEY_WIDTH-1:0]  access_key,
    output logic                  access_hit,
    output logic [IDX_WIDTH-1:0]  access_idx,       // position rank (only valid on hit)
    output logic [DATA_WIDTH-1:0] access_old_data,  // pre-commit payload at access_idx
    output logic [TS_WIDTH-1:0]   access_old_ts,    // pre-commit timestamp at access_idx

    input  logic [1:0]            access_action,
    input  logic [DATA_WIDTH-1:0] access_new_data,
    input  logic [TS_WIDTH-1:0]   access_new_ts,    // timestamp to write on TOUCH / INSTALL

    // Status
    output logic                  cam_full,
    output logic [CNT_WIDTH-1:0]  cam_count,
    output logic                  evicted,          // pulses on full-CAM INSTALL

    // Counting-consumer ports (additive; the compressor ties/ignores these)
    output logic [KEY_WIDTH-1:0]  evict_key,        // victim key,  valid when evicted
    output logic [DATA_WIDTH-1:0] evict_data,       // victim data, valid when evicted
    input  logic [IDX_WIDTH-1:0]  dump_idx,         // position to observe
    output logic                  dump_valid,       // entry at dump_idx is occupied
    output logic [KEY_WIDTH-1:0]  dump_key,
    output logic [DATA_WIDTH-1:0] dump_data,
    input  logic                  soft_clear        // synchronous invalidate-all
);
```

### Counting-Consumer Ports

The compressor uses only the access port + `evicted`. A second class of
consumer — a **counting** cache such as [`monbus_pkt_tally`](monbus_pkt_tally.md),
where the payload is a partial count that must survive eviction — needs to see
the victim and to walk live entries. These ports were added **additively** for
that use; they do not change the LRU behaviour the compressor golden depends on,
and any instantiation that does not need them may tie `dump_idx`/`soft_clear`
low and leave the new outputs open. (The compressor no longer instantiates
*this* module -- it uses `monbus_cam_pipe`, which has neither port.)

| Port | Direction | Width | Description |
|---|---|---|---|
| `evict_key` / `evict_data` | output | KEY_WIDTH / DATA_WIDTH | The LRU victim (position `DEPTH-1`), combinational, valid the cycle `evicted` is high. A counting consumer folds `evict_data` back into its backing store before the entry is lost. |
| `dump_idx` | input | IDX_WIDTH | Position to observe (for a freeze/flush walk over all entries). |
| `dump_valid` / `dump_key` / `dump_data` | output | 1 / KEY_WIDTH / DATA_WIDTH | Occupancy + contents of `dump_idx`, purely observational (no state change). |
| `soft_clear` | input | 1 | Synchronous invalidate-all (`cam_count → 0`) without an async reset pulse; re-arms the cache between capture windows. Takes priority over any concurrent `access_action`. |

---

## Functional Description

### Architecture

![monbus_cam block diagram](../../assets/rtl-amba/monbus_cam.svg)

Source: [`monbus_cam.mmd`](../../assets/rtl-amba/monbus_cam.mmd)

```mermaid
%%{init: {'theme': 'neutral', 'themeVariables': { 'fontSize': '14px'}}}%%
flowchart TB
    subgraph Access["Access Port (1 lookup + 1 commit per cycle)"]
        KEY["access_key[KEY_WIDTH-1:0]"]
        ACTION["access_action[1:0]<br/>NONE / TOUCH / INSTALL"]
        NEWDATA["access_new_data[DATA_WIDTH-1:0]"]
    end

    subgraph monbus_cam["monbus_cam (position-indexed LRU)"]
        subgraph Storage["Storage (slot 0 = MRU)"]
            S0["r_entry[0] = MRU"]
            S1["r_entry[1]"]
            SD["r_entry[2..DEPTH-2]"]
            SE["r_entry[DEPTH-1] = LRU"]
        end
        MATCH["Parallel match:<br/>w_match_oh[i] =<br/>r_valid[i] && (r_key[i] == access_key)"]
        SHIFT["Per-slot shift logic:<br/>TOUCH: shift down 0..idx<br/>INSTALL: shift down 0..count or 0..DEPTH-1<br/>(LRU evicted if full)"]
    end

    subgraph Outputs["Outputs"]
        HIT["access_hit"]
        IDX["access_idx<br/>(position rank == tmpl_idx)"]
        OLD["access_old_data"]
        FULL["cam_full"]
        COUNT["cam_count"]
        EVICTED["evicted (pulses<br/>on full-CAM INSTALL)"]
    end

    KEY --> MATCH
    Storage --> MATCH
    MATCH --> HIT
    MATCH --> IDX
    MATCH --> OLD
    ACTION --> SHIFT
    NEWDATA --> SHIFT
    MATCH --> SHIFT
    SHIFT --> Storage
    Storage --> COUNT
    COUNT --> FULL
    ACTION --> EVICTED
    FULL --> EVICTED
```

### Storage Model: Position-Indexed LRU

The fundamental design choice is that **the slot index IS the position rank**:

```
r_entry[0]              = most-recently-used (MRU)
r_entry[1] .. r_entry[count-1]  = ordered, newer first
r_entry[count..DEPTH-1] = invalid (empty slots)
```

This means:

- The `access_idx` output on a hit is the entry's current position rank,
  which is exactly what `tmpl_idx` needs to be in the compressed slot stream.
- On `TOUCH` or `INSTALL`, the matched/new entry moves to slot 0 and older
  entries shift down by one position. This is one structural operation that
  updates *both* the storage AND the rank simultaneously.
- The LRU victim is always whoever sits at slot `DEPTH-1`. No tag pointers,
  no doubly-linked list, no per-entry counter — pure structural.

The trade-off: every `TOUCH`/`INSTALL` performs a shift of up to `DEPTH-1`
entries on a single clock edge. For `DEPTH=32` this is well within timing
budget (parallel per-slot updates in a generate loop) but it's the reason
the format spec locks the size at 32 and not 64 or 128.

### Actions

The caller drives exactly one action per cycle on the `access_action` port:

| Action | Encoding | Caller protocol | State change on commit |
|---|---|---|---|
| `ACTION_NONE` | `2'b00` | Pure lookup — anytime | None. Just samples hit/idx/old_data. |
| `ACTION_TOUCH` | `2'b01` | Must coincide with a hit | Matched entry moves to slot 0, payload updated with `access_new_data`. |
| `ACTION_INSTALL` | `2'b10` | Must coincide with a miss | New entry installed at slot 0. If `cam_full`, the entry at slot `DEPTH-1` is evicted and `evicted` pulses high that cycle. |
| `2'b11` | reserved | — | Treated as NONE (no state change). |

**Caller protocol enforcement** (simulation-only, via `$error`):

- `TOUCH` without `access_hit` is illegal — the caller saw a miss but is
  claiming to be touching an existing entry.
- `INSTALL` while `access_hit` is illegal — the key is already present and
  reinstalling would create a duplicate.
- The internal match vector must be at most one-hot.

The natural compressor pattern is `TOUCH-on-hit / INSTALL-on-miss`, which
satisfies all three constraints by construction.

### Per-Slot Update Mechanics

On every clock edge:

| Action | What happens to slot `i` |
|---|---|
| `NONE` or reserved | Unchanged. |
| `TOUCH` matching slot `P` | Slots `1..P` each take their predecessor's contents (slot `i` <= slot `i-1`), so the entries formerly at `0..P-1` shift down by one and the matched entry's old position `P` is overwritten. Slot 0 becomes the (matched key, new_data). Slots **above** `P` are untouched. |
| `INSTALL` when `!cam_full` | Insertion position is `cam_count`. Slots `1..cam_count` shift down from `0..cam_count-1`. Slot 0 becomes the new entry. `cam_count++`. |
| `INSTALL` when `cam_full` | Insertion position is `DEPTH-1` (overwriting the LRU). Slots `1..DEPTH-1` shift down from `0..DEPTH-2`. Slot 0 becomes the new entry. `evicted` pulses high. `cam_count` stays at `DEPTH`. |

A single `ALWAYS_FF_RST` block contains a `for` loop over slots 1..DEPTH-1,
each iteration gated by `do_shift && (CNT_WIDTH'(i) <= shift_to)` (slot 0 is
handled separately). Synthesis infers the same per-slot enables. This compiles to
~one LUT level per slot on the per-bit datapath — Vivado synthesises the
whole shift as `DEPTH` parallel small update cones.

### Per-Entry Timestamp Storage

Earlier revisions of the CAM stored only `(key, data)` per entry; the
compressor measured `delta_ts` against a single global `r_last_ts`.
That worked for single-source streams but collapsed compression to
raw whenever multiple sources interleaved templates with non-monotonic
absolute timestamps (the 4-channel STREAM characterization case).

The current CAM adds a **per-entry `r_ts[TS_WIDTH=24]` array** that
shifts in lockstep with the key and data on every `TOUCH` / `INSTALL`:

```
r_key[i], r_data[i], r_ts[i]   shift together when slot i moves
```

`access_old_ts` outputs the *pre-commit* timestamp at the matched slot
(valid only when `access_hit`) — i.e. the timestamp of the previous
record that used this template. The compressor uses it to compute
`delta_ts = src_ts_lo - cam_access_old_ts`, then writes the current
record's `source_ts[23:0]` back into the slot via `access_new_ts` in
the same cycle.

> **TS_WIDTH = 24 bits.** Format-B (the 23-bit-delta Tier-1 format)
> needs 24 bits to *detect* its delta overflow. 16 bits silently
> aliases large gaps to wrong encodes.

The CAM is therefore no longer pure opaque-payload — its caller
needs to drive `access_new_ts` along with `access_new_data` on every
`TOUCH` / `INSTALL`. The compressor wires this directly from the
incoming record's low 24 timestamp bits.

### Match Logic

The match vector is a parallel one-hot:

```systemverilog
always_comb begin
    for (int i = 0; i < DEPTH; i++) begin
        w_match_oh[i] = r_valid[i] && (r_key[i] == access_key);
    end
end
```

That's 1 LUT per bit × 32 bits × 49-bit equality. Vivado fuses each
equality into ~3 LUT levels; the whole match is independent of the rest of
the cycle's logic (no chained dependencies on shift/count signals). The
priority encoder feeding `access_idx` is then `DEPTH-1`-input.

---

## Testing

`val/amba/test_monbus_cam.py` runs 10 sub-tests covering:

1. Reset state (all empty, `cam_full=0`, no matches)
2. Install + lookup basic round-trip
3. Fill to `DEPTH-1` (no overflow path exercised)
4. `TOUCH` updates payload, idx becomes 0
5. `cam_full` asserts on the Nth install
6. LRU eviction on `INSTALL` when full
7. `evicted` pulses **only** on full-CAM install (not on lookup, not on touch)
8. Miss on absent key (no state change)
9. `TOUCH` moves the entry to MRU (the LRU-specific invariant)
10. Random stress (~500 ops at FUNC, 5000 at FULL) cross-checked against
    a Python LRU model

The Python model in the test is a bit-exact mirror of the RTL — same
storage semantics, same shift rules. Random stress is constrained to the
caller protocol (no `INSTALL` on hit, no `TOUCH` on miss) so the protocol
assertions never fire spuriously.

```bash
pytest val/amba/test_monbus_cam.py -v
```

REG_LEVEL parameter sweep (`gate` / `func` / `full`):

- **GATE:** 1 config (default 49/64/32)
- **FUNC:** 2 configs (+ small DEPTH=8)
- **FULL:** 6 configs (DEPTH 4/8/16/32, key 16/32/49/64, data 16/32/64)

---

## Related Modules

| Module | Role |
|---|---|
| [`monbus_compressor`](monbus_compressor.md) | Consumer of the CAM *semantics* this module specifies — but it instantiates [`monbus_cam_pipe`](monbus_cam_pipe.md), not this module |
| `bin/TBClasses/monbus/monbus_compressor.py` (`Cam` class) | Python golden mirror |
| [`monitor_trans_cam`](monitor_trans_cam.md) | Sister CAM, different use case (AXI ID matching, multi-port, no LRU) |

---

## Navigation

- [Back to Shared Infrastructure Index](../_book_monitor_index.md)
- [Back to rtl-amba Index](../index.md)
