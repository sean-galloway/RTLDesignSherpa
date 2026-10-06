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

# amber_tag_array and amber_data_array

**Modules:** `amber_tag_array.sv`, `amber_data_array.sv`
**Location:** `projects/components/cache-ip/amber-mesi-l1/rtl/fub/`
**Status:** Pre-RTL micro-architecture contract

---

## Overview

Both arrays are built from the house `sdpram_core` primitive. They are simple dual-port RAMs: one write port and one read port per physical instance, mapped so that port A serves CPU/fill traffic and port B serves snoop traffic. The HAS F8 decision (dual-port `sdpram_core`) is implemented here.

---

## amber_tag_array

### Tag + state packing

Each way has its own `sdpram_core` instance, or the ways are banked into one instance per way depending on the synthesis attributes allowed by `GLOBAL_REQUIREMENTS.md`. The data width of each instance is:

```systemverilog
TAG_STATE_WIDTH = TAG_WIDTH + 3
```

where `TAG_WIDTH = ADDR_WIDTH - SET_INDEX_WIDTH - LINE_OFFSET_WIDTH` and the 3 bits carry `cache_state_t`.

The memory word is packed as `{tag[TAG_WIDTH-1:0], state[2:0]}`.

### Port assignment

| Port | Traffic | Operations |
|------|---------|------------|
| A | CPU / fill | Read tag+state for lookup; write tag+state on fill or hit-state update. |
| B | Snoop | Read tag+state for snoop lookup. |

Port A is driven by `amber_control`. Port B is driven by `amber_control` during snoop handling.

### Addressing

The address into the tag array is the set index:

```systemverilog
tag_addr = req_addr[SET_INDEX_WIDTH + OFFSET_WIDTH - 1 : OFFSET_WIDTH]
```

Way selection is done by instantiating one `sdpram_core` per way and decoding the way index on writes. On reads, all ways return their tag+state in parallel and a comparator determines the hit way.

### Banking

For timing closure at larger geometries, each way is a separate physical memory instance. There is no cross-way banking; a fill or snoop reads all ways in parallel and writes one. This keeps the critical hit/miss decision a simple combinational comparison across `WAYS` tag outputs.

---

## amber_data_array

### Organization

The data array stores cache-line data. A line is `LINE_BYTES*8` bits wide and is split into `FILL_BEATS = LINE_BYTES / (BUS_WIDTH/8)` beats. Each way has its own `sdpram_core` instance, or one instance per way, with:

```systemverilog
DATA_MEM_DEPTH = SETS * FILL_BEATS
DATA_MEM_WIDTH = BUS_WIDTH
```

The address is `{set_index, beat_index}`.

### Port assignment

| Port | Traffic | Operations |
|------|---------|------------|
| A | CPU / fill | Read data on hit or replay; write fill beats. |
| B | Snoop | Read whole line for snoop data transfer. |

### Write masking

`sdpram_core` is instantiated with byte-write enable support. On a CPU write hit, only the bytes selected by `be` are written; the rest of the line is preserved. On a fill, the entire beat is written with all byte enables asserted. On a write-allocate miss, the fill data is merged with the CPU write data before installation.

### Snoop data readout

A snoop that requires data transfer reads the matching way from port B beat-by-beat. `amber_control` drives `data_b_addr = {snoop_set, beat}` and increments the beat counter each cycle until the line is complete. The data is forwarded to `amber_snoop_resp` for CD transmission.

---

## Reset Behavior

The `sdpram_core` contents are not reset. After `aresetn` deassertion, `amber_control` treats all ways as Invalid until the first access. Two implementation options are acceptable:

1. A software/init sequence walks all sets and writes `STATE_I` to every way.
2. An `initial` block (simulation only) or a one-cycle hardware clear loop invalidates all lines.

The chosen approach will be recorded when RTL lands. The formal proofs assume all lines are Invalid after reset.

---

**Last Updated:** 2026-10-06
