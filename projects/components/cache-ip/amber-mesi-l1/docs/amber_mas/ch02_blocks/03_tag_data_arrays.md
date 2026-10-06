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
**Status:** RTL landed 2026-10-06; this chapter is the micro-architecture
contract the RTL implements. DV: `dv/tests/fub/test_amber_{tag,data}_array.py`,
green at gate/func/full across the default and tiny-formal geometries.

---

## Overview

Both arrays are per-way inferred RAMs — the same storage idiom the house
FIFOs and `sdpram_core` use internally, with the GLOBAL_REQUIREMENTS 1.2
synthesis attributes. They are **not** `sdpram_core` instances: `sdpram_core`
(`rtl/amba/shared`) is a FUB/AXI burst *slave*, the wrong shape for a
multi-way parallel tag lookup or single-beat random data readout. Each array
has one synchronous write port (one-hot way select) and two combinational
lookup ports: port A serves CPU/fill traffic and port B serves snoop traffic,
matching the port assignment below. Combinational read keeps the hit/miss
decision and the snoop CRRESP path inside one cycle; it maps to distributed
RAM (tags) / block RAM (data) rather than a wrapped burst slave.

The one-write / two-read shape exceeds a single physical 2-port BRAM; per-way
flat storage (`way * SETS + set` for tags, `way * (SETS*FILL_BEATS) + {set,
beat}` for data) lets synthesis bank per way at the default geometry. That is
the HAS F8 dual-port decision implemented at L1-array granularity.

---

## amber_tag_array

### Tag + state packing

Each way has its own `sdpram_core` instance, or the ways are banked into one instance per way depending on the synthesis attributes allowed by `GLOBAL_REQUIREMENTS.md`. The data width of each instance is:

```systemverilog
TAG_STATE_WIDTH = TAG_WIDTH + 3
```

where `TAG_WIDTH = ADDR_WIDTH - SET_INDEX_WIDTH - LINE_OFFSET_WIDTH` and the 3 bits carry `cache_state_t`.

The memory word is packed as `{tag[TAG_WIDTH-1:0], state[2:0]}` — verified by
the DV against per-location values that place nonzero patterns in both fields.

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

A snoop that requires data transfer reads the matching way from port B beat-by-beat. `amber_control` drives `b_addr = {snoop_set, beat}`, increments the beat counter each cycle until the line is complete, and supplies the hit way on `b_way` (from the tag compare on port B). The data is forwarded to `amber_snoop_resp` for CD transmission.

---

## Reset Behavior

The arrays carry **no reset port** (GLOBAL_REQUIREMENTS 1.4 — SRAM contents
are not reset, and real BRAM has no reset pin). After `aresetn` deassertion,
`amber_control` treats all ways as Invalid until the init walk completes;
option 1 from the pre-RTL review is the contract: a hardware sequence walks
all sets and writes `STATE_I` to every way (the DV TBs perform the same walk
so unwritten locations cannot leak X's). The formal proofs assume all lines
are Invalid after reset.

---

**Last Updated:** 2026-10-06
