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

# l1_tag_array and l1_data_array

**Modules:** `l1_tag_array.sv`, `l1_data_array.sv`
**Location:** `projects/components/cache-ip/common-ip/rtl/fub/`
**Status:** RTL landed 2026-10-06; this chapter is the micro-architecture
contract the RTL implements. DV: `cache-ip/common-ip/dv/tests/test_l1_tag_array.py + test_l1_data_array.py`,
green at gate/func/full across the default and tiny-formal geometries.

---

## Overview

Both arrays are per-way inferred RAMs — the same storage idiom the house
FIFOs and `sdpram_core` use internally, with the GLOBAL_REQUIREMENTS 1.2
synthesis attributes. They are **not** `sdpram_core` instances: `sdpram_core`
(`rtl/amba/shared`) is a FUB/AXI burst *slave*, the wrong shape for a
multi-way parallel tag lookup or single-beat random data readout. Each array
has one synchronous write port (one-hot way select) and two read ports:
port A serves CPU/fill traffic and port B serves snoop traffic, matching the
port assignment below. The **tag** array reads combinationally, which keeps
the hit/miss decision and the snoop CRRESP decode inside one cycle; it maps
to distributed RAM. The **data** array's read latency is a parameter
(`SYNC_READ`, below): the cores set it to the registered read, which is
what block RAM provides.

The one-write / two-read shape exceeds a single physical 2-port BRAM. The
storage is one array **per way** (`mem[SETS]` for tags, `mem[SETS*FILL_BEATS]`
for data, inside a `generate` loop) rather than one flat array indexed
`way * SETS + set`: a flat array written at several addresses in one process
is not a RAM to Vivado and dissolves into flops (handbook
`design/sram-and-memories.md`, "Several write addresses in one process also
dissolve the array" — the per-way form was the 23k-LUT / 11k-FF per-core
finding of the FPGA review, 2026-11-06). Per way, synthesis banks each array
on its own. That is the HAS F8 dual-port decision implemented at L1-array
granularity.

---

## l1_tag_array

### Tag + state packing

Each way has its own `mem[SETS]` array (one `always_ff` write process per way, combinational read). The word width is:

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

Port A is driven by `l1_control`. Port B is driven by `l1_control` during snoop handling.

### Addressing

The address into the tag array is the set index:

```systemverilog
tag_addr = req_addr[SET_INDEX_WIDTH + OFFSET_WIDTH - 1 : OFFSET_WIDTH]
```

Way selection is the per-way array: the one-hot `wr_way_onehot` decodes the write, and on reads all ways return their tag+state in parallel and a comparator determines the hit way.

### Banking

For timing closure at larger geometries, each way is a separate physical memory instance. There is no cross-way banking; a fill or snoop reads all ways in parallel and writes one. This keeps the critical hit/miss decision a simple combinational comparison across `WAYS` tag outputs.

---

## l1_data_array

### Organization

The data array stores cache-line data. A line is `LINE_BYTES*8` bits wide and is split into `FILL_BEATS = LINE_BYTES / (BUS_WIDTH/8)` beats. Each way has its own `mem` array with:

```systemverilog
DATA_MEM_DEPTH = SETS * FILL_BEATS
DATA_MEM_WIDTH = BUS_WIDTH
```

The address is `{set_index, beat_index}`.

### Port assignment

| Port | Traffic | Operations |
|------|---------|------------|
| A | CPU / fill | Read one beat on hit or replay; write fill beats; victim gather (one beat per cycle). |
| B | Snoop | Read the matching way one beat at a time for the snoop data transfer. |

### Read latency (`SYNC_READ`)

| `SYNC_READ` | Read port | Mapping | Who uses it |
|---|---|---|---|
| 0 | combinational: `*_rdata` is the word at the address presented this cycle | distributed RAM (16k LUT at the default geometry) | unit benches, the `formal/` flats |
| 1 | registered: `*_rdata` is the word at the address presented **last** cycle; the way select is applied in the data cycle | block RAM (16 RAMB36 per core) | `l1_coh_core` / `jet_coh_core` (`DATA_SYNC_READ = 1`), hence every top and the boards |

With the registered read the controller presents each address one cycle before it consumes the word: the hit beat during `CTRL_LOOKUP`, gather beat k+1 while it writes gather beat k into the victim store, the snoop's beat 0 in the grant cycle and beat k+1 on each CD handshake. A fill beat landing at the same edge as the registered read of that beat returns the pre-write word (read-before-write), so the pending-fill bypass streams a beat only from the cycle after its landing (`pf_data_valid_d1`). Cycle behaviour is otherwise identical to the combinational build; the DV runs both. The rule and the failure that taught it: handbook `design/sram-and-memories.md`, "A cache data array belongs in block RAM: the read address leads by a cycle".

### Write masking

`sdpram_core` is instantiated with byte-write enable support. On a CPU write hit, only the bytes selected by `be` are written; the rest of the line is preserved. On a fill, the entire beat is written with all byte enables asserted. On a write-allocate miss, the fill data is merged with the CPU write data before installation.

### Snoop data readout

A snoop that requires data transfer reads the matching way from port B beat-by-beat. `l1_control` drives `b_addr = {snoop_set, beat}`, increments the beat counter on each accepted CD beat until the line is complete, and supplies the hit way on `b_way` (from the tag compare on port B). The data is forwarded to `l1_snoop_resp` for CD transmission. Under `SYNC_READ` the address leads: beat 0 is presented in the grant cycle and the port's word is always the current beat during the stream (a stalled beat re-presents itself).

---

## Reset Behavior

The arrays carry **no reset port** (GLOBAL_REQUIREMENTS 1.4 — SRAM contents
are not reset, and real BRAM has no reset pin). After `aresetn` deassertion,
`l1_control` treats all ways as Invalid until the init walk completes;
option 1 from the pre-RTL review is the contract: a hardware sequence walks
all sets and writes `STATE_I` to every way (the DV TBs perform the same walk
so unwritten locations cannot leak X's). The formal proofs assume all lines
are Invalid after reset.

---

**Last Updated:** 2026-11-07
