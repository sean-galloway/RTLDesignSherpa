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

# Monitor Bus Group Family

**Modules:**
- `monbus_group_core.sv` — protocol-agnostic backend (filter, FIFOs, watermark/timeout burst writer, slice-counter slave-read drain)
- `monbus_axil_axil_group.sv` — wrapper: AXIL slave-read + AXIL master-write
- `monbus_axil_axi4_group.sv` — wrapper: AXIL slave-read + AXI4-burst master-write
- `monbus_axi4_axil_group.sv` — wrapper: AXI4-burst slave-read + AXIL master-write
- `monbus_axi4_axi4_group.sv` — wrapper: AXI4-burst slave-read + AXI4-burst master-write

**Location:** `rtl/amba/shared/`
**Category:** Monitor Bus → AXI / AXIL Aggregation
**Status:** Production Ready

---

## Overview

The `monbus_group` family is the **delivery layer** for the monitor bus.
It takes a single monbus stream — already arbitrated upstream if multiple
sources need to be merged — and:

1. **Filters** packets per protocol (drop / route-to-err-FIFO / route-to-write-FIFO)
2. **Drains** the error FIFO over a slave-read port for CPU IRQ handlers
3. **Streams** the write FIFO over a master-write port into a memory ring
4. **Optionally compresses** the write-path traffic before it lands in memory
   (gated by `USE_COMPRESSION=1`)

The family replaces the previous single `monbus_axil_group.sv` module. The
new design exposes the same behavior under four protocol-permutation
wrappers, so callers can pick the exact slave/master shape their fabric
demands without tying off "fake AXI4" fields on AXIL sides.

---

## Architecture

The diagram below is for the AXIL/AXIL variant; the other three wrappers
are structurally identical except for the leaf skids and the FUB-to-leaf
bridge (e.g., `axi4_slave_rd` instead of `axil4_slave_rd`).

```mermaid
%%{init: {'theme': 'neutral', 'themeVariables': { 'fontSize': '14px'}}}%%
flowchart TB
    subgraph MonInput["Monitor Bus Input"]
        MONBUS["monbus_valid/ready<br/>monbus_packet (128b)<br/>monbus_timestamp (64b)"]
    end

    subgraph Wrapper["monbus_axil_axil_group (wrapper)"]
        subgraph Core["monbus_group_core (protocol-agnostic)"]
            FILTER["Per-protocol filter<br/>(drop / err / write)<br/>+ per-event masks"]
            ERR_FIFO["Err FIFO<br/>192-bit records"]
            WRITE_FIFO["Write FIFO<br/>BEAT-granular<br/>(one entry = 64b)"]
            TS_CTR["Free-running 64-bit<br/>timestamp counter"]
            EXP["Raw expander<br/>(USE_COMPRESSION=0)<br/>3 beats/record"]
            COMP["Compressor<br/>(USE_COMPRESSION=1)<br/>1 slot/burst entry"]
            DRAIN["Slice counter<br/>3 beats per record<br/>(arlen-aware)"]
            WRITER["Burst writer<br/>watermark + timeout<br/>4KB-boundary aware"]
        end
        AXIL_RD["axil4_slave_rd<br/>(single-beat AR)"]
        AXIL_WR["axil4_master_wr<br/>(single-beat AW)"]
    end

    MONBUS --> FILTER
    FILTER -- "err_select=1<br/>not dropped" --> ERR_FIFO
    FILTER -- "default route" --> EXP
    FILTER -- "default route" --> COMP
    EXP --> WRITE_FIFO
    COMP --> WRITE_FIFO
    TS_CTR -.mon_time_out.-> MONBUS
    ERR_FIFO --> DRAIN
    WRITE_FIFO --> WRITER
    DRAIN --> AXIL_RD
    WRITER --> AXIL_WR
```

The module has **no built-in arbitration** — it is a single-input block.
Callers with N upstream sources (e.g., RAPIDS source+sink) instantiate a
separate `monbus_arbiter` upstream to merge their streams before feeding
the group. Keeping arbitration orthogonal to capture means the family
never has to duplicate the arbiter for each consumer's input count.

---

## Why one core + four wrappers?

SystemVerilog cannot conditionally include or exclude ports from a
single module's port list. The port list is a static syntactic
construct, fixed at module declaration. So to give each protocol
combination an exact port shape — no spurious AXI4-only fields for the
caller to tie off — the family is split:

- **One common backend** (`monbus_group_core.sv`) carries the filter,
  FIFOs, watermark/timeout burst-writer FSM, slice-counter drain, and
  optional compressor. Its FUBs are AXI4-shaped on both sides (id /
  awlen / awsize / awburst / wlast / arlen / rlast / etc.). AXIL
  wrappers feed single-beat defaults (`len=0`, `size=3`, `burst=INCR`,
  `id=0`) and force `MAX_BURST_BEATS=1`.
- **Four thin wrappers**, each with the right protocol-shaped port
  list, that directly instantiate the matching leaf skids
  (`axi4_slave_rd` / `axil4_slave_rd` and `axi4_master_wr` /
  `axil4_master_wr`) and bridge their FUBs to the core's FUB.

| Wrapper | Slave-read shape | Master-write shape | `MAX_BURST_BEATS` (default) |
|---|---|---|---|
| `monbus_axil_axil_group` | AXIL `s_axil_ar*/r*` | AXIL `m_axil_aw*/w*/b*` | 1 |
| `monbus_axil_axi4_group` | AXIL `s_axil_ar*/r*` | AXI4 `m_axi_aw*/w*/b*` (full) | 64 |
| `monbus_axi4_axil_group` | AXI4 `s_axi_ar*/r*` (full) | AXIL `m_axil_aw*/w*/b*` | 1 |
| `monbus_axi4_axi4_group` | AXI4 `s_axi_ar*/r*` (full) | AXI4 `m_axi_aw*/w*/b*` (full) | 64 |

Callers pick the wrapper module name matching their fabric. The bare
`monbus_group_core` is not intended to be instantiated directly — its
AXI4-shaped FUBs are an internal contract.

---

## Common Parameters

All wrappers expose the same set of behavioral knobs (per-wrapper
parameters like `AXI_ID_WIDTH` / `AXI_USER_WIDTH` are only present
where at least one side is AXI4):

| Parameter | Default | Notes |
|---|---|---|
| `FIFO_DEPTH_ERR` | 64 | Error FIFO depth, in **records** (192-bit entries). |
| `FIFO_DEPTH_WRITE` | 96 | Write FIFO depth, in **beats** (64-bit entries). 96 beats = 32 raw records. |
| `ADDR_WIDTH` | 32 | Address width on both slave and master ports. |
| `FLUSH_TIMEOUT_CYCLES` | 1024 | Cycles since the last accepted W handshake before the writer fires a timeout-driven flush. |
| `MAX_BURST_BEATS` | 1 (AXIL master) / 64 (AXI4 master) | Maximum beats per master-write burst. AXI4 protocol max is 256. |
| `NUM_PROTOCOLS` | 3 | Informational — AXI, AXIS, CORE filter configs are unconditional. |
| `USE_COMPRESSION` | 0 | **Elaboration**: 0 omits the compressor entirely (raw-only build, minimum area); 1 elaborates the compressor so it can be selected at runtime via `cfg_compress_en`. The raw 3-beat-per-record path is always elaborated. |
| `HALF_BEAT_EN` | 0 | **Elaboration**: pack two 30-bit half-slots per 64-bit beat downstream of the compressor (`monbus_halfbeat_packer`), pushing tier-1 bandwidth from 1 beat/record toward 0.5 beat/record. Requires `USE_COMPRESSION=1`; folds away when 0. |
| `SKID_DEPTH_AR/R/AW/W/B` | 2/4/2/2/2 | Skid buffer depths for each channel. AXI4 wrappers default `SKID_DEPTH_W=4` to absorb burst W bursts. |

### Runtime config

In addition to the elaboration parameters, the group exposes runtime
inputs that pick mode and shape on the fly:

| Input | Width | Notes |
|---|---|---|
| `cfg_compress_en` | 1 | Runtime compression enable. Only effective when `USE_COMPRESSION=1` (otherwise the compressor isn't elaborated and the bit folds away). Must be stable while the write path is active. |
| `cam_clear` | 1 | **Synchronous CAM clear** (level-sensitive, sample one cycle while idle). Empties the compressor template CAM and zeroes the compressor stat counters so the next run starts with a fresh hit/miss profile — without asserting `axi_aresetn`. Tied off in raw-only builds (`USE_COMPRESSION=0`) where there is no CAM. Stream uses this on CTRL[4]. |
| `cfg_base_addr` / `cfg_limit_addr` | `ADDR_WIDTH` | Master-write address window. |
| `cfg_flush_watermark` | 16 | Master-write FIFO depth (in beats) at which a flush is triggered. |
| `cfg_<proto>_*_mask` / `cfg_<proto>_err_select` | 16 each | Per-protocol filter and err-FIFO routing masks; see the dedicated section below. |

---

## Beat Layout

The write-FIFO and slave-read drain are **beat-granular** (one queue
entry = one 64-bit beat). Two emit modes:

### Raw mode (`cfg_compress_en = 0`, or `USE_COMPRESSION = 0` build)

Each accepted monbus record becomes three sequential 64-bit beats in
the write FIFO:

```
beat 0 = {tag[3:0]=4'h0, source_ts[59:0]}
beat 1 = packet[127:64]
beat 2 = packet[63:0]
```

The expander is **atomic per record**: once it commits to driving the
ts beat, it drives beats 1 and 2 before accepting a new record. This
means partial records never appear in the FIFO, and the
master-write burst writer can safely round burst lengths down to a
multiple of 3.

The `tag` nibble in beat 0 is reserved for future on-the-wire format
variants. The raw writer hardwires it to `4'h0`.

### Compressed mode (`cfg_compress_en = 1`, requires `USE_COMPRESSION = 1` build)

`monbus_compressor` consumes `(packet, source_ts)` records via its
in-handshake and emits 64-bit self-tagged slots via its
out-handshake. Each slot becomes one beat directly in the write
FIFO. Slot tags (bits `[63:60]`):

```
4'h0 = raw expansion beat (Tier-0 fallback)
4'h1 = Tier-1 format A
4'h2 = Tier-1 format B
4'h3 = Tier-1 format C
4'h4..4'hF = reserved
```

See [`monbus_compressor.md`](monbus_compressor.md) for the encoder's
internal state and the byte-exact Python golden.

The raw expander is **always elaborated**; the compressor is elaborated
only when `USE_COMPRESSION=1`. The two paths' FIFO-write outputs and
`monbus_ready` are muxed on `w_use_comp = (USE_COMPRESSION != 0) && cfg_compress_en`.
Only one path is ever active; the inactive one is gated off at its
input. `BEATS_PER_UNIT` (3 in raw, 1 in compressed) is therefore a
runtime quantity (`w_beats_per_unit`), feeding the burst-writer
geometry described below.

> **Note on switching modes:** `cfg_compress_en` must be stable while
> there is unflushed data in the write FIFO. Toggling it mid-stream
> would mix raw 3-beat records with compressed 1-beat slots at the
> same memory addresses — the host decoder couldn't reassemble them.
> Software should drain the FIFO (poll `write_fifo_count` to zero)
> before flipping the bit.

### Slave-read drain (both modes)

The slave-read port returns the same 3-beat layout per err-FIFO
record, sliced by an internal counter. In AXI4 mode, `arlen+1` beats
are emitted across the burst with `rlast` asserting on the final
beat; the slicer advances through records, and the FIFO entry is
popped only when slice 2 (`SLICE_PKT_LO`) fires. In AXIL mode each
AR returns one beat.

---

## Master-Write Behavior

The burst writer fires when **either**:

- `flush_trigger_watermark`: `r_fifo_beats >= cfg_flush_watermark`
- `flush_trigger_timeout`: `r_timeout_cnt >= FLUSH_TIMEOUT_CYCLES`

…and at least `BEATS_PER_UNIT` beats are available (3 in raw mode, 1
in compressed mode).

### Burst geometry: 3-stage pipeline + fresh-FIFO cap at commit

The drain-plan math was originally a single combinational chain off
`r_wr_addr` feeding straight back into `r_wr_addr` — the 100 MHz
critical path on Nexys A7 (-1) (WNS −7.06 ns post-route). Since
`r_wr_addr` is stable while the writer sits in `WR_IDLE` (only `WR_W`
advances it) and the write FIFO only grows there, the **address
geometry** is now a **3-stage registered pipeline**:

```
stage 1 (caps):           bytes_to_limit / bytes_to_4kb from r_wr_addr,
                          plus the rewind decision (geom_addr).
stage 2 (planned):        min-cap tree + whole-record /3 rounding
                          via u_mod3_geo (see "mod-3 rounding" below).
stage 3 (rounded + addr): r_plan_geo_units (address-feasible whole-
                          record count) + r_plan_addr (eff_addr).
```

A `geom_valid` settle counter holds the plan invalid for the first
few cycles after `r_wr_addr` moves so the pipeline can reflect the
settled address before the FSM commits.

#### Rewind-snap: in-window with no record-room left

If a flush fires while `r_wr_addr` is in-window but the remaining bytes
to the next 4KB boundary cannot fit a whole record, the pipeline
produces `r_plan_ok=false` (units rounded down to zero) and the writer
would otherwise wedge in `WR_IDLE`. The FSM detects this case
(`do_flush && geom_valid && !r_plan_ok && r_wr_addr != cfg_base_addr`)
and **snaps `r_wr_addr` to `cfg_base_addr`**, staying in `WR_IDLE` so
the pipeline re-settles with fresh geometry. The next pipeline output
(after the settle counter expires) has `r_plan_ok=true` provided
`cfg_base_addr` itself has at least one whole record's worth of room
before the next 4KB line — the host's responsibility.

This case is hit by the AXIL/AXIL master_write stress in Phase 5,
where `cfg_base_addr` is intentionally placed only a few beats below a
4KB boundary so the very first drain has to wrap-snap before it can
emit anything.

The **FRESH FIFO-occupancy cap** is applied combinationally at the
`WR_IDLE` commit (not inside the pipeline):

```
// Pipeline produces r_plan_geo_units = address-feasible whole-record beats.
// At commit time, cap by the CURRENT FIFO contents:
units_commit = min(r_plan_geo_units, w_fifo_units)
```

where `w_fifo_units = r_fifo_beats - (r_fifo_beats mod 3)` (or
`r_fifo_beats` itself in compressed mode where the unit is 1 beat).
This matters because the FIFO keeps filling while the writer sits in
`WR_IDLE`; a stale (3-cycle-old) FIFO count would short the burst —
for example, capping a watermark-triggered 24-beat plan to 21. The
fresh path starts from a single counter (no address subtract/shift),
so it doesn't recreate the critical path.

Per-AW sub-burst sizing happens **inside the FSM**, capping each AW
by `MAX_BURST_BEATS`:

```
sub_burst_beats = min(remaining_in_cycle, MAX_BURST_BEATS)
awlen           = sub_burst_beats - 1
```

The split between drain-cycle plan (whole records) and per-AW
sub-burst (`MAX_BURST_BEATS`) is what makes the family work for both
AXIL (`MAX_BURST_BEATS = 1`) and AXI4 masters in raw mode
(`BEATS_PER_UNIT = 3`):

- **AXI4 master, raw mode:** one drain cycle ≈ one large sub-burst.
  e.g. 24 beats = 8 records in a single AW + 24 × W + B. Throughput-
  optimal.
- **AXIL master, raw mode:** one drain cycle = N single-beat
  sub-bursts. Each record requires three AW + 1 × W + B handshakes at
  consecutive addresses. The memory image is identical to the AXI4
  case; only the address-channel handshake count differs.

### Address-window behavior: **wrap, not saturate**

The master-write address is **circular** within `[cfg_base_addr,
cfg_limit_addr]`. When the writer rolls past the window's end (or starts
out of window, e.g. `r_wr_addr = 0` immediately after reset), the
geometry pipeline finds `r_wr_addr` outside `[cfg_base_addr,
cfg_limit_addr]` and computes against a pre-rewound `geom_addr =
cfg_base_addr`. The final `r_plan_addr` reflects that rewind — so the
next burst starts at `cfg_base_addr` and the dump ring keeps moving
forever.

This is **not** a saturation behavior. The writer never stalls at
`cfg_limit_addr`; it always wraps. Any host-side bookkeeping
(SRAM-dump write pointer, ring-buffer position cursor, etc.) **must
match this wrap behavior** — saturating a host-visible pointer at the
SRAM cap will desynchronize it from the actual ring state. The
`stream_char_harness.sv` debug pointer was fixed for exactly this
reason on 2026-06-14 (`d82b1e04`); see that commit message for the
hardware-confirmed symptom.

### mod-3 rounding (no `/3` operator)

Rounding a beat count down to a whole record (`X − (X mod 3)`) is done
by two `mod_3_compress` instances (`u_mod3_geo`, `u_mod3_fifo`) — a
carry-save-compressor implementation of `X mod 3` via base-4 digit
sum (each 2-bit group has weight `4^k ≡ 1 mod 3`). No `*` or `/`
operators, so Vivado neither infers a DSP48 (a combinational path
through a far-placed DSP was catastrophic) nor a CARRY4 iterative
divider — both used to blow timing. Exhaustively verified for all
65 536 inputs (`val/common/test_mod_3_compress.py`).

### Final port behavior

`awsize` is fixed at 3 (8 bytes per beat) and `awburst` at INCR
(`2'b01`). `awlen` is `sub_burst_beats - 1`. `wlast` asserts on the
final beat of each sub-burst.

---

## Per-Protocol Filter Configuration

The filter is configured per protocol (AXI, AXIS, CORE). For each
protocol the caller provides:

- `cfg_<proto>_pkt_mask[15:0]` — drop the packet if the bit at
  `pkt_type` is set.
- `cfg_<proto>_err_select[15:0]` — route to the err FIFO if the bit at
  `pkt_type` is set (and not dropped). All other surviving packets go
  to the write FIFO.
- `cfg_<proto>_<event_type>_mask[15:0]` — per-event-code mask. If the
  bit at `event_code[3:0]` is set, the packet is dropped regardless
  of the above. Per-protocol event categories differ:
  - **AXI:** error, timeout, compl, thresh, perf, addr, debug
  - **AXIS:** error, timeout, compl, credit, channel, stream
  - **CORE:** error, timeout, compl, thresh, perf, debug

Per-event masks are 16 bits but only `event_code[3:0]` indexes; codes
≥ 16 are treated as "not in mask range" (no masking applied).
Protocols not in the supported set (APB=2, ARB=3) are always
dropped.

---

## Sub-modules Instantiated

| Sub-module | Role |
|---|---|
| `axi4_slave_rd` / `axil4_slave_rd` | Slave-read skid (one per wrapper) |
| `axi4_master_wr` / `axil4_master_wr` | Master-write skid (one per wrapper) |
| `gaxi_fifo_sync` × 2 | Err FIFO + write FIFO inside the core |
| `monbus_compressor` (conditional) | Compressed-mode encoder; only when `USE_COMPRESSION=1` |
| `monbus_halfbeat_packer` (conditional) | Pairs two 30-bit half-slots into one 64-bit beat downstream of the compressor; only when `HALF_BEAT_EN=1` (which itself requires `USE_COMPRESSION=1`) |
| `monbus_cam_pipe` (transitive) | **Pipelined** 49-bit-key LRU CAM with per-template `last_ts`/`last_data`; replaces the unpipelined `monbus_cam` as the in-production CAM inside the compressor. See [`monbus_cam`](monbus_cam.md) for the deprecation note. |
| `mod_3_compress` × 2 (`rtl/common/`) | Geometry / FIFO whole-record rounding (X − (X mod 3)) |
| `math_adder_carry_save_nbit` (transitive) | 3:2 compressor primitive used by `mod_3_compress` |
| `gaxi_skid_buffer` (inside compressor) | Input skid on the `(source_ts, packet)` feed; breaks the aggregator → CAM long route |

### Canonical filelist

A single canonical filelist enumerates the group core's dependency
tree so a new core dep lands in **one place**:

```
rtl/amba/filelists/monbus_group.f
```

It lists `math_adder_carry_save_nbit` + `mod_3_compress` + `monbus_cam` +
`monbus_compressor` + `monbus_group_core`. All consumers (`val/amba`
tests, RAPIDS / STREAM macro filelists) `-f`-include it rather than
listing those sources inline.

---

## Status / Debug Outputs

Common to all wrappers:

| Output | Width | Meaning |
|---|---|---|
| `irq_out` | 1 | High whenever the err FIFO is non-empty |
| `err_fifo_full` | 1 | Err FIFO write port not ready |
| `write_fifo_full` | 1 | Write FIFO write port not ready |
| `err_fifo_count` | 16 | Err FIFO entry count (records) |
| `write_fifo_count` | 16 | Write FIFO entry count (beats) |
| `mon_time_out` | 64 | Free-running timestamp counter |
| `mon_compressor_stat_*` | 32 each | Compressor statistics, only live when `USE_COMPRESSION=1`; tied to 0 in raw mode |

The compressor stat ports stay in the port list regardless of
elaboration mode so wrapper layers see a consistent port surface;
only their semantics differ.

---

## Test

Verification lives in `val/amba/`:

- `test_monbus_axil_axil_group.py` — basic flow + err-FIFO drain on
  the AXIL/AXIL wrapper (slave-read coverage; master-write side is
  driven into a synthetic sink in this test).
- `test_monbus_axil_axil_group_compressed.py` — byte-exact compressed
  slot stream comparison against the Python `Encoder` golden across
  three phases (small synth stream, real-silicon 682-record dataset,
  wrap-window).
- `test_monbus_axil_axil_group_master_write.py` — raw-mode
  master-write coverage on the AXIL/AXIL wrapper. Three phases:
  watermark-driven flush (asserts `3*N` beats at 8-byte stride
  starting at `cfg_base_addr`), timeout-driven flush, window
  wrap-back. The test that would have caught the AXIL-master raw-mode
  flush deadlock fixed on 2026-06-11.
- `test_monbus_axil_axi4_group.py` — AXI4 burst master-write
  coverage on the AXIL/AXI4 wrapper. Three phases: watermark-driven
  multi-beat burst, timeout-triggered flush, 4KB-boundary respect.
- `test_monbus_axi4_axil_group.py` — dedicated AXI4-slave +
  AXIL-master coverage. Phase 1 covers the master-write raw-mode
  flush; Phase 2 covers the AXI4 burst slave-read drain (asserts
  `rlast` timing across a 6-beat AR with custom `arid`).

```bash
pytest val/amba/test_monbus_axil_axil_group.py \
       val/amba/test_monbus_axil_axil_group_compressed.py \
       val/amba/test_monbus_axil_axil_group_master_write.py \
       val/amba/test_monbus_axil_axi4_group.py \
       val/amba/test_monbus_axi4_axil_group.py -v
```

`monbus_axi4_axi4_group` does not yet have a dedicated test; its
master-write path is covered by `test_monbus_axil_axi4_group.py` (same
master leaf) and its AXI4-burst slave-read drain is covered by
`test_monbus_axi4_axil_group.py` Phase 2 (same slave leaf). Adding a
direct test for the pure-AXI4 wrapper is a future-work item.

---

## Migration from `monbus_axil_group`

The legacy `monbus_axil_group.sv` module is gone. Callers should
migrate to the wrapper matching their fabric. Key port-surface
changes:

1. **`S_AXIL_DATA_WIDTH` / `M_AXIL_DATA_WIDTH` parameters dropped** —
   data width is locked at 64 bits in the family.
2. **`cfg_flush_watermark[15:0]` is a new required input.** Set to 1
   for the legacy "fire immediately" behavior; set higher to batch.
3. **`err_fifo_count` and `write_fifo_count` are now 16 bits** (were 8).
4. **`FIFO_DEPTH_WRITE` is in beats**, not records. 32 records of the
   legacy module = 96 beats in raw mode.

Example (AXIL/AXIL — the closest analog to the legacy module):

```systemverilog
// Old
monbus_axil_group #(
    .FIFO_DEPTH_ERR    (64),
    .FIFO_DEPTH_WRITE  (32),   // records
    .S_AXIL_DATA_WIDTH (64),
    .M_AXIL_DATA_WIDTH (64),
    .USE_COMPRESSION   (0)
) u_group (...);

// New
monbus_axil_axil_group #(
    .FIFO_DEPTH_ERR       (64),
    .FIFO_DEPTH_WRITE     (96),   // beats (3x for raw mode)
    .FLUSH_TIMEOUT_CYCLES (1024),
    .USE_COMPRESSION      (0)
) u_group (
    .cfg_flush_watermark  (16'd24),  // 8 records worth, eager flush
    ...
);
```

For AXI4 burst capture (e.g., when the memory ring lives behind an
AXI4 fabric and you want to bunch records into multi-beat bursts to
amortize address-channel overhead), switch the wrapper to
`monbus_axil_axi4_group` and pick `MAX_BURST_BEATS` to taste.

---

## Related Modules

| Module | Role |
|---|---|
| [`monbus_compressor`](monbus_compressor.md) | Bulk-trace encoder used when `USE_COMPRESSION=1` |
| [`monbus_cam_pipe`](monbus_cam_pipe.md) | Pipelined LRU CAM backing the compressor (production) |
| [`monbus_cam`](monbus_cam.md) | Unpipelined reference CAM (superseded by `monbus_cam_pipe`) |
| [`monbus_arbiter`](monbus_arbiter.md) | Upstream multi-source merge (instantiate before this family if you have N>1 sources) |
| [`sdpram_slave`](sdpram_slave.md) | Canonical memory-ring backend for the master-write port (AXIL/AXIL variant pairs with `sdpram_slave_axil_axil`) |
| [`axi_monitor_base`](axi_monitor_base.md) | Source of the monitor packets this family captures |
| [`axi_monitor_reporter`](axi_monitor_reporter.md) | Per-protocol packet-emission frontend |
