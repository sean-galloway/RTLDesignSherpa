# MonBus Packet: 64-bit → 128-bit Migration Plan

**Status:** **Executed** — packet is now 128 bits + 64-bit side-band timestamp
across packages, monitor core, 25 wrappers, both `monbus_axil_group`s, the
bridge generator, all subsystem reporters, the Python parser, and the formal
harnesses. Regression status (see §6 for the gate list):

- §6.1 Python parser tests: **20/20 PASS**
- §6.2 Bridge dv regression: **26/26 PASS**
- §6.3 Bridge-filelist sweep lint: **12/12 clean**
- §6.4 Formal proves re-checked: `axi_monitor_addr_check` (prove + cover) PASS,
  `axi_monitor_reporter` PASS, `axi_monitor_filtered` PASS, `axi_monitor_base`
  baseline-fails on un-migrated code too (not on the hook for this migration),
  `arbiter_monbus_common` makes progress to step ≥19/25 but is slower under
  the wider state — tractability follow-up, not a correctness regression.
- §6.5 STREAM/RAPIDS regression:
  - STREAM fub: **62/62 PASS**
  - STREAM macro+top: **all known failures fixed** (the 2 monbus_axil_group
    cases that initially failed flipped to PASS after switching the test
    from `DATA_WIDTH` to `S_AXIL_DATA_WIDTH`); coverage swept through 98%
    of parameterizations before wall-time cap
  - RAPIDS fub + fub_beats: **86/87 PASS** (1 TB-side memory-bounds in
    `test_ctrlwr_channel_reset`, not a packet-format issue)
  - RAPIDS macro + macro_beats: **90/90 PASS**

**One-shot atomic PR:** YES. Do **NOT** stage. Do **NOT** make `PACKET_WIDTH` runtime-parameterizable. Pick one width, sweep, commit.

---

## 1 — Why we're widening

The current 64-bit packet format packs `event_data` into only 35 bits. The
new `axi_monitor_addr_check` module then sub-allocates that 35-bit field as
`{range_index[4:0], is_read, addr[28:0]}` — leaving only **29 address bits**
in the packet.

That's:

| Address space | Outcome with 29-bit payload                                   |
| ------------- | ------------------------------------------------------------- |
| ≤ 512 MB      | Lossless                                                      |
| 32-bit, top-half mapped (e.g. `0x8000_0000`) | Top 3 bits truncated, ambiguous between range banks |
| 64-bit (RAPIDS) | 35 of 64 address bits lost — effectively unusable for forensics |

Workarounds (drop `is_read`, two-packet encoding, software inference from
range_index) all add complexity to either producer or consumer.  RAPIDS
uses 64-bit addresses today; a wider format is the right reset.

Beyond the address-payload issue, several other fields are running tight:

- `channel_id` (6 bits): can collide with multi-master AXI ID concatenation.
- `unit_id` (4 bits): only 16 subsystems repository-wide.
- `agent_id` (8 bits): bridge's stage-2 encoding `(port_idx << 4) | chan_bit`
  burns the low nibble; that leaves 4 bits of port index = 16 ports max.
- No on-wire timestamp / ordering signal: arbitrated packets lose
  temporal ordering relative to the wrapper that produced them.
  (Addressed downstream by the monbus_axil_group's optional
  timestamp-append on memory writes — see §4.4.1 — **not** by adding
  a field to the on-wire packet.)

128 bits gives us room to fix all of the above in one transaction.

---

## 2 — Proposed field layout

Locked-in layout (128 bits, no padding):

```
[127:124]  packet_type   (4 bits)   -- unchanged semantics
[123:109]  reserved     (15 bits)   -- forward-compat slack
[108:105]  protocol      (4 bits)   -- widen from 3
[104: 97]  event_code    (8 bits)   -- widen from 4 (gives 256 events/category)
[ 96: 88]  channel_id    (9 bits)   -- widen from 6
[ 87: 72]  agent_id     (16 bits)   -- widen from 8
[ 71: 64]  unit_id       (8 bits)   -- widen from 4
[ 63:  0]  event_data   (64 bits)   -- fits full 64-bit address with bits to spare
```

Total: 4 + 15 + 4 + 8 + 9 + 16 + 8 + 64 = **128 bits**.

### Timestamps are NOT in the on-wire packet

The on-wire monbus packet carries **no timestamp field**. Timestamping
uses a hybrid scheme:

* **Counter owned by `monbus_axil_group`** — one free-running
  `r_ts_counter[MONBUS_TS_WIDTH-1:0]` lives inside the group. Width
  is **locked at 64 bits** in `monitor_common_pkg.sv` (see §3) —
  same single-source-of-truth discipline as `MONBUS_PKT_WIDTH`. No
  module-level `TS_WIDTH` parameter, no SoC-level distribution
  network to design separately.

* **Counter routed OUT of the group** as `mon_time_out[MONBUS_TS_WIDTH-1:0]`,
  driven from `r_ts_counter`. The bridge top (or stream/rapids top)
  connects this to a shared `mon_time_w` net.

* **Every monitor wrapper takes `i_mon_time[MONBUS_TS_WIDTH-1:0]` as
  an input.** All wrappers see the same time value. Each wrapper
  samples it on event emission (same cycle as `monbus_valid`) and
  emits the sampled value as a **side-band `monbus_timestamp`
  output** alongside the packet.

* **`monbus_arbiter` carries `(monbus_packet, monbus_timestamp)`
  as a unit** — same grant cycle multiplexes both. Internally
  the skid buffer's `DATA_WIDTH` becomes
  `MONBUS_PKT_WIDTH + MONBUS_TS_WIDTH` (= 192 bits per client).

* **`monbus_axil_group` consumes the side-band** and can append
  either the source timestamp, its own arrival timestamp, or
  both, depending on cfg. See §4.4.1.

Net effect: source-time accuracy at the wrapper (no arbiter/FIFO
smearing), single ownership of the counter, parameter-driven width,
on-wire packet stays a clean 128 bits.

```
                          (free-running counter, TS_WIDTH bits)
                          +-------------------------------+
                          | monbus_axil_group             |
                          |   r_ts_counter ──► mon_time_out
                          +---------▲---------------------+
                                    │ packet + ts side-band
                                    │
                          +---------┴---------+
                          |  monbus_arbiter   |
                          | DATA = PKT+TS     |
                          +---------▲---------+
                                    │ per-client
                ┌───────────────────┼───────────────────┐
                │                   │                   │
         +------┴-----+      +------┴-----+      +------┴-----+
         | wrapper 0  |      | wrapper 1  |      | wrapper N  |
         | sample on  |      | sample on  |      | sample on  |
         | emit       |      | emit       |      | emit       |
         +-----▲------+      +-----▲------+      +-----▲------+
               │                   │                   │
               └───────── mon_time_w (broadcast) ──────┘
```

### Event-code 4 → 8 bits

The 19 typedef enums in `monitor_amba4_pkg.sv` (and `monitor_amba5_pkg.sv`)
currently declare event_code values as `logic [3:0]`. Bumping to 8 bits is
non-destructive: every existing value still fits in the low nibble. Just
widen the typedefs:

```diff
- typedef enum logic [3:0] {
+ typedef enum logic [7:0] {
       AXI_ERR_RESP_SLVERR = 4'h0,
```

The Python parser's IntEnum classes are unaffected (auto-extraction
regenerates them with whatever bit-width the SV declares).

### Why field widths chose what they did

- **`protocol` 4 bits:** AXI / AXIS / APB / ARB / CORE today (5 used of 8).
  4 bits = 16 protocols. Comfortable headroom.
- **`channel_id` 9 bits:** today's AXI ID can be up to 8 bits per the SV.
  Add 1 bit so a multi-master crossbar can OR-in the source port without
  needing a separate field.
- **`agent_id` 16 bits:** matches bridge's stage-2 encoding scheme
  `(port_idx << 4) | chan_bit` with 12 bits of port_index = 4096 ports.
  Future-proof against very large fabrics.
- **`unit_id` 8 bits:** 256 subsystems. Vast overprovision but cheap.
- **`event_data` 64 bits:** the whole point. Carries full 64-bit AXI address.

If anyone wants a different allocation, **negotiate before the sweep
begins**, not after.

---

## 3 — Single source of truth

Add to `rtl/amba/includes/monitor_common_pkg.sv`:

```systemverilog
// Monitor bus packet width. ANY consumer that declares a bus or FIFO
// holding a packet MUST reference this localparam, not hard-code 128.
localparam int MONBUS_PKT_WIDTH = 128;
typedef logic [MONBUS_PKT_WIDTH-1:0] monitor_packet_t;

// Monitor bus side-band timestamp width. Locked at 64 to:
//   - keep beats aligned on the 64-bit AXIL master in monbus_axil_group,
//   - be non-wrapping over any realistic capture window (~584 years
//     at 1 GHz vs ~4.3 s at 32-bit), and
//   - avoid per-instance parameter plumbing through 28+ wrappers.
// Same single-source-of-truth discipline as MONBUS_PKT_WIDTH — any
// site that needs a timestamp width references this, never literal 64.
localparam int MONBUS_TS_WIDTH = 64;
typedef logic [MONBUS_TS_WIDTH-1:0] monbus_timestamp_t;
```

Every `output logic [63:0] monbus_packet` site below becomes:

```systemverilog
output monitor_packet_t monbus_packet,
// or
output logic [MONBUS_PKT_WIDTH-1:0] monbus_packet,
```

Pick `monitor_packet_t` (the typedef) for SV; pick the localparam for
parameterised modules where the typedef would force a package import.

**Do NOT** add `parameter int PACKET_WIDTH = 128` or `parameter int
TS_WIDTH = ...` to any module. Locking both widths to package
localparams means there's exactly one packet format and one timestamp
format in the codebase. Future width changes are another atomic PR.

---

## 4 — File-by-file punch list

### 4.1 — Package files (start here — they define the format)

| File | Change |
| ---- | ------ |
| `rtl/amba/includes/monitor_common_pkg.sv` | Add `MONBUS_PKT_WIDTH`/`monitor_packet_t`. Widen all `get_*` / `create_monitor_packet` functions and their bit slices to the new layout. |
| `rtl/amba/includes/monitor_pkg.sv` | Mirror the above (re-exports). |
| `rtl/amba/includes/monitor_amba4_pkg.sv` | Widen 19 `typedef enum logic [3:0]` → `[7:0]`. |
| `rtl/amba/includes/monitor_amba5_pkg.sv` | Same. |

### 4.2 — Monitor core and helpers

| File | Change |
| ---- | ------ |
| `rtl/amba/shared/axi_monitor_base.sv` | `monbus_packet` port + every internal `[63:0]` net → `monitor_packet_t`. **NEW: input `i_mon_time[MONBUS_TS_WIDTH-1:0]`, output `monbus_timestamp[MONBUS_TS_WIDTH-1:0]`** (both widths come from the package localparam — no module parameter). Sample `i_mon_time` on the same cycle the reporter asserts `monbus_valid`; drive that sampled value on `monbus_timestamp`. |
| `rtl/amba/shared/axi_monitor_reporter.sv` | Same packet-width updates. **NEW: pipeline the sampled-time register alongside the packet so it flows out coincident with `monbus_valid`.** |
| `rtl/amba/shared/axi_monitor_filtered.sv` | Same packet-width updates. Pass-through for the timestamp side-band (no semantics here, just route it). |
| `rtl/amba/shared/axi_monitor_addr_check.sv` | Restructure `event_data_field`. Drop `is_read` (recover from `IS_READ` parameter on consumer). Keep `range_index`. Put full address in low 64 bits of event_data. **NEW: also drive its own `monbus_timestamp` output by sampling `i_mon_time` on emission.** |
| `rtl/amba/shared/monbus_arbiter.sv` | (1) `monbus_packet_in[CLIENTS]`, `monbus_packet`, internal skid buffers → `MONBUS_PKT_WIDTH`. (2) **NEW: `monbus_timestamp_in[CLIENTS]` array (each `MONBUS_TS_WIDTH` wide), `monbus_timestamp` output.** Single combined skid buffer with `DATA_WIDTH = MONBUS_PKT_WIDTH + MONBUS_TS_WIDTH` so both fields ride the same grant cycle atomically. Pack/unpack at the buffer boundary. |
| `rtl/amba/shared/arbiter_monbus_common.sv` | Update event-packet assembly. |
| `rtl/amba/shared/arbiter_rr_pwm_monbus.sv` | Same. |
| `rtl/amba/shared/arbiter_wrr_pwm_monbus.sv` | Same. |

#### 4.2.1 — Wrapper ports: new inputs/outputs

Every `axi4/axi5/axil4/apb` `_mon` (and `_mon_cg`) variant — **28 files**
(12 snooping + 12 CG axi4/axil4/axi5 + apb_monitor + apb5_monitor +
the 2 arbiter monbus wrappers which carry the packet but no addr) —
needs the same two port additions in addition to the packet-width bump:

```systemverilog
// NEW inputs/outputs alongside the existing monbus signals.
// Widths come from monitor_common_pkg::MONBUS_TS_WIDTH (= 64) — no
// module parameter, no per-instance plumbing.
input  monbus_timestamp_t   i_mon_time,
output monbus_timestamp_t   monbus_timestamp,
```

The `gen_no_monitor` branch ties `monbus_timestamp` to all-zero, matching
the existing `monbus_valid = 1'b0`/`monbus_packet = '0` pattern.

### 4.3 — Wrapper variants (32 files, mechanical)

All have an `output logic [63:0] monbus_packet` port + an internal
`gen_no_monitor` branch that drives `monbus_packet = 64'h0`. Change both.

```
rtl/amba/axi4/axi4_master_rd_mon.sv         + _cg, _wr, _wr_cg
rtl/amba/axi4/axi4_slave_rd_mon.sv          + _cg, _wr, _wr_cg
rtl/amba/axi5/axi5_master_rd_mon.sv         + _cg, _wr, _wr_cg
rtl/amba/axi5/axi5_slave_rd_mon.sv          + _cg, _wr, _wr_cg
rtl/amba/axil4/axil4_master_rd_mon.sv       + _cg, _wr, _wr_cg
rtl/amba/axil4/axil4_slave_rd_mon.sv        + _cg, _wr, _wr_cg
rtl/amba/apb/apb_monitor.sv
```

### 4.4 — Monitor-group consumers

| File | Change |
| ---- | ------ |
| `projects/components/stream/rtl/macro/monbus_axil_group.sv` | (1) `monbus_valid/ready/packet` port + internal FIFOs (`gaxi_fifo_sync`, `DATA_WIDTH(128)`). (2) **Bump `m_axil_*` data width from 32 to 64** so a 128-bit packet writes in 2 beats; with timestamp-append enabled and 64-bit timestamps, a packet+stamp writes in 3 beats. Slave AXIL stays 32-bit (CPU reads IRQ status one word at a time). (3) **NEW: optional timestamp-append on the AXIL master write path** — see below. |
| `projects/components/rapids/rtl/macro/monbus_axil_group.sv` | Same as above. |

#### 4.4.1 — Counter ownership, distribution, and timestamp append

`monbus_axil_group` is the **counter authority** for the entire monitor
mesh. It owns the free-running counter, distributes it upstream, and
consumes the source-time side-band coming back through the arbiter.

**No module parameter** — timestamp width is locked at `MONBUS_TS_WIDTH`
(= 64) in `monitor_common_pkg.sv` (§3). The module just imports the
package.

**New ports (added to existing port list):**
```systemverilog
// Source-time distribution: drive this to every wrapper's i_mon_time
output monbus_timestamp_t   mon_time_out,

// Side-band timestamp arriving with each input monbus packet
input  monbus_timestamp_t   monbus_timestamp,

// Configuration -- end-user-selectable append behaviour
input  logic        cfg_ts_append_enable,   // 0 = packets only, 1 = append
input  logic [1:0]  cfg_ts_append_mode,     // 00 = packet only (cfg_ts_append_enable=0)
                                            // 01 = packet + source ts
                                            // 10 = packet + arrival ts
                                            // 11 = packet + both (source first; default — see §8.6)
```

**Internal counter and source distribution:**
```systemverilog
monbus_timestamp_t r_ts_counter;
`ALWAYS_FF_RST(axi_aclk, axi_aresetn,
    if (`RST_ASSERTED(axi_aresetn))  r_ts_counter <= '0;
    else                              r_ts_counter <= r_ts_counter + 1'b1;
)
assign mon_time_out = r_ts_counter;
```

**Arrival-time capture:** sample `r_ts_counter` on the `monbus_valid &&
monbus_ready` handshake at the group's input and latch alongside the
incoming `monbus_timestamp` (source time) and the packet body in the
write FIFO. The write FIFO now carries 3 columns:

```
{packet[127:0], source_ts[TS_WIDTH-1:0], arrival_ts[TS_WIDTH-1:0]}
```

A single 64-deep FIFO holding that combined record stays the simplest
implementation; if area is tight, split into a packet FIFO and a parallel
timestamp side-FIFO with synchronized pointers.

**Write FSM extension** — after the existing packet-body beats (2 × 64-bit
beats on the bumped 64-bit AXIL master), emit additional beats per
`cfg_ts_append_mode`:

```
addr +  0:  packet[63:0]                       packet body
addr +  8:  packet[127:64]                     packet body
addr + 16:  source_ts                          if mode = 01 or 11
addr + 16/24:  arrival_ts                      if mode = 10 (at +16) or 11 (at +24)
```

Record size depends only on (cfg_ts_append_enable, cfg_ts_append_mode)
— `MONBUS_TS_WIDTH` is locked at 64, so there's no width axis:

| append_enable | append_mode  | Record bytes | AXIL beats @ 64-bit master |
| ------------- | -----------  | ------------ | -------------------------- |
| 0             | x            | 16           | 2                          |
| 1             | 01 (source)  | 24           | 3                          |
| 1             | 10 (arrival) | 24           | 3                          |
| 1             | 11 (both)    | 32           | 4                          |

The existing `cfg_base_addr` / `cfg_limit_addr` window honours whatever
record size results — wrap at limit, rewind to base. Every record is a
multiple of 8 bytes (one full master beat) — no half-beat alignment
hazards. This is one of the reasons `MONBUS_TS_WIDTH` is locked at 64
(see §4.4.2 for the full storage-footprint analysis).

**Python parser implication:** `parse_stream()` gains optional
`stride_bytes=` (default 16, packet-only). When timestamps are enabled
the consumer passes the matching stride and receives a richer object:

```python
@dataclass(frozen=True)
class TimestampedPacket:
    packet: MonitorPacket
    source_ts: Optional[int]    # None if append_mode != 01 / 11
    arrival_ts: Optional[int]   # None if append_mode != 10 / 11
```

`parse_stream()` becomes:

```python
def parse_stream(raw_words, stride_bytes=16, ts_mode=0):
    """Parse a memory dump produced by monbus_axil_group.
    raw_words: iterable of 64-bit ints (the AXIL master writes 64-bit beats).
    Yields MonitorPacket or TimestampedPacket depending on ts_mode.
    Timestamp width is fixed at 64 bits (monbus_timestamp_t in the SV)."""
```

Sample-time ordering note: because every wrapper sees the same
`mon_time_w` and samples on its OWN emission cycle, packets from
different wrappers carry **directly comparable** source timestamps. The
arrival timestamp is also directly comparable across packets, but
typically lags the source timestamp by the wrapper-to-group latency
(monitor internal FIFO + arbiter grant + skid buffers). Use mode 11 if
you want to measure that latency — this is the default at reset (see
§8.6).

#### 4.4.2 — Storage footprint and bandwidth implications

The packet-width bump (64 → 128) plus the new timestamp side-band
(0 → 64 bits) changes the per-event memory footprint significantly:

| Era                              | Bytes / event | Beats @ master |
| -------------------------------- | ------------- | -------------- |
| Old (64-bit packet, no TS)       |  8            | 1 (32-bit) or 1 (64-bit) |
| New, append_mode=00 (none)       | 16            | 2 (64-bit)     |
| New, append_mode=01 or 10 (one TS)| 24           | 3 (64-bit)     |
| New, append_mode=11 (both TS)    | 32            | 4 (64-bit)     |

That's a **3–4× growth** at the consumer per event compared to the old
format. Three places need to account for this:

1. **Memory window sizing.** `cfg_base_addr` / `cfg_limit_addr` ring
   in `monbus_axil_group` fills 3–4× faster at the same event rate.
   Any external code that pre-allocates the capture buffer in terms
   of "N events × 8 bytes" needs to be updated to "N events × 16/24/32"
   based on the configured `cfg_ts_append_mode`.

   Example: a bridge emitting 50 K events/s previously consumed
   400 KB/s of capture bandwidth. After the migration:
     - mode 00:   800 KB/s
     - mode 01:  1.2 MB/s
     - mode 11:  1.6 MB/s

2. **AXIL master write-pipe utilization.** A burst of N events now
   issues 2N/3N/4N W-beats instead of N. The internal write FIFO in
   `monbus_axil_group` must size for `(peak_event_rate ×
   max_master_backpressure × beats_per_record)`. Today's depth was
   sized for 1 beat per event — re-evaluate with the new worst case.
   Recommended minimum depth: `2 × beats_per_record × MAX_TRANSACTIONS`
   so a transient backpressure stall doesn't drop events.

3. **Beat alignment is why `MONBUS_TS_WIDTH = 64`.** With a 64-bit
   AXIL master and 64-bit timestamps, every field is exactly one
   beat:
     ```
     beat 0:  packet[63:0]
     beat 1:  packet[127:64]
     beat 2:  source_ts[63:0]   (if cfg_ts_append_mode = 01 or 11)
     beat 3:  arrival_ts[63:0]  (if cfg_ts_append_mode = 10 or 11)
     ```
   No padding, no half-beats, address generator is just `addr += 8`
   per beat. Choosing 32-bit TS would have given mode 01 a 20-byte
   record on a 64-bit master — a half-beat misalignment requiring
   either padding (waste) or falling back to 32-bit master (4 beats
   for the packet alone). Locked 64-bit TS avoids the whole class.

4. **Reserved-field carve-out** (informational, not required for
   this migration). The packet's 15-bit `[123:109]` reserved field
   doesn't currently carry any timing info. If a future PR wants a
   short-window **sequence number** inside the packet for ordering
   verification (so dropped-beat corruption is detectable from the
   data alone), that's where it'd live — 12 bits gives 4096-event
   wrap, enough to spot a single missing event in a typical burst.

### 4.5 — Subsystem reporters (stream, rapids)

| File | Change |
| ---- | ------ |
| `projects/components/stream/rtl/fub/descriptor_engine.sv` | Any `monbus_packet` output / internal nets. |
| `projects/components/stream/rtl/fub/scheduler.sv` | Same. |
| `projects/components/stream/rtl/macro/scheduler_group_array.sv` | Same. |
| `projects/components/rapids/rtl/macro/scheduler_group.sv` | Same. |
| `projects/components/rapids/rtl/macro/scheduler_group_array.sv` | Same. |
| `projects/components/rapids/rtl/macro_beats/scheduler_group_beats.sv` | Same. |
| `projects/components/rapids/rtl/macro_beats/scheduler_group_array_beats.sv` | Same. |

### 4.6 — Bridge generator (Python)

Two classes of change: (1) bump every hardcoded `[63:0]` monbus signal
to `[127:0]`; (2) plumb the new source-time side-band so every
wrapper's `i_mon_time` input ties to the group's `mon_time_out` and
every wrapper's `monbus_timestamp` output feeds the arbiter.

| File | Sites |
| ---- | ----- |
| `projects/components/bridge/bin/bridge_pkg/components/bridge_module_generator.py` | (1) `_generate_monitor_internal_signals`: bump `[63:0] monbus_packet` → `[127:0]` (or use `monitor_packet_t` if the file imports the package) and add the per-wrapper `monbus_timestamp_t monbus_timestamp_<port>_<idx>_<chan>` nets + the shared `monbus_timestamp_t mon_time_w` net. No top-level parameter needed — widths come from the package. (2) `_generate_monitor_aggregator`: extend the arbiter unpacked-array set to include the timestamp side-band, wire `mon_time_w` to the group's `mon_time_out`, wire the group's `monbus_timestamp` input to the arbiter output. |
| `projects/components/bridge/bin/bridge_pkg/components/axi4_timing_wrapper_component.py` | `connect_monbus` — emit the connections for `monbus_packet[127:0]`, the new `i_mon_time(mon_time_w)`, and `monbus_timestamp(<per-wrapper net>)`. |
| `projects/components/bridge/bin/bridge_pkg/components/slave_adapter_instance_component.py` | Same — slave-adapter instantiation gets the same three new connections. |
| `projects/components/bridge/bin/bridge_pkg/generators/adapter_generator.py` | `_generate_monitor_ports`: declare the new `input monbus_timestamp_t i_mon_time` and `output monbus_timestamp_t monbus_<chan>_timestamp` in the adapter module's port list. The adapter's interior already-existing `Axi4TimingWrapper.connect_*` calls need extension to pipe these through. |
| `projects/components/bridge/bin/bridge_pkg/generators/slave_adapter_generator.py` | Same. |

After updating the Python, **regenerate all bridges** (`python3
bridge_generator.py --bulk bridge_batch.csv`) and verify the generated
SV uses the new width and the new ports.

### 4.7 — Bridge dv-side smoke wrapper

| File | Change |
| ---- | ------ |
| `projects/components/bridge/dv/tests/bridge_1x2_rd_mon_smoke.sv` | None directly — it ties off the bridge's AXIL master with `m_mon_axil_*` signals which are still 32/64-bit. **But:** if §4.4 bumps `m_mon_axil_master` to 64-bit data, update the smoke wrapper's `m_mon_axil_wdata` port width from 32 to 64 (and `wstrb` 4→8). |

### 4.8 — Python parser library

| File | Change |
| ---- | ------ |
| `bin/TBClasses/monbus/monbus_types.py` | Update bit slices in every `get_*` / `create_monitor_packet`. Re-run the auto-extractor against the widened SV typedef enums (event_code values are unchanged numerically — only the SV type width changed — so the Python IntEnums themselves don't need edits). |
| `bin/TBClasses/monbus/monbus_packet.py` | `create_monbus_field_config()`: bump `event_code` field 4→8, `protocol` 3→4, `channel_id` 6→9, `unit_id` 4→8, `agent_id` 8→16, add `timestamp_lo` 8, add `reserved` 7, `data` 35→64. |
| `bin/TBClasses/monbus/__init__.py` | Replace `raw_packet & ((1 << 64) - 1)` with `& ((1 << 128) - 1)`. Add `MONBUS_PKT_WIDTH = 128` constant. |
| `bin/TBClasses/monbus/tests/test_monbus_parser.py` | Update `test_field_widths_match_sv_packet_layout` and `test_event_data_is_35_bits_not_36` (rename to `_is_64_bits_now`). Update edge-case values to the new field widths. |

### 4.9 — Other monbus consumers

```
bin/TBClasses/monbus/monbus_event_factories.py
bin/TBClasses/monbus/monbus_slave.py
bin/TBClasses/monbus/monbus_validators.py
bin/TBClasses/axil4/monitor/axil4_master_monitor_tb.py
bin/TBClasses/axil4/monitor/axil4_slave_monitor_tb.py
bin/TBClasses/amba/arbiter_monbus/   (basic / corner_case / error / performance / stress / threshold / monitor_config / test_framework)
```

Audit each for hard-coded 64-bit assumptions (packet construction, field
masks, comparison vectors). The factories under `monbus_event_factories.py`
build synthetic packets via `create_monitor_packet(...)` — once that
function is updated they just work, but check for any inline bit-shifting
that bypasses it.

### 4.10 — Formal harnesses (16 files)

```
formal/amba/axi_monitor_reporter/        (both .sv + _flat.v)
formal/amba/axi_monitor_filtered/        (same)
formal/amba/axi_monitor_base/            (same)
formal/amba/axi_monitor_addr_check/      (same)
formal/amba/axi4_master_rd_mon/          (same)
formal/amba/axi4_master_wr_mon/          (same)
formal/amba/axi4_slave_rd_mon/           (same)
formal/amba/axi4_slave_wr_mon/           (same)
formal/amba/arbiter_monbus_common/       (same)
formal/amba/arbiter_rr_pwm_monbus/       (same)
```

The `_flat.v` files are flattened SV outputs — regenerate them via the
existing formal flow rather than hand-editing. The hand-written
`formal_*.sv` harnesses need their `monbus_packet` widths bumped.

The P6/P7 assertions added in `f5286023` test `*_ready = w_core_*_ready &
w_block_ready` — width-agnostic, no change needed. The
`axi_monitor_addr_check` formal harness needs the same field-slice update
as the module itself.

---

## 5 — Generated-file regeneration order

This matters because some generated files depend on others. Follow this
order or you'll fight cascading errors:

1. Update SV packages (§4.1) — packages compile first in every filelist.
2. Update SV monitor cores (§4.2).
3. Update SV wrapper variants (§4.3).
4. Update SV consumers (§4.4, §4.5).
5. Update bridge generator Python (§4.6).
6. **Regenerate all bridges:**
   ```
   cd projects/components/bridge/bin
   python3 bridge_generator.py --bulk bridge_batch.csv
   ```
   Confirm the new SV uses `[127:0]` / `MONBUS_PKT_WIDTH` consistently.
7. Update Python parser (§4.8).
8. Update other Python consumers (§4.9).
9. Update formal harnesses (§4.10).
10. Regenerate `_flat.v` formal files via existing formal flow.

---

## 6 — Acceptance / regression

Run in this order; do NOT proceed past a failure:

1. **Python parser unit tests:**
   ```
   PYTHONPATH=bin pytest bin/TBClasses/monbus/tests/test_monbus_parser.py -v
   ```
   Expect 18/18 (or higher, after field-width tests adapt).

2. **Bridge regression** (proves the bridge generator changes lint+sim):
   ```
   cd projects/components/bridge/dv/tests
   pytest -n 8 -q
   ```
   Expect 26/26.

3. **Lint sweep** — every batch bridge with `variants = ["no", "mon"]`:
   ```
   for fl in projects/components/bridge/rtl/filelists/bridge_*.f; do
     verilator --lint-only -Wno-fatal -Wno-UNUSED -Wno-DECLFILENAME \
       -Wno-PINMISSING -Wno-WIDTH -Wno-CASEINCOMPLETE \
       -f "$fl" --top-module "$(basename "$fl" .f)" \
       -I rtl/amba/includes
   done
   ```
   Expect 0 errors across all 11 (or 12 with `bridge_1x2_rd_mon`).

4. **Formal sanity** — re-run any formal proofs that were green before the
   sweep; they should all be green after. Specifically:
   - `axi_monitor_base` properties
   - P6/P7 in the wrapper formal harnesses
   - `axi_monitor_addr_check` properties (these will exercise the new
     field allocation directly)

5. **Stream / RAPIDS regression** — these subsystems consume the packet
   format. Run their existing tests; expect no new failures.

---

## 7 — Things to NOT do

1. **Don't make `PACKET_WIDTH` a runtime parameter.** Two formats in flight
   means every consumer handles both, including the Python parser, the
   formal harnesses, and the AXIL group's address logic. Pick 128, sweep.

2. **Don't stage this over multiple PRs.** Even apparently-independent
   sub-modules share the packet format via package imports — a half-updated
   tree compiles fine but produces silent wrong-decode bugs that look like
   data-corruption regressions in unrelated tests.

3. **Don't extend `event_data` past 64 bits in this transition.** Keep the
   metadata fields (timestamp, ID widening) carved out. If you fold every
   spare bit into `event_data` "for future use," you've just kicked the
   field-allocation discussion down the road to whoever needs it next.

4. **Don't pre-emptively update `_flat.v` formal files by hand.** They're
   regenerated by the formal toolchain — hand edits get clobbered.

---

## 8 — Open questions before kickoff

1. **~~`TS_WIDTH` parameter~~** — **RESOLVED.** Width is locked at 64 bits
   via `monbus_timestamp_t` in `monitor_common_pkg.sv` (see §3). Same
   single-source-of-truth discipline as `MONBUS_PKT_WIDTH`. The choice
   was 32 vs 64 (other widths waste bits or break AXIL beat alignment
   on a 64-bit master); 64 wins on (a) non-wrapping at any realistic
   capture window, (b) clean beat alignment in
   `monbus_axil_group`, (c) zero per-instance parameter plumbing.

2. **Drop `is_read` from `axi_monitor_addr_check`?**
   - **AXI variants:** YES, drop it. The `IS_READ` module parameter on
     each consumer wrapper already encodes the direction (master_rd_mon
     vs master_wr_mon are different modules), so the on-wire bit is
     redundant. Recovers 1 bit; raise `range_index` to 6 bits (64 ranges).
   - **APB variant:** KEEP the bit. `apb_monitor.sv` and `apb5_monitor.sv`
     handle both directions in a single module via `cmd_pwrite`; the
     `is_read` flag is the only on-wire indicator of direction for
     APB events. Per-protocol field allocation in `apb_monitor_addr_check`
     stays as-is.

3. **`gaxi_fifo_sync` depth assumptions:** Are any FIFO depths or skid
   depths sized in terms of `(64 / DATA_WIDTH) * something`? Audit
   `monbus_axil_group` for assumptions about 64-bit packet width when
   sizing the err / write FIFOs. Also the timestamp-append latch column
   doubles the per-entry storage in the write FIFO when enabled — decide
   if that gets a separate (smaller) FIFO or rides on the main one.

4. **APB monbus path:** `rtl/amba/apb/apb_monitor.sv` reports via the same
   packet format. Confirm with the APB owner that bumping width doesn't
   collide with any in-flight APB-specific work.

5. **Reserved-field semantics:** the 15-bit reserved field at [123:109].
   Producers MUST drive it to all-zero. Consumers MUST ignore on read.
   Future allocations come out of reserved without breaking
   forward-compat — but only if everyone honours the contract.

6. **Source vs. arrival timestamp default mode:**
   **DECIDED: `2'b11` (both).** Rationale: marginal cost is 8 bytes
   per record (one extra beat at the 64-bit master), and it gives
   wrapper→group latency observability for free. Anyone tight on
   capture-buffer space can lower `cfg_ts_append_mode` at runtime
   to `01` (source-only) or `00` (no timestamps).

7. **`mon_time_w` distribution skew:** the broadcast `mon_time_w`
   net in the bridge / stream / rapids top has meaningful fanout
   (every monitor wrapper sees it).
   **DECIDED: insert a 1-cycle pipeline register per FUB cluster**
   at the consumer end of `mon_time_w` to break the fanout cone.
   Accepted consequence: timestamps from wrappers in different
   clusters can differ by ±1 cycle on the same logical event. That
   skew is below the wrapper-to-group latency anyway, so consumers
   that care about cross-wrapper ordering already need a tolerance
   ≥ 1 cycle. If any wrapper sits across a CDC boundary, the
   broadcast must additionally be re-synchronised on the destination
   clock domain — today the bridge is single-domain; flag for the
   day cross-clock monitors land.

---

## 9 — Estimated effort

- SV sweep + regen: ~half a day if the agent already has the SV-emitter
  scripts they used to add `_mon` variants. Half a day if not.
- Python parser sweep + tests: ~2 hours.
- Formal harness updates + reproof: 2-4 hours depending on tool turnaround.
- Bridge generator update + regen + regression: ~1 hour (the change is
  localized; regression takes 33 s).

**Total: 1-2 days of focused work for one agent.** No more — if it
sprawls beyond that, something in the plan is wrong; stop and re-scope.

---

## 10 — Sign-off checklist (don't merge until)

- [ ] All four package files updated (§4.1).
- [ ] All monitor cores, addr_check, arbiter, monbus_axil_group updated (§4.2, §4.4).
- [ ] All 32 wrapper variants updated (§4.3).
- [ ] All subsystem reporters updated (§4.5).
- [ ] Bridge generator regenerates byte-identical no-monitor RTL when
      `variants = ["no"]`, and 128-bit-clean monitored RTL when
      `variants = ["no", "mon"]`.
- [ ] Python parser tests: ≥ 18 PASS.
- [ ] Bridge regression: 26 PASS.
- [ ] Verilator lint: 0 errors across all batch bridges (mon + no-mon).
- [ ] Pre-existing formal proofs: re-prove green.
- [ ] Stream regression: no new failures vs main.
- [ ] RAPIDS regression: no new failures vs main.
- [ ] No surviving hardcoded `[63:0]` for monbus signals (`git grep '\[63:0\].*monbus'` returns 0 hits outside legitimate non-monbus 64-bit uses).
- [ ] **Bit-position discipline assertion** added to the Python parser
      test suite: `assert MONBUS_PKT_WIDTH == 4 + 15 + 4 + 8 + 9 + 16 + 8 + 64`.
      A follow-up field reallocation that drops one of the constituent
      widths without updating the others fails this assertion before
      anything else miscoders.
- [ ] **Event-code widening search-and-destroy:** `grep -rn 'event_code\['
      rtl/ bin/` returns no hits assuming 4-bit width. Any `[3:0]` slice
      on event_code must be widened or removed.

---

*Documentation and implementation support by Claude.*
