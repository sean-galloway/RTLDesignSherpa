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

# axi_monitor_addr_check

**Module:** `axi_monitor_addr_check.sv`
**Location:** `rtl/amba/monitor/`
**Category:** Core Infrastructure
**Status:** Production Ready (Formally Verified)

---

## Overview

`axi_monitor_addr_check` is a parallel address-range comparator instantiated
within AXI monitor wrappers. It observes command-phase handshakes (AR/AW) and
classifies each accepted address against N user-configured inclusive ranges
`[low, high]`. Each range carries a **flavor** (`ADDR_RANGE_IS_ERROR[i]`) that
selects one of two independent report paths:

- **DEBUG range** (`ADDR_RANGE_IS_ERROR[i] = 0`): a hit emits a `PktTypeAddrMatch` (`4'h8`) packet with event code `AXI_ADDR_RANGE_MATCH = 8'h01`, gated by `cfg_debug_enable`.
- **ERROR range** (`ADDR_RANGE_IS_ERROR[i] = 1`): the enabled ERROR ranges form an **allowlist**; a command whose address is in NONE of them emits a `PktTypeError` (`4'h0`) packet with event code `AXI_ERR_ADDR_RANGE = 8'h0D`, gated by `cfg_error_enable`.

DEBUG and ERROR ranges are evaluated independently, so a single command may
produce both a match and a miss; two pending slots hold each and the output
stream serialises them.

This is a **shared infrastructure module** used internally by AXI4/AXIL4/AXI5
monitor wrappers when parameterized with `N_ADDR_RANGES > 0`. It is not
typically instantiated directly by users but is critical for address-space
validation (allowlist enforcement) and targeted debug tracing. In practice it
buys you four things:

1. **Allowlist enforcement:** ERROR ranges declare the *expected* address space; any access outside it raises an Error/ADDR_RANGE packet.
2. **Targeted debug tracing:** DEBUG ranges watch specific regions; a hit emits an AddrMatch packet without implying an error.
3. **Independent debug/error regions:** the two flavors can cover different address sets, so "watch this region" and "everything must stay inside that region" are configured separately.
4. **Design Verification:** verify address constraints in functional simulation and formal proof.

The ERROR/allowlist path is the checker built into the monitor whenever `N_ADDR_RANGES > 0`, **independent of the error reporter cone** (`ENABLE_ERROR_LOGIC`). It is therefore the most controllable way to **deliberately inject an error** for coverage: point an enabled ERROR range at a region the legitimate traffic never touches, and every access becomes an allowlist miss that emits `PktTypeError`/`AXI_ERR_ADDR_RANGE`. Because an error is a fault condition, this injection is expected to hang the traffic that provoked it -- see [Healthy classes vs fault classes](monitor_system_architecture.md#healthy-classes-vs-fault-classes) for why that stall is the point, not a defect.

Feature summary:

- **Parallel Range Comparators:** N independent [low, high] inclusive range checkers
- **Two flavors per range:** `ADDR_RANGE_IS_ERROR` selects DEBUG (match) vs ERROR (allowlist-miss) behavior per range; default all-0 leaves the ERROR/miss path inert (feature unused by default)
- **Independent path enables:** `cfg_debug_enable` gates AddrMatch packets, `cfg_error_enable` gates Error packets; `cfg_addr_check_enable` is the master gate
- **Zero-Area Synthesis:** `N_ADDR_RANGES = 0` omits this module entirely (no gates, no regs) -- done by the **parent**, not here: `axi_monitor_base` wraps the instance in `if (N_ADDR_RANGES > 0) gen_addr_check` and ties the packet stream off in `gen_no_addr_check`
- **Monbus Integration:** AddrMatch packets (`8'h8`/`8'h01`) and Error packets (`8'h0`/`8'h0D`)
- **Coalescing:** per-range latched address for MATCH; a single latched slot for MISS; one packet per cycle (MISS has emit priority)
- **Formal Verification:** all properties proven (prove + cover PASS)

---

## Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| `N_ADDR_RANGES` | int | 4 | Number of address-range comparators (>= 1). Max 16 (4-bit range index). |
| `ADDR_WIDTH` | int | 32 | Address bus width (matches AXI_ADDR_WIDTH of parent monitor). Must be <= 60 (fits the event_data address field). |
| `ID_WIDTH` | int | 6 | Transaction ID width (clipped to 9 bits when copied into the packet's channel_id). |
| `UNIT_ID` | logic [7:0] | 8'h00 | 8-bit unit identifier in monitor packets. |
| `AGENT_ID` | logic [15:0] | 16'h0000 | 16-bit agent identifier in monitor packets. |
| `IS_READ` | bit | 1 | Build-time flag: 1 if this monitor watches reads (AR), 0 for writes (AW). Drives direction recovery at the consumer (see Event Encoding). |
| `ADDR_RANGE_IS_ERROR` | logic [N_ADDR_RANGES-1:0] | `'0` | Per-range flavor: bit i = 0 → range i is a DEBUG range (hit → AddrMatch); bit i = 1 → range i is an ERROR range (allowlist; miss → Error/ADDR_RANGE). Default all-0 keeps the ERROR/miss path inert. |

---

## Ports

### Clock and Reset

| Port | Direction | Width | Description |
|---|---|---|---|
| `clk` | Input | 1 | AXI clock |
| `aresetn` | Input | 1 | AXI active-low reset |

### Side-Band Timestamp

| Port | Direction | Width | Description |
|---|---|---|---|
| `i_mon_time` | Input | 64 | Free-running counter from `monbus group`, broadcast to every wrapper via the shared `mon_time_w` net. Sampled when `addr_pkt_valid` asserts and driven out on `addr_pkt_timestamp`. |

### Command Interface (Snoop)

| Port | Direction | Width | Description |
|---|---|---|---|
| `cmd_valid` | Input | 1 | Command valid (AR or AW handshake) |
| `cmd_ready` | Input | 1 | Command ready (slave accepting) |
| `cmd_addr` | Input | ADDR_WIDTH | Command address (araddr or awaddr) |
| `cmd_id` | Input | ID_WIDTH | Command transaction ID (arid or awid) |

### Configuration Inputs

| Port | Direction | Width | Description |
|---|---|---|---|
| `cfg_addr_check_enable` | Input | 1 | Master enable for all comparators. 0 = no packets generated. |
| `cfg_debug_enable` | Input | 1 | Enables the MATCH path: DEBUG-range hits emit AddrMatch packets. |
| `cfg_error_enable` | Input | 1 | Enables the MISS path: an address outside the ERROR allowlist emits an Error/ADDR_RANGE packet. |
| `cfg_addr_range_enable[N_ADDR_RANGES-1:0]` | Input | N | Per-range enable bits. 1 = range active, 0 = range disabled. |
| `cfg_addr_range_low[N_ADDR_RANGES-1:0][ADDR_WIDTH-1:0]` | Input | N × ADDR_WIDTH | Inclusive low bound for each range. |
| `cfg_addr_range_high[N_ADDR_RANGES-1:0][ADDR_WIDTH-1:0]` | Input | N × ADDR_WIDTH | Inclusive high bound for each range. |

### Monitor Bus Output

| Port | Direction | Width | Description |
|---|---|---|---|
| `addr_pkt_valid` | Output | 1 | Address-check packet valid (AddrMatch or Error) |
| `addr_pkt_ready` | Input | 1 | Downstream ready to accept packet |
| `addr_pkt_data` | Output | 128 | Monitor packet (`monitor_packet_t`, 128-bit format) |
| `addr_pkt_timestamp` | Output | 64 | Sampled `i_mon_time` paired atomically with `addr_pkt_data` |

---

## Functional Description

### Internal Architecture

The module instantiates N parallel comparators and splits them by flavor:

1. **Per-Range Comparators:** Each range i computes `raw_hit[i] = cfg_addr_range_enable[i] && (cmd_addr >= cfg_addr_range_low[i]) && (cmd_addr <= cfg_addr_range_high[i])`.

2. **Flavor split:**
   - `debug_hit[i] = raw_hit[i] && !ADDR_RANGE_IS_ERROR[i]` — a hit in a DEBUG range.
   - `err_hit = |(raw_hit & ADDR_RANGE_IS_ERROR)` — the address is inside some enabled ERROR range (allowed).
   - `err_ranges_exist = |(cfg_addr_range_enable & ADDR_RANGE_IS_ERROR)`.

3. **Per-command events** (qualified by `cmd_fire = cmd_valid && cmd_ready && cfg_addr_check_enable`):
   - `match_set[i] = cmd_fire && cfg_debug_enable && debug_hit[i]` → MATCH (AddrMatch packet).
   - `miss_set = cmd_fire && cfg_error_enable && err_ranges_exist && !err_hit` → MISS (Error packet).

4. **Pending + emit:** MATCH events coalesce per DEBUG range (`r_match_pending[i]`, latched address, latest-win); MISS events coalesce into a single slot (`r_miss_pending`). One packet drains per cycle — **MISS has priority**, then the lowest-index pending DEBUG range. Direction (read vs. write) is not embedded — the build-time `IS_READ` parameter fixes the channel, and consumers recover direction from `(UNIT_ID, AGENT_ID)`.

Because the two flavors are independent, a command that hits a DEBUG range and is also outside the ERROR allowlist sets BOTH pending slots; the two packets emit on successive cycles.

### Event Encoding

Two packet types share the 128-bit `monitor_packet_t` layout; only
`packet_type`, `event_code`, and the range-index nibble differ:

| Field | MATCH (debug hit) | MISS (error allowlist) |
|---|---|---|
| `[127:124]` Packet Type | `4'h8` PktTypeAddrMatch | `4'h0` PktTypeError |
| `[108:105]` Protocol | `4'h0` PROTOCOL_AXI | `4'h0` PROTOCOL_AXI |
| `[104:97]` Event Code | `8'h01` AXI_ADDR_RANGE_MATCH | `8'h0D` AXI_ERR_ADDR_RANGE |
| `[96:88]` Channel ID | `cmd_id` clipped/zero-extended to 9 bits | same |
| `[87:72]` Agent ID | from `AGENT_ID` | from `AGENT_ID` |
| `[71:64]` Unit ID | from `UNIT_ID` | from `UNIT_ID` |
| `[63:60]` Range Index | matching DEBUG range (0..N-1) | `4'hF` (no-range sentinel) |
| `[59:0]` Address | full `cmd_addr`, zero-padded | full `cmd_addr`, zero-padded |

**`is_read` flag dropped:** Earlier revisions reserved a bit in event_data for
read-vs-write direction. The 128-bit layout drops it because each AXI monitor
instance watches a single direction (set at build time by `IS_READ`); consumers
recover direction from `(UNIT_ID, AGENT_ID)`. Note: `apb_monitor_addr_check`
still carries `is_read` since a single APB monitor sees both directions on the
same channel.

**Side-band timestamp:** `addr_pkt_timestamp` carries the sampled `i_mon_time`
paired atomically with the packet through the arbiter and into
`monbus group`.

---

## Usage Example

### Example 1: Error allowlist (out-of-range → Error packet)

Declare `0x1000_0000..0x1FFF_FFFF` as the only legal region; any access outside
it raises an Error/ADDR_RANGE packet:

```systemverilog
axi4_master_wr_mon #(
    .N_ADDR_RANGES(1),
    .ADDR_RANGE_IS_ERROR(1'b1),   // range 0 is an ERROR (allowlist) range
    .AXI_ADDR_WIDTH(32)
) u_wr_mon (
    .cfg_addr_check_enable(1'b1),
    .cfg_error_enable(1'b1),      // enable the MISS path
    .cfg_addr_range_enable(1'b1),
    .cfg_addr_range_low(32'h1000_0000),
    .cfg_addr_range_high(32'h1FFF_FFFF)
    // ...
);
```

### Example 2: Mixed debug + error ranges

Range 0 traces a debug region (AddrMatch on hit); range 1 is the error
allowlist (Error on miss). `ADDR_RANGE_IS_ERROR = 2'b10`:

```systemverilog
axi4_master_rd_mon #(
    .N_ADDR_RANGES(2),
    .ADDR_RANGE_IS_ERROR(2'b10),  // range1 = ERROR, range0 = DEBUG
    .AXI_ADDR_WIDTH(32)
) u_rd_mon (
    .cfg_addr_check_enable(1'b1),
    .cfg_debug_enable(1'b1),      // MATCH path (range0)
    .cfg_error_enable(1'b1),      // MISS  path (range1 allowlist)
    .cfg_addr_range_enable(2'b11),
    .cfg_addr_range_low ({32'h1000_0000, 32'h0800_0000}),  // {r1, r0}
    .cfg_addr_range_high({32'h1FFF_FFFF, 32'h08FF_FFFF})
    // ...
);
```

### Example 3: Exact-Match Detector

Detect accesses to a single debug address:

```systemverilog
.cfg_addr_range_low(32'hDEAD_BEEF),
.cfg_addr_range_high(32'hDEAD_BEEF)   // low == high => exact match only
```

---

## Design Notes

### Filtering Integration

The checker produces two packet classes, each filtered by the parent monitor's
existing drop masks (`axi_monitor_filtered` / `monbus_group_core`):

- **MATCH** (`PktTypeAddrMatch`, event `0x01`) — dropped by `cfg_axi_addr_mask[1]`.
- **MISS** (`PktTypeError`, event `0x0D` `AXI_ERR_ADDR_RANGE`) — dropped by `cfg_axi_error_mask[13]`.

No new mask wiring is needed — both event codes already have reserved bits in the
per-class 16-bit masks.

**Example:** suppress the error/allowlist packets while keeping debug matches:
```systemverilog
.cfg_axi_error_mask(16'h2000)  // bit 13 high = drop ADDR_RANGE error packets
```

### Instantiation Pattern

The module is instantiated **inside** AXI monitor wrappers (`axi4_master_wr_mon`, etc.) by the monitor architecture. Users do not instantiate this module directly but configure it via wrapper parameters.

### Synthesis Behavior

- **`N_ADDR_RANGES = 0`:** handled by the **instantiating parent**. `axi_monitor_base`
  generates the instance only under `N_ADDR_RANGES > 0`; its `gen_no_addr_check` branch
  drives `addr_pkt_valid = 0` and a zeroed packet, so from the monitor's arbiter the
  stream is constant 0 and the checker costs nothing.

  This module itself has **no `N == 0` guard** and must not be instantiated directly with
  0 -- its parameter is documented `>= 1`. At 0 the per-range vectors degenerate
  (`logic [-1:0]`), the range loops are empty so the enable terms are never driven, and
  `addr_pkt_valid` would be undriven (X in simulation) rather than a clean constant 0.
- **`N_ADDR_RANGES > 0`:** Full comparator logic synthesized. Area scales with N.

### Downstream FIFO

The monbus output should be fed into a standard FIFO (e.g., `gaxi_fifo_sync`) to prevent backpressure stalls:

In practice the addr_check output is merged with the reporter's main packet
stream by an arbiter (`monbus_arbiter`) that carries packet+timestamp atomically
through a 192-bit skid. The arbiter's downstream FIFO sits at the
`monbus group` boundary, sized for the aggregate of all per-wrapper
streams. A standalone FIFO on the addr_check output is normally not needed.

---

## Related Modules

- **[axi_monitor_base](./axi_monitor_base.md)** — Core monitor infrastructure that instantiates this module
- **[axi_monitor_filtered](./axi_monitor_filtered.md)** — 3-level packet filtering (sibling to addr_check)
- **[axi4_master_wr_mon](../axi4/axi4_master_wr_mon.md)** — Wrapper that uses this module (N_ADDR_RANGES parameter)

---

## Testing

All properties proven via formal verification (see `formal/amba/axi_monitor_addr_check/formal_axi_monitor_addr_check.sv`):

| Property | Description | Status |
|---|---|---|
| **P1: Reset quiet** | After reset, `addr_pkt_valid` is deasserted. | PASS |
| **P2: Master gate** | When `cfg_addr_check_enable=0`, `addr_pkt_valid` stays low. | PASS |
| **P3: Packet class** | An emitted packet is PROTOCOL_AXI and is either MATCH (AddrMatch/`0x01`) or MISS (Error/`0x0D`) — nothing else. | PASS |
| **P4: MATCH validity** | A MATCH packet's range_index points to an enabled **DEBUG** range (`ADDR_RANGE_IS_ERROR=0`) and the address lies within its `[low, high]`. | PASS |
| **P5: MISS validity** | A MISS packet carries the `0xF` sentinel, at least one ERROR range is enabled, and the address lies in **no** enabled ERROR range. | PASS |
| **P6: Sticky valid** | Once `addr_pkt_valid` asserts it stays asserted until the consumer accepts. | PASS |
| **cover** | Both emission and the emit+handshake are reachable (non-vacuous). | PASS |

---

## References

- **Monitor Architecture:** `docs/markdown/rtl-amba/overview.md`
- **Monitor Configuration Guide:** [Monitor Base Configuration](./axi_monitor_base.md)
- **Packet Format Specification:** `docs/markdown/rtl-amba/includes/monitor_package_spec.md`
- **Formal Verification:** `formal/amba/axi_monitor_addr_check/`

---

## Navigation

- **[← Back to Shared Infrastructure Index](../_book_monitor_index.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
