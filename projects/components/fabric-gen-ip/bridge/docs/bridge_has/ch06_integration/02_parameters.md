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

# Parameter Configuration

## Overview

Every bridge the generator emits starts here: port counts, bus widths, per-port configuration, and the address map. This chapter collects the full parameter set — the core knobs, the widths the generator derives from them, the per-port fields, the monitor options, and the checks the generator runs before it accepts your configuration.

## Parameters

### Core Parameters

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| NUM_MASTERS | int | 1-32 | 2 | Number of master ports |
| NUM_SLAVES | int | 1-256 | 2 | Number of slave ports |
| ADDR_WIDTH | int | 12-64 | 32 | Address bus width |
| DATA_WIDTH | int | 32-512 | 64 | Data bus width |
| ID_WIDTH | int | 1-16 | 4 | Master ID width |
| USER_WIDTH | int | 1-16 | 1 | User signal width |

: Bridge Core Parameters

### Registered Crossbar (`xbar_pipeline`)

| TOML key (`[bridge]`) | Type | Default | Effect |
|---|---|---|---|
| `xbar_pipeline` | bool | `false` | `true` puts a 2-deep skid stage on every slave-side channel (AW, W, AR, B, R) inside the crossbar. Propagation 3/3 cycles instead of 2/2 (Table 5.7), throughput unchanged. For high-fanout or wide fabrics that miss timing on the arbiter-plus-mux or the response OR-merge cone. Measured (HAS 6.4): +0.57 ns against about 0 on the plain 2x2 at 100 MHz on the Artix-7. It registers the slave-side response paths, which is where the larger width-converting fixtures still miss. |
| `r_queue_depth` | int, 0 or 2..64 | `0` | Read response queues (bridge TASK-021): with a depth, every slave that two or more masters read gets one `gaxi_fifo_sync` of that many R beats per reading master inside the crossbar, written by the slave's R keyed on the returned bridge id and drained by the master's response arbiter. A slave returns R in its own order; without the queue, when the master its head beat is for cannot take it (its R port is carrying the other slave's burst) the slave stalls, and the master its next beats are for sits idle: head-of-line blocking at the slave's output, which uniform traffic past saturation shows (HAS 5.1: 0.67 of capacity at 2x offered on `bridge_2x2_rw`, 1.00 at every load point with 8 beats; on `bridge_4x4_rw` it changes nothing, that fabric's loss being another stage -- bridge TASK-022). Below saturation nothing changes but one cycle of R latency (the FIFO's mux read). Set it at least one slave-side burst deep so a whole burst hands over before the slave waits. The default is 0, the minimal fabric: the cost is M x N x depth R beats of flops -- on ASAP7 the 2x2 crossbar's flops go from 1,883 to 3,235 at 8 beats (HAS 5.3). Not on a CDC lane (its own FIFO already decouples it) nor on the internal catch-all slave. Reported in `<bridge>_sizing.json`. |
| `preset` | `"xbar"` | none | Bridge-wide defaults in one key. `"xbar"` is the plain crossbar: `latency = "cut_none"` on every same-clock AXI4/AXI5 port (a converted or CDC port keeps its buffers), `rate_buffer = 0`, `id_remap = false`. Each is only a default; the same key on `[bridge]` or on a port wins. Measured on `bridge_2x2_rw_xbar` by `test_bridge_2x2_rw_xbar_preset`: 0 cycles master to slave on AW, B, AR and R for every pair, 9-bit `{index, ID}` at the slaves from 8-bit masters. Fewer stages also means a shorter clock-to-clock path through the fabric, so check timing at your clock. |
| `id_remap` | bool | `true` | `false` turns off the transaction-ID remap (bridge TASK-018) for every master; a `[[bridge.masters]]` entry may set it for itself. The master's own ID then travels whole and the fabric and slave IDs are `{master index, ID}` -- wider, so each slave's `id_width` must grow to match (the validator names the width). Same-ID order is kept by the per-ID target table (`id_track_bits`) instead of the remap table. |
| `arbitration` | `"rr"` / `"qos"` / `"matrix"` | `"rr"` | Per-slave arbitration policy. `"qos"` grants the highest `AxQOS` plus aging (MAS 2.4); it decides among requests pending at the arbiter, so it shows at a slave that backpressures AW, not at one that accepts every AW on arrival; equals share round-robin. `"matrix"` is the least-recently-served matrix arbiter (MAS 2.4, bridge TASK-015): one priority bit per master pair, a two-level pick, the same `n-1` wait bound as round-robin; on ASAP7 it shortens a 4x4 crossbar's worst path by 5-11 percent for about 2 percent more cells and is a wash at 2x2 (HAS 5.3). |
| `qos_aging_shift` | int 0..7 | 4 | With `"qos"`: a waiting request gains one priority level every `2**shift` cycles, so the worst wait for a QoS-0 request is `15 * 2**shift` cycles. |
| `id_track_bits` | int 0..8 | 4 | Per-ID target tracking in a master adapter that keeps its port's ID (one no wider than `$clog2(max_outstanding)`, or a read-return-atomic port; a wider one is remapped to slots and tracked by its remap table, which matches whole IDs): `2**id_track_bits` entries indexed by the ID's low bits (never more bits than the port's ID). A request waits only when its ID is in flight to a different slave; IDs sharing the index bits are treated as one ID, which is safe and at worst stalls needlessly. 0 orders every ID as one. Every port, read-return-atomic and trace-echo ports included (GitHub #119 L1b). |
| `max_outstanding` | int, power of two 2..64 | the sizing rule (bridge TASK-016) | Outstanding limit per direction for every port that does not set its own; given here it PINS every port. Left out everywhere, each port gets the smallest power of two >= `1 + latency_cycles + round trip` over its connected paths (the rule, HAS 5.1 "Buffer Sizing Rule"; the fabric round trip is modelled per path, 7-13 cycles), floored at `2**id_width` for a master that keeps its ID so the derivation never switches ID remapping on. The generator prints each port's depth with the rule's minimum beside it and writes `<bridge>_sizing.json` next to the RTL; a pinned value under the minimum is a WARNING, never an error. A master holds at most this many AWs and ARs in flight, and a master whose ID is wider than `$clog2` of it is remapped to slots of that width (bridge TASK-018), which sets the fabric ID width; a slave tracks at most this many (its by-ID counter or in-order FIFO), and its AWREADY/ARREADY drop when full. Fixes the fixed 16 (GitHub #119 L5); measured exactly by `test_bridge_2x2_rw_depth_limits`. |

: Crossbar options (bridge TASK-006, was BRIDGE-017)

| TOML key (`[[bridge.slaves]]`) | Type | Default | Effect |
|---|---|---|---|
| `cdc` | bool | `false` | `true` gives this AXI4 slave port its own clock: `<name>_aclk` / `<name>_aresetn` on the top. Several masters: per-master lanes, crossed and arbitrated on that clock (`bridge_cdc_slave_arb`, bridge W9); one master: `axi4_cdc_{wr,rd}` between the adapter's timing wrapper and the port (HAS 4.5a). The same key on a `[[bridge.masters]]` entry does the same for a master port, with the crossing ahead of its wrapper (GitHub #119 L2). `protocol = "axi4"` only. |
| `latency` | `"cut_all"` / `"cut_ax"` / `"cut_none"` | `"cut_all"` | Which channels of this port's timing wrapper are registered (masters take the same key). `cut_ax` keeps AW/AR, `cut_none` makes the port boundary wires: 0 cycles. Same-clock axi4/axi5 ports only. GitHub #119 L7; `test_bridge_2x2_rw_lat_modes` measures every pair. |
| `timeout_cycles` | int, 0 or >= 2 | 0 | > 0 puts `axi4_slave_watchdog` in front of this AXI4 slave: after that many cycles of silence with work outstanding it answers everything with DECERR, and the top gains a sticky `<name>_timeout` (HAS "Slave Watchdog", GitHub #119 L3). 0 = no watchdog. |
| `max_outstanding` | int, power of two 2..64 | `[bridge].max_outstanding`, else the sizing rule | This slave's response-tracker depth (by-ID counter or in-order FIFO), and so its outstanding limit; it also sizes the W-owner FIFO at this port. The same key on a `[[bridge.masters]]` entry sets that master adapter's limit, its W-destination FIFO and its remap table. Derived, it is `pow2(1 + latency_cycles + round trip)`; a derived value above 16 on a remapped master widens the remap slot (`$clog2(max_outstanding)`) and so the fabric ID -- the validator then asks for the wider slave `id_width`. |
| `latency_cycles` | int 0..4096 | 0 | Slaves only (bridge TASK-016): this slave's own response latency, request handshake to first response beat, as the sizing rule's third term. 0 is a slave that answers the cycle after it accepts. A DRAM controller is tens to hundreds: set it (or pin `max_outstanding` on the ports that reach it), or single-beat traffic there runs at `max_outstanding / (1 + latency + round trip)` of the port's peak. `bridge_2x2_rw_slow` declares 16 and derives 32 where `bridge_2x2_rw` derives 16. |
| `max_burst_beats` | int 1..256 | 16 | Masters only (bridge TASK-016): the longest write burst this master issues. Sizes `rate_buffer` to hold one such burst whole. |
| `rate_buffer` | 0 (off) or 2..256 wide beats | the sizing rule | Masters only (bridge W2): the rate-matching buffer on each of this master's upsized paths into a slave another master shares. Derived, it is `pow2(max_burst_beats / width ratio)` on the master's widest such path (8 wide beats for 16-beat bursts into a 2:1 slave), 0 where it has no such path; `[bridge].rate_buffer` pins every master. A burst longer than the buffer passes at the narrow rate. |

: Per-port options: CDC (bridge TASK-006, GitHub #119 L2), latency, outstanding limit

| TOML key (`[bridge]`) | Type | Default | Effect |
|---|---|---|---|
| `mon_preset` | `"lite"` (also accepted: `"error_only"` / `"functional"` / `"all"` / `"none"`) | `"lite"` | Accepted for compatibility; since 2026-09-26 every monitored port builds `axi_monitor_lite` through the `*_monlite` wrapper (error, timeout, completion and active-count threshold packets, same monbus, about a fifth of the full monitor's LUTs), so the cone presets no longer select hardware. Which packets a port emits is the runtime `cfg_*_enable` pins. To remove a monitor use `use_monitor = false` on the port or `use_no_monitors = true` on the bridge. `mon_add` / `mon_remove` are validated and ignored. |

: Monitor preset

### Derived Parameters

The generator works these out from the core set — you never write them yourself:

| Parameter | Formula | Example |
|-----------|---------|---------|
| BRIDGE_ID_WIDTH | clog2(NUM_MASTERS), minimum 1 | 4 masters = 2 bits |
| MASTER_ID_WIDTH | widest master-local ID: `clog2(max_outstanding)` for a remapped master, else its `id_width` | 8-bit IDs, 16 outstanding = 4 |
| ID_PREFIX_WIDTH | clog2(NUM_MASTERS), 0 for one master | 4 masters = 2 bits |
| XBAR_ID_WIDTH | MASTER_ID_WIDTH + ID_PREFIX_WIDTH | 4 + 2 = 6 bits |
| STRB_WIDTH | DATA_WIDTH / 8 | 64b = 8 strobes |

: Derived Parameters

> `BRIDGE_ID_WIDTH` sizes the sideband master index stored in each slave
> adapter's response tracker. `XBAR_ID_WIDTH` is the AXI ID width inside the
> fabric and on every AXI slave port, because each master adapter sends
> `{BRIDGE_ID, slot}` (or `{BRIDGE_ID, id}` for a kept ID); a slave's
> `id_width` must be at least this. All
> four are emitted into `<bridge>_pkg.sv`. There is no `TOTAL_ID_WIDTH`.

### Per-Port Configuration

Each master and slave port carries its own field set in the configuration file.

#### Master Port Configuration

| Field | Type | Description |
|-------|------|-------------|
| name | string | Unique identifier |
| prefix | string | Signal prefix |
| channels | enum | "rw", "wr", or "rd" |
| data_width | int | Port data width |
| id_width | int | Port ID width |
| use_monitor | bool | Optional, defaults to `true`. Per-port monitor wrappers. Only meaningful on a `mon` variant; on a `no` variant there is nothing to disable. |

: Master Port Configuration

#### Slave Port Configuration

| Field | Type | Description |
|-------|------|-------------|
| name | string | Unique identifier |
| prefix | string | Signal prefix |
| protocol | enum | `axi4`, `axi5`, `axil`, `axil5`, `apb`, `apb5`, `wb4` -- the exact values `config_validator.valid_protocols` accepts. Note `axil`, not `axi4lite`. |
| axi5_features | list | On an `axi5` port: any of `nsaid`, `trace`, `mpam`, `mecid`, `unique` (droppable), `chunking` (droppable, 128-bit ports), `wakeup` (AWAKEUP, not path sideband), `poison`, `atomic`, `mte` (connectivity-gated; `mte` 128-bit ports). On an `axil5` port: `user` only. Classes and rules in HAS 4.4. |
| atomic_rr_depth | int, power of two 2..64 | Optional, default 8. On an `axi5` rw slave with `atomic` in its features: read-return atomics (AtomicLoad / Swap / Compare) in flight at this port, the depth of its `axi5_atomic_rr_tracker`; the next atomic AW waits while it is full (bridge TASK-020). Rejected on any other port. Reported in `<bridge>_sizing.json` and as `<SLAVE>_ATOMIC_RR_DEPTH` in the package. |
| data_width | int | Port data width |
| base_addr | hex | Base address (must be 4K-aligned) |
| addr_range | hex | Address range size (must be multiple of 4K) |
| use_monitor | bool | Optional, defaults to `true`. Per-port monitor wrappers. Only meaningful on a `mon` variant; on a `no` variant there is nothing to disable. |

: Slave Port Configuration

#### Slave Address Window Rules (MANDATORY)

Every slave must occupy a 4K-aligned address window that is a multiple of 4 KB:

```
Rule 1: Base Address Alignment
  base_addr & 0xFFF == 0x000
  
  Valid:   0x00000000, 0x00001000, 0x80000000, 0xFFFF0000
  Invalid: 0x00000001, 0x80000800, 0xC0000100

Rule 2: Range Alignment
  addr_range % 0x1000 == 0
  
  Valid:   0x1000 (4 KB), 0x2000 (8 KB), 0x10000 (64 KB)
  Invalid: 0x800 (2 KB), 0x1001, 0x7FFF

Rule 3: Non-Overlapping Windows
  All slaves must have non-overlapping address ranges
  
  Valid:   Slave0: 0x00000000-0x0FFFFFFF, Slave1: 0x10000000-0x1FFFFFFF
  Invalid: Slave0: 0x00000000-0x10000000, Slave1: 0x0FFFFFFF-0x1FFFFFFF
```

**Why This Rule Exists:**

- Real memory systems use 4K page boundaries (virtual memory, MMU)
- Linker scripts and memory maps assume 4K granularity
- Address decoders simplify to bit masks with 4K alignment
- Prevents ambiguity in address decode logic

There's nothing arbitrary about the 4K requirement — it's the granularity the rest of the system already assumes.

### Top-Level Monitor Configuration

When monitor collection is desired, the bridge TOML configuration includes:

| Field | Type | Description |
|-------|------|-------------|
| variants | list | List of bridge variants to generate. Supported: `["no"]` (no monitor), `["mon"]` (monitor only), `["no", "mon"]` (both). Default: `["no"]` |

: Top-Level Monitor Configuration

#### Monitor Identifiers

Each monitored port gets a unique `(UNIT_ID, AGENT_ID)` pair for identification in monitor packets:

```
UNIT_ID Assignment:
  - UNIT_ID = 1: Master-side monitor wrappers (axi4_master_{rd,wr}_monlite)
  - UNIT_ID = 2: Slave-side monitor wrappers (axi4_slave_{rd,wr}_monlite)

AGENT_ID Assignment (per port):
  - AGENT_ID = (port_index << 4) | channel_bit
  - channel_bit: 0 = read channel (AR/R), 1 = write channel (AW/W/B)
  - Example: Master port 2, write direction → AGENT_ID = (2 << 4) | 1 = 0x21
```

#### AXIL→Wider-Slave Master-Side Alignment

When an AXI4-Lite master connects to a wider AXI4 slave through the bridge (e.g., 32-bit AXIL master to 64-bit AXI4 slave), the generator emits a master-side alignment converter (the `axil_to_axi4_wide_align_{rd,wr}` modules) between the master adapter and the crossbar core. The converter handles partial-word alignment on the narrow side while preserving AXIL's single-beat semantics; the protocol stays AXIL — protocol shims are a slave-boundary concern, applied separately.

### Parameter Validation

#### Generator Checks

The generator checks every configuration against these rules:

| Check | Error Condition |
|-------|-----------------|
| NUM_MASTERS | < 1 or > 32 |
| NUM_SLAVES | < 1 or > 256 |
| DATA_WIDTH | Not power of 2 |
| Address overlap | Slave ranges intersect |
| Connectivity | Master with no slaves |
| ID width | Insufficient for masters |

: Generator Validation Checks

#### Runtime Validation

Bridge includes optional assertions for:

- Address alignment
- Burst boundary crossing
- Protocol violations
- ID mismatch

## Usage Example

A complete configuration is two parts: the TOML file that describes the bridge, and the CSV that describes the connectivity.

### TOML Configuration

```toml
[bridge]
  name = "my_bridge"
  description = "Example bridge configuration"

  defaults.skid_depths = {ar = 2, r = 4, aw = 2, w = 4, b = 2}
  # (the generator's own default is 2 on every channel since bridge TASK-016 --
  #  the smallest stage that sustains a beat per cycle; a deeper W or R stage
  #  buys elasticity, not rate. The internal catch-all slave follows these
  #  defaults too.)

  masters = [
    {name = "cpu", prefix = "cpu_m_axi", channels = "rw",
     id_width = 4, addr_width = 32, data_width = 64, user_width = 1},
    {name = "dma", prefix = "dma_m_axi", channels = "rw",
     id_width = 4, addr_width = 32, data_width = 256, user_width = 1}
  ]

  slaves = [
    {name = "ddr", prefix = "ddr_s_axi", protocol = "axi4",
     id_width = 6, addr_width = 32, data_width = 512, user_width = 1,
     base_addr = 0x80000000, addr_range = 0x40000000},
    {name = "uart", prefix = "uart_apb", protocol = "apb",
     addr_width = 12, data_width = 32,
     base_addr = 0x00000000, addr_range = 0x00001000}
  ]
```

### CSV Connectivity

```csv
master\slave,ddr,uart
cpu,1,1
dma,1,0
```

Two configurations to use as starting points:

### Simple 2x2

```toml
[bridge]
  name = "bridge_simple"
  masters = [
    {name = "m0", prefix = "m0_axi", data_width = 64},
    {name = "m1", prefix = "m1_axi", data_width = 64}
  ]
  slaves = [
    {name = "s0", prefix = "s0_axi", base_addr = 0x0, addr_range = 0x10000000},
    {name = "s1", prefix = "s1_axi", base_addr = 0x10000000, addr_range = 0x10000000}
  ]
```

### Mixed Protocol

```toml
[bridge]
  name = "bridge_mixed"
  masters = [
    {name = "cpu", prefix = "cpu_axi", data_width = 64, channels = "rw"}
  ]
  slaves = [
    {name = "mem",  prefix = "mem_axi",  protocol = "axi4", data_width = 512,
     base_addr = 0x00000000, addr_range = 0x80000000},
    {name = "gpio", prefix = "gpio_apb", protocol = "apb",  data_width = 32,
     base_addr = 0x80000000, addr_range = 0x00010000},
    {name = "uart", prefix = "uart_apb", protocol = "apb",  data_width = 32,
     base_addr = 0x80010000, addr_range = 0x00010000}
  ]
```
