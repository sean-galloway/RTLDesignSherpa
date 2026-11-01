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

# `l1_fabric_contract.md` — core-facing fabric seam

This document is the single source of truth a future CHI fabric plane
implements against.  It applies to both amber and jet: the seam is identical
at the core boundary, even though the two IPs parameterise it differently
(MSHR count, victim depth, response sequencer depth).  The current fabric
planes (`l1_axi4_plane`, `l1_ace_plane`) already satisfy this contract; the
CHI stub (`l1_chi_plane_stub`) proves the port list is syntactically
complete.

## Intent

The cache-ip plane restructure isolates the protocol generation in a named
**fabric plane**.  The coherence core plane (`l1_coh_core` / `jet_coh_core`)
is protocol-agnostic MESI; it must not change when the ACE fabric plane is
replaced by a CHI fabric plane.  This contract defines the exact boundary
between the coherence core plane and any fabric plane.

## Core-facing fabric seam

The seam is a bundle of named directed signals presented by the fabric plane
to the coherence core plane.  All widths use the parameter defaults from
`l1_pkg`:

| Parameter | Default | Meaning |
|---|---|---|
| `ADDR_WIDTH` | `AMBER_ADDR_WIDTH` (32) | byte address |
| `BUS_WIDTH` | `AMBER_BUS_WIDTH` (64) | datapath width |
| `LINE_BYTES` | `AMBER_LINE_BYTES` (64) | cache line size |
| `AXI_ID_WIDTH` | 8 | `fub_axi` ID width |
| `AXI_USER_WIDTH` | 1 | `fub_axi` user width |

### 1. Snoop request in (fabric → core)

| Signal | Direction | Width | Meaning |
|---|---|---|---|
| `ctrl_snoop_req` | output (fabric → core) | 1 | new snoop request valid |
| `ctrl_snoop_addr` | output | `ADDR_WIDTH` | snoop byte address |
| `ctrl_snoop_type` | output | 3 | snoop type encoding (ACE-derived; see `l1_pkg`) |
| `ctrl_snoop_ready` | input (core → fabric) | 1 | core accepts the snoop this cycle |
| `ctrl_snoop_safe` | input | 1 | core grants snoop service (may be combinatorial) |

Semantics:
- `ctrl_snoop_req` is asserted when the fabric has accepted an external snoop
  and is presenting it to the core.
- The core answers with `ctrl_snoop_ready` in the cycle it services the
  request; the fabric holds `ctrl_snoop_req` until accepted.
- `ctrl_snoop_safe` is the core's guard that prevents a new snoop colliding
  with a critical pipeline window (victim capture, pending-fill commit,
  etc.).  It is an input to the fabric so the snoop responder can hold
  `ctrl_snoop_req` low when unsafe.

### 2. Snoop response out (core → fabric)

| Signal | Direction | Width | Meaning |
|---|---|---|---|
| `ctrl_crresp` | input (core → fabric) | `AMBER_CRRESP_WIDTH` | CRRESP bit field |
| `ctrl_cddata` | input | `BUS_WIDTH` | CD data beat |
| `ctrl_cdlast` | input | 1 | last data beat of this response |
| `ctrl_cdvalid` | input | 1 | CD data valid |
| `ctrl_cdready` | output (fabric → core) | 1 | fabric accepts the CD beat |

Semantics:
- `ctrl_crresp` is sampled by the fabric on the cycle `ctrl_snoop_req` is
  accepted (`ctrl_snoop_ready` high).
- `ctrl_cdvalid` / `ctrl_cddata` / `ctrl_cdlast` are driven by the core until
  `ctrl_cdready` is high on the last beat (`ctrl_cdlast`).
- The fabric's snoop responder guarantees CDLAST before CRVALID to the
  external ACE pins.

### 3. Engine (fill / drain) burst channels

The core exposes an AXI4-like read-master interface for fills and a
write-master interface for writebacks/victims.  These are the **raw engine
pins** upstream of any transport; the fabric plane closes the transport.

#### Read (fill) engine — `fub_axi_*` AR/R

| Signal | Direction | Width | Meaning |
|---|---|---|---|
| `fub_axi_arid` | input | `AXI_ID_WIDTH` | AR ID (single ID in v1) |
| `fub_axi_araddr` | input | `ADDR_WIDTH` | AR byte address |
| `fub_axi_arlen` | input | 8 | AR burst length (beats − 1) |
| `fub_axi_arsize` | input | 3 | AR burst size |
| `fub_axi_arburst` | input | 2 | AR burst type (INCR) |
| `fub_axi_arlock` | input | 1 | AR lock |
| `fub_axi_arcache` | input | 4 | AR cache hint |
| `fub_axi_arprot` | input | 3 | AR protection |
| `fub_axi_arqos` | input | 4 | AR QoS |
| `fub_axi_arregion` | input | 4 | AR region |
| `fub_axi_aruser` | input | `AXI_USER_WIDTH` | AR user |
| `fub_axi_arvalid` | input | 1 | AR valid |
| `fub_axi_arready` | output | 1 | AR ready |
| `fub_axi_rid` | output | `AXI_ID_WIDTH` | R ID |
| `fub_axi_rdata` | output | `BUS_WIDTH` | R data |
| `fub_axi_rresp` | output | 4 | R response (ACE plane uses 4 bits; AXI4 plane pads 2-bit to 4) |
| `fub_axi_rlast` | output | 1 | R last |
| `fub_axi_ruser` | output | `AXI_USER_WIDTH` | R user |
| `fub_axi_rvalid` | output | 1 | R valid |
| `fub_axi_rready` | input | 1 | R ready |

#### Write (drain) engine — `fub_axi_*` AW/W/B

| Signal | Direction | Width | Meaning |
|---|---|---|---|
| `fub_axi_awid` | input | `AXI_ID_WIDTH` | AW ID |
| `fub_axi_awaddr` | input | `ADDR_WIDTH` | AW byte address |
| `fub_axi_awlen` | input | 8 | AW burst length |
| `fub_axi_awsize` | input | 3 | AW burst size |
| `fub_axi_awburst` | input | 2 | AW burst type |
| `fub_axi_awlock` | input | 1 | AW lock |
| `fub_axi_awcache` | input | 4 | AW cache hint |
| `fub_axi_awprot` | input | 3 | AW protection |
| `fub_axi_awqos` | input | 4 | AW QoS |
| `fub_axi_awregion` | input | 4 | AW region |
| `fub_axi_awuser` | input | `AXI_USER_WIDTH` | AW user |
| `fub_axi_awvalid` | input | 1 | AW valid |
| `fub_axi_awready` | output | 1 | AW ready |
| `fub_axi_wdata` | input | `BUS_WIDTH` | W data |
| `fub_axi_wstrb` | input | `BUS_WIDTH/8` | W strobe |
| `fub_axi_wlast` | input | 1 | W last |
| `fub_axi_wuser` | input | `AXI_USER_WIDTH` | W user |
| `fub_axi_wvalid` | input | 1 | W valid |
| `fub_axi_wready` | output | 1 | W ready |
| `fub_axi_bid` | output | `AXI_ID_WIDTH` | B ID |
| `fub_axi_bresp` | output | 2 | B response |
| `fub_axi_buser` | output | `AXI_USER_WIDTH` | B user |
| `fub_axi_bvalid` | output | 1 | B valid |
| `fub_axi_bready` | input | 1 | B ready |

### 4. Coherence launch-event sideband

| Signal | Direction | Width | Meaning |
|---|---|---|---|
| `core_coh_req_valid` | input (core → fabric) | 1 | a coherence transaction launches this cycle |
| `core_coh_req_addr` | input | `ADDR_WIDTH` | launch byte address |
| `core_coh_req_type` | input | 3 | launch class (`AMBER_ACE_*` encodings in v1) |

Exported fabric-side (pair-rig style):

| Signal | Direction | Width | Meaning |
|---|---|---|---|
| `coh_req_valid` | output | 1 | launch valid |
| `coh_req_addr` | output | `ADDR_WIDTH` | launch address |
| `coh_req_type` | output | 3 | launch class |

In the ACE plane these events are consumed on-chip by `l1_ace_issue`.  In the
AXI4 plane they are exported to the pair-rig fabric.  A CHI plane would map
them into CHI `TXREQ`/`TXRSP`/`TXDAT` flits.

### 5. AC-pending throttle

| Signal | Direction | Width | Meaning |
|---|---|---|---|
| `sn_want_o` | output (fabric → core) | 1 | a snoop request is pending in the fabric |

The fabric samples external AC/RXSNP handshakes and the snoop grant to
produce a one-cycle-safe pending indicator.  The jet coherence core uses this
as the J6 throttle input; amber does not use it but the seam carries it
uniformly.

### 6. MonBus observation

| Signal | Direction | Width | Meaning |
|---|---|---|---|
| `mon_valid` | output | 1 | observer has a packet |
| `mon_ready` | input | 1 | downstream accepts the packet |
| `mon_packet` | output | 128 | `ocelus_common_pkg::monitor_packet_t` |
| `mon_timestamp` | output | 64 | `ocelus_common_pkg::monbus_timestamp_t` |
| `i_mon_time` | input | 64 | rig-level timestamp source |

The fabric plane merges its internal transport observers before exporting a
single `mon_valid/ready/packet/timestamp` stream.  The top-level
`monbus_arbiter` merges this with the coherence core's `l1_monlite` stream
(and, for jet, the J7 `jet_monlite` stream).

## Rules

### One outstanding coherence transaction class per direction (v1)

The coherence core issues at most one fill-class launch and one
writeback-class launch at a time.  The fabric plane may assume this and need
not queue multiple launches internally.

### Response ordering

Fill responses must return in AR issue order.  Writeback responses (`BVALID`)
match the single in-flight AW order.  A CHI plane must preserve the same
per-class ordering visible at the core boundary.

### Launch-event mux discipline

The coherence core may produce two launch events in the same cycle — a fill
launch and a writeback (victim-drain) launch.  The **fill launch wins the
single-event slot**; the writeback is held and replayed on the next cycle.
This discipline is enforced **inside the coherence core plane** (the
`u_coh`/`jet_coh_core` launch adapter), so every fabric plane — AXI4, ACE,
and future CHI — inherits an already-disciplined one-event-per-cycle stream.
The fabric plane therefore consumes a single `core_coh_req_valid` event per
cycle and never sees colliding fill + writeback launches.

## Per-IP MonBus convention

The fabric-plane transport observers stamp each packet with an `AGENT_ID` and
a `UNIT_ID`:

| Field | amber | jet | Meaning |
|---|---|---|---|
| `AGENT_ID` | `16'h00A0` | `16'h00A1` | per-IP stream identifier |
| read-transport `UNIT_ID` | `8'h02` | `8'h02` | fill / read engine |
| write-transport `UNIT_ID` | `8'h03` | `8'h03` | drain / write engine |

The default `AGENT_ID` (`16'h00A0`) is amber; the jet tops pass `16'h00A1`
to preserve jet's historical stream id.

## jet observability addition

`jet_ace_top` carries a third MonBus input on the top-level arbiter: the **J7**
stream from `jet_monlite` / the MSHR observer.  The contract does not change
— the fabric plane still exports one merged `{rd,wr}` observer stream — but
the top-level arbiter is a 3:1 merge (`l1_monlite`, fabric observers, J7
`jet_monlite`).

## Forward reservations (J8–J10)

These are intentionally **not built** in the current restructure; the seams
above are reserved so they can land later without changing the boundary.

### J8 — AMO cache-side ALU

The CPU-plane request payload (`cpu_req_wr_data`) will gain an **op field**
(`LD` / `ST` / nine word AMOs).  The bit layout of `cpu_req_wr_data` keeps
MSB room for this field.  The field is marked **reserved** here; no fabric
plane consumes it yet.

### J9 — LR/SC sideband

The CPU plane will export a one-line **"snoop service touched line X"**
notice toward the core (for LR/SC monitoring).  The seam records the notice
as **reserved**; nothing is wired in this task.

### J10 — `aq`/`rl`

Ruled **no cache hardware**.  The RISC-V `aq`/`rl` bits do not add cache-side
state; noted here only so the seam review does not reopen the question.

## CHI swap demonstration

`l1_chi_plane_stub` is an elaboration-only proof.  It carries:

- the full core-facing seam on one side (snoop, `fub_axi` fill/drain,
  `core_coh_req_*`, `sn_want_o`, MonBus);
- a CHI channel pin skeleton on the other side:
  - `chi_rxreq_*` / `chi_rxsnp_*` — inputs from the interconnect;
  - `chi_txreq_*` / `chi_txrsp_*` / `chi_txdat_*` — outputs to the
    interconnect;
  - `chi_rxdat_*` — data input from the interconnect.

All CHI-side outputs are tied off.  A real CHI plane would:

1. Decode `chi_rxsnp_*` into the core-facing snoop seam (`ctrl_snoop_req`,
   `ctrl_snoop_addr`, `ctrl_snoop_type`).
2. Map the core's `core_coh_req_*` launch events into CHI `TXREQ` flits
   (read-shared, read-unique, clean-unique, evict/writeback).
3. Replace the `fub_axi` fill/drain engines with CHI DAT/RSP transport state
   machines.
4. Produce a CHI-equivalent `sn_want_o` from the pending snoop count.
5. Export a MonBus observer stream from the CHI transport layers.

The stub's channel widths are illustrative placeholders; a real CHI plane
would import a CHI package or take width parameters.

## Elaboration proof

The stub is linted/elaborated standalone through its filelist:

```bash
python3 bin/flatten_filelist.py \
    projects/components/cache-ip/common-ip/rtl/filelists/plane/l1_chi_plane_stub.f \
    --resolve-env --absolute-paths -o /tmp/l1_chi_plane_stub_flat.f
verilator --lint-only -Wall -Wno-TIMESCALEMOD -Wno-fatal \
    -Irtl/amba/includes -f /tmp/l1_chi_plane_stub_flat.f --top-module l1_chi_plane_stub
```

The expected result is a clean pass with no errors.

## References

- [cache-ip plane restructure design spec](../../../../../docs/superpowers/specs/2026-10-30-cache-ip-plane-restructure-design.md)
- [The shared core contract](l1_shared_core.md)
- `projects/components/cache-ip/common-ip/rtl/plane/l1_axi4_plane.sv`
- `projects/components/cache-ip/common-ip/rtl/plane/l1_ace_plane.sv`
- `projects/components/cache-ip/common-ip/rtl/plane/l1_chi_plane_stub.sv`
