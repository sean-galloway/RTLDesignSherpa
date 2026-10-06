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

# ACE (AXI Coherency Extensions) Modules

**Location:** `rtl/amba/ace/`
**Status:** Production Ready

---

## Overview

The ACE subsystem is the AMBA AXI Coherency Extensions transport layer for the `cache-ip` family (amber/jet caches, onyx CCU). ACE extends AXI4 with coherent transaction-type fields on the address channels (`ARSNOOP[3:0]`, `AWSNOOP[2:0]`) and three additional snoop channels (AC/CR/CD) so that a coherency manager can broadcast snoops to peer caches and gather their responses.

These modules are **channel movers with skid buffers**, not protocol controllers. They carry the ACE-shaped port contract defined in `projects/components/cache-ip/References/AMBA_ACE_Interface_Definition.md`: the onyx D2 subset supports ReadShared, ReadUnique, CleanUnique, MakeUnique, WriteBack, and Evict; full ACE/ACE-Lite conformance is intentionally not claimed.

### What is here

- Six base channel movers (base + `_monlite` only; no `_cg`, `_mon`, or stubs):
  - Front-side read/write masters and slaves (`axi4ace_master_rd/wr`, `axi4ace_slave_rd/wr`)
  - Snoop-side cache responder and CCU initiator (`axi4ace_snoop_slave/master`)
- Eight `_monlite` wrappers in `rtl/amba/ace/` that wrap the base movers with the lite-monitor discipline.
- One new ACE-aware monitor core in `rtl/amba/monitor/axi4ace_snoop_monitor_lite.sv` that tracks snoops in AC-issue order because snoop channels have no ID.

### Key Features

- **AXI4 + ACE payloads:** Full AXI4 address/data channels plus `ARSNOOP`/`AWSNOOP`
- **Auto-pulsed acknowledges:** Master read/write movers generate `RACK`/`WACK` one cycle after the transaction completes (no ordering semantics in the current subset)
- **Snoop transport:** AC in, CR/CD out (cache side) or AC out, CR/CD in (CCU side)
- **Lite monitoring:** Front-side wrappers use `axi_monitor_lite`; snoop-side wrappers use `axi4ace_snoop_monitor_lite`
- **Skid-buffer elasticity:** Per-channel configurable depth, same `gaxi_skid_buffer` infrastructure as the rest of the AMBA library

### Module Categories

#### Core Front-Side Movers

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axi4ace_master_rd** | ACE read master with `ARSNOOP[3:0]` and auto-pulsed `RACK` | [axi4ace_master_rd.md](axi4ace_master_rd.md) | Documented |
| **axi4ace_master_wr** | ACE write master with `AWSNOOP[2:0]` and auto-pulsed `WACK` | [axi4ace_master_wr.md](axi4ace_master_wr.md) | Documented |
| **axi4ace_slave_rd** | ACE read slave with `ARSNOOP[3:0]` pass-through | [axi4ace_slave_rd.md](axi4ace_slave_rd.md) | Documented |
| **axi4ace_slave_wr** | ACE write slave with `AWSNOOP[2:0]` pass-through | [axi4ace_slave_wr.md](axi4ace_slave_wr.md) | Documented |

#### Snoop-Side Movers

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axi4ace_snoop_slave** | Cache-side snoop responder transport: AC in, CR/CD out | [axi4ace_snoop_slave.md](axi4ace_snoop_slave.md) | Documented |
| **axi4ace_snoop_master** | CCU-side snoop initiator transport: AC out, CR/CD in | [axi4ace_snoop_master.md](axi4ace_snoop_master.md) | Documented |

#### Monitor Wrappers

All eight wrappers are documented collectively in [monitor/axi_monitor_lite_wrappers.md](../monitor/axi_monitor_lite_wrappers.md).

| Wrapper | Core | Monitor core | Role |
|---------|------|--------------|------|
| **axi4ace_master_rd_monlite** | `axi4ace_master_rd` | `axi_monitor_lite` | Front-side read master + lite monitor |
| **axi4ace_master_wr_monlite** | `axi4ace_master_wr` | `axi_monitor_lite` | Front-side write master + lite monitor |
| **axi4ace_slave_rd_monlite** | `axi4ace_slave_rd` | `axi_monitor_lite` | Front-side read slave + lite monitor |
| **axi4ace_slave_wr_monlite** | `axi4ace_slave_wr` | `axi_monitor_lite` | Front-side write slave + lite monitor |
| **axi4ace_snoop_slave_monlite** | `axi4ace_snoop_slave` | `axi4ace_snoop_monitor_lite` | Cache-side snoop responder + snoop monitor |
| **axi4ace_snoop_master_monlite** | `axi4ace_snoop_master` | `axi4ace_snoop_monitor_lite` | CCU-side snoop initiator + snoop monitor |

The front-side `_monlite` wrappers use the same `axi_monitor_lite` taps as the AXI4/AXI5 families; the snoop-side wrappers use the new `axi4ace_snoop_monitor_lite` core because snoop channels have no transaction ID.

---

## Functional Description

### ACE adds to AXI4

On the front side, every address channel gains a transaction-type field:

| Channel | Field | Width | Meaning |
|---------|-------|-------|---------|
| AR | `ARSNOOP` | 4 | Read-side coherent transaction type |
| AW | `AWSNOOP` | 3 | Write-side coherent transaction type |

Data and response channels are unchanged AXI4. Masters additionally drive:

| Signal | Direction | Meaning |
|--------|-----------|---------|
| `RACK` | Output | One-cycle pulse after the last read data beat |
| `WACK` | Output | One-cycle pulse after the write response |

The current subset gives these acknowledges no ordering semantics; they are auto-pulsed promptly by the master movers and recorded as such.

### Snoop channels

The snoop side uses three channels between the coherency manager (onyx) and each peer cache (amber/jet):

| Channel | Dir (cache view) | Payload | Meaning |
|---------|------------------|---------|---------|
| **AC** | In | `ACADDR`, `ACSNOOP[3:0]`, `ACPROT[2:0]` | Snoop address/command |
| **CR** | Out | `CRRESP[4:0]` | Snoop response |
| **CD** | Out | `CDDATA`, `CDLAST` | Snoop data |

The cache-side mover is `axi4ace_snoop_slave`; the manager-side mover is `axi4ace_snoop_master`. Both are pure transports: they buffer the channels and present the same payload on the FUB side as on the AXI side.

### Ordering rules

ACE requires:

- CR and CD only after the AC handshake
- CR responses in the same order as AC addresses
- CD data in the same order as AC addresses
- Multiple outstanding snoops are allowed

The `cache-ip` family convention is stricter: a cache completes all CD beats for a snoop before asserting its CR, so onyx sees one fully-closed response at a time. That convention is enforced by the cache adapter, not by these transport modules.

### CRRESP bit semantics

| Bit | Name | Meaning when set |
|---|---|---|
| [0] | DataTransfer | Responder will drive data on CD |
| [1] | Error | Responder's lookup had an error |
| [2] | PassDirty | Dirty responsibility moves with the data |
| [3] | IsShared | Another master may hold a copy |
| [4] | WasUnique | Line was unique in the responder (IHI 0022) |

---

## Timing

### Throughput

| Configuration | Address CH | Data CH | Notes |
|--------------|------------|---------|-------|
| Single transaction | 1 txn/cycle | 1 beat/cycle | When buffers not stalled |
| Burst (len=16) | 1 txn/16 cycles | 1 beat/cycle | Sustained |
| Multiple outstanding | Up to table depth | 1 beat/cycle | Out-of-order on front side, in-order on snoop side |

### Latency

| Path | Cycles | Notes |
|------|--------|-------|
| AR → R (single) | 2-3 | Minimum read latency |
| AW → B (single) | 2-3 | Minimum write latency |
| AC → CR (single) | 2-3 | Snoop response latency |
| Buffer overhead | +1 per channel | Skid buffer latency |

---

## Usage Example

### ACE read master

```systemverilog
axi4ace_master_rd #(
    .SKID_DEPTH_AR(2),
    .SKID_DEPTH_R(4),
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64)
) u_ace_rd_master (
    .aclk           (axi_clk),
    .aresetn        (axi_resetn),
    // FUB side (upstream requestor)
    .fub_axi_arid   (cpu_arid),
    .fub_axi_araddr (cpu_araddr),
    .fub_axi_arlen  (cpu_arlen),
    .fub_axi_arsnoop(cpu_arsnoop),   // ACE read transaction type
    // ...
    // Master side (downstream manager/CCU)
    .m_axi_arid     (m_arid),
    .m_axi_araddr   (m_araddr),
    .m_axi_arsnoop  (m_arsnoop),
    // ...
    .m_axi_rack     (m_rack),        // auto-pulsed by the module
    .busy           (rd_busy)
);
```

### Cache-side snoop responder

```systemverilog
axi4ace_snoop_slave #(
    .SKID_DEPTH_AC(2),
    .SKID_DEPTH_CR(4),
    .SKID_DEPTH_CD(4),
    .ADDR_WIDTH(32),
    .DATA_WIDTH(64)
) u_snoop_slave (
    .aclk          (axi_clk),
    .aresetn       (axi_resetn),
    // Manager/CCU side
    .m_axi_acaddr  (snp_acaddr),
    .m_axi_acsnoop (snp_acsnoop),
    .m_axi_acprot  (snp_acprot),
    .m_axi_acvalid (snp_acvalid),
    .m_axi_acready (snp_acready),
    .m_axi_crresp  (snp_crresp),
    .m_axi_crvalid (snp_crvalid),
    .m_axi_crready (snp_crready),
    .m_axi_cddata  (snp_cddata),
    .m_axi_cdlast  (snp_cdlast),
    .m_axi_cdvalid (snp_cdvalid),
    .m_axi_cdready (snp_cdready),
    // Cache FSM side
    .fub_acaddr    (fub_acaddr),
    .fub_acsnoop   (fub_acsnoop),
    .fub_acprot    (fub_acprot),
    .fub_acvalid   (fub_acvalid),
    .fub_acready   (fub_acready),
    .fub_crresp    (fub_crresp),
    .fub_crvalid   (fub_crvalid),
    .fub_crready   (fub_crready),
    .fub_cddata    (fub_cddata),
    .fub_cdlast    (fub_cdlast),
    .fub_cdvalid   (fub_cdvalid),
    .fub_cdready   (fub_cdready),
    .busy          (snp_busy)
);
```

---

## Design Notes

### Buffer depth guidelines

`SKID_DEPTH_*` is an entry count, not a log2 exponent. Legal values are 2..8 inclusive (any integer, odd depths are legal). Values above 8 fail elaboration; place a `gaxi_fifo_sync` stage ahead of the module for deeper elasticity.

### Snoop monitor vs. front-side monitor

The front-side ACE wrappers reuse `axi_monitor_lite`, which tracks AXI transactions by ID. The snoop-side wrappers use `axi4ace_snoop_monitor_lite` because snoop channels have no ID: the monitor keeps a circular table of outstanding snoops in AC-issue order and attributes each CR/CDLAST to the oldest entry.

### What is not here

- No `_cg` variants: clock gating is not provided for ACE in this release
- No `_mon` variants: only the lite-monitor wrappers exist
- No stubs: these are production channel movers
- ACE-Lite is not separately implemented; the `cache-ip` contract is full ACE-shaped on the pins documented here

---

## Related Modules

- [axi4ace_snoop_monitor_lite](../monitor/axi4ace_snoop_monitor_lite.md) — ACE snoop-channel monitor core
- [axi_monitor_lite_wrappers](../monitor/axi_monitor_lite_wrappers.md) — the eight `_monlite` wrappers
- [AXI4 modules](../axi4/README.md) — the base protocol these modules extend
- [AMBA ACE Interface Definition](../../../../projects/components/cache-ip/References/AMBA_ACE_Interface_Definition.md) — the in-repo port contract

---

## References

- ARM IHI 0022H: *AMBA AXI and ACE Protocol Specification* (ACE chapters) — cited, not mirrored
- `projects/components/cache-ip/References/AMBA_ACE_Interface_Definition.md` — working interface definition for this family

---

**Last Updated:** 2026-10-05

---

## Navigation

- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
