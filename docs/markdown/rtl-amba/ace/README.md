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

The ACE subsystem is the AMBA AXI Coherency Extensions transport layer for the `cache-ip` family (amber/jet caches, onyx CCU). ACE extends AXI4 with coherent transaction-type, shareability-domain and barrier fields on the address channels (`ARSNOOP[3:0]`/`AWSNOOP[2:0]`, `ARDOMAIN[1:0]`/`AWDOMAIN[1:0]`, `ARBAR[1:0]`/`AWBAR[1:0]`), a 4-bit `RRESP` on read data, and three additional snoop channels (AC/CR/CD) so that a coherency manager can broadcast snoops to peer caches and gather their responses.

These modules are **channel movers with skid buffers**, not protocol controllers. They carry the ACE-shaped port contract defined in `projects/components/cache-ip/References/AMBA_ACE_Interface_Definition.md`: the onyx D2 subset supports ReadShared, ReadUnique, CleanUnique, MakeUnique, WriteBack, and Evict; full ACE/ACE-Lite conformance is intentionally not claimed.

### What is here

- Six base channel movers (base + `_monlite` only; no `_cg`, `_mon`, or stubs):
  - Front-side read/write masters and slaves (`axi4ace_master_rd/wr`, `axi4ace_slave_rd/wr`)
  - Snoop-side cache responder and CCU initiator (`axi4ace_snoop_slave/master`)
- Eight `_monlite` wrappers in `rtl/amba/ace/` that wrap the base movers with the lite-monitor discipline.
- One new ACE-aware monitor core in `rtl/amba/ocelus/axi4ace_snoop_monitor_lite.sv` that tracks snoops in AC-issue order because snoop channels have no ID.

### Key Features

- **AXI4 + ACE payloads:** Full AXI4 address/data channels plus `AxSNOOP`, `AxDOMAIN`, `AxBAR` and the 4-bit ACE `RRESP` (IHI 0022H §D2.1). The optional `AWUNIQUE` (WriteEvict only) is not carried.
- **Acknowledges:** Master read/write movers generate `RACK`/`WACK` one cycle after the transaction completes (no ordering semantics in the current subset); the slave movers take the manager's `RACK`/`WACK` and forward it to the backend
- **Snoop transport:** AC in, CR/CD out (cache side) or AC out, CR/CD in (CCU side)
- **Lite monitoring:** Front-side wrappers use `axi_monitor_lite`; snoop-side wrappers use `axi4ace_snoop_monitor_lite`
- **Skid-buffer elasticity:** Per-channel configurable depth, same `gaxi_skid_buffer` infrastructure as the rest of the AMBA library

### Module Categories

#### Core Front-Side Movers

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axi4ace_master_rd** | ACE read master with `ARSNOOP`/`ARDOMAIN`/`ARBAR`, 4-bit `RRESP` and auto-pulsed `RACK` | [axi4ace_master_rd.md](axi4ace_master_rd.md) | Documented |
| **axi4ace_master_wr** | ACE write master with `AWSNOOP`/`AWDOMAIN`/`AWBAR` and auto-pulsed `WACK` | [axi4ace_master_wr.md](axi4ace_master_wr.md) | Documented |
| **axi4ace_slave_rd** | ACE read slave: `ARSNOOP`/`ARDOMAIN`/`ARBAR` and 4-bit `RRESP` pass-through, `RACK` forwarded | [axi4ace_slave_rd.md](axi4ace_slave_rd.md) | Documented |
| **axi4ace_slave_wr** | ACE write slave: `AWSNOOP`/`AWDOMAIN`/`AWBAR` pass-through, `WACK` forwarded | [axi4ace_slave_wr.md](axi4ace_slave_wr.md) | Documented |

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

On the front side, ACE adds these signals to the AXI4 channels (IHI 0022H §D2.1, Tables D2-1 to D2-3):

| Channel | Field | Width | Meaning |
|---------|-------|-------|---------|
| AR | `ARSNOOP` | 4 | Read-side transaction type |
| AR | `ARDOMAIN` | 2 | Shareability domain: 00 Non-shareable, 01 Inner, 10 Outer, 11 System (Table D3-2) |
| AR | `ARBAR` | 2 | Barrier: 00 normal, 01 memory barrier, 10 normal ignoring barriers, 11 synchronization barrier (Table D3-5) |
| AW | `AWSNOOP` | 3 | Write-side transaction type |
| AW | `AWDOMAIN` | 2 | Shareability domain, as `ARDOMAIN` |
| AW | `AWBAR` | 2 | Barrier, as `ARBAR` |
| R | `RRESP[3:2]` | 2 | `RRESP` is 4 bits: `[2]` PassDirty, `[3]` IsShared (Table D3-14) |

W and B are unchanged AXI4. The movers carry every field without decoding it; whether a given `AxSNOOP`/`AxDOMAIN`/`AxBAR` combination is legal (Tables D3-7 and D3-8) is the issuing manager's responsibility. `AWUNIQUE`, required only by a component that supports WriteEvict, is not carried. The front-side monitors see `RRESP[1:0]` only, so IsShared and PassDirty are never counted as errors.

The manager additionally drives the acknowledges (§D2.3):

| Signal | Master movers | Slave movers | Meaning |
|--------|---------------|--------------|---------|
| `RACK` | Output, auto-pulsed | `s_axi_rack` in, forwarded to `fub_axi_rack` | One-cycle pulse after the last read data beat |
| `WACK` | Output, auto-pulsed | `s_axi_wack` in, forwarded to `fub_axi_wack` | One-cycle pulse after the write response |

The current subset gives these acknowledges no ordering semantics; the master movers auto-pulse them promptly and the slave movers forward them as wires.

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

- Arm. *AMBA AXI and ACE Protocol Specification*, ARM IHI 0022H.c, Jan. 2021, Part D "AMBA ACE and ACE-Lite Protocol Specification". [developer.arm.com/documentation/ihi0022/h](https://developer.arm.com/documentation/ihi0022/h/) — ch. D2 "Signal Descriptions", ch. D3 "Channel Signaling" (§D3.3 `RACK`, §D3.5 `WACK`, §D3.6-§D3.9 snoop channels and their dependencies), ch. D5 "Snoop Transactions". Issues J and later remove ACE from IHI 0022, so Issue H.c is the last to define it. Cited, not mirrored.
- Carloni, L.P., McMillan, K.L., Sangiovanni-Vincentelli, A.L. "Theory of Latency-Insensitive Design." *IEEE Trans. Computer-Aided Design of Integrated Circuits and Systems*, 20(9), Sept. 2001. DOI: [10.1109/43.945302](https://doi.org/10.1109/43.945302) — the valid/ready channel discipline behind the `gaxi_skid_buffer` queues: a buffered stage may stall or add latency without changing what the endpoints compute.
- Papamarcos, M.S., Patel, J.H. "A Low-Overhead Coherence Solution for Multiprocessors with Private Cache Memories." *Proc. 11th Int. Symp. Computer Architecture (ISCA)*, 1984, pp. 348-354. DOI: [10.1145/800015.808204](https://doi.org/10.1145/800015.808204) — the snoopy write-back protocol with an exclusive-clean state (MESI) that the snoop channels serve; background only, since this family holds no coherence state.
- Sweazey, P., Smith, A.J. "A Class of Compatible Cache Consistency Protocols and their Support by the IEEE Futurebus." *Proc. 13th ISCA*, 1986; *ACM SIGARCH Computer Architecture News*, 14(2), May 1986, pp. 414-423. DOI: [10.1145/17356.17404](https://doi.org/10.1145/17356.17404) — the MOESI state class (the Owned state, `PassDirty` ownership transfer); background only.
- Nagarajan, V., Sorin, D.J., Hill, M.D., Wood, D.A. *A Primer on Memory Consistency and Cache Coherence*, 2nd ed. Synthesis Lectures on Computer Architecture, Morgan & Claypool, 2020. DOI: [10.1007/978-3-031-01764-3](https://doi.org/10.1007/978-3-031-01764-3) — ch. 7 "Snooping Coherence Protocols" (§7.3 Exclusive state, §7.4 Owned state, §7.5 non-atomic bus): what a snoop request and response mean to the caches at each end.
- Maaref, M. *Architecting and Building High-Speed SoCs*, Packt, 2022, ch. 3 "Basic and Advanced On-Chip Busses and Interconnects", sections "ARM AMBA interconnect protocols suite" (ACE) and "Data sharing and coherency challenges" — textbook treatment (secondary source).
- Handy, J. *The Cache Memory Book*, 2nd ed., 1998, ch. 4 "Maintaining Coherency in Cached Systems", §4.3.1 "The MESI Protocol" and §4.3.3 "The MOESI Protocol" — textbook treatment (secondary source).
- Hennessy, J.L., Patterson, D.A. *Computer Architecture: A Quantitative Approach*, 6th ed., Morgan Kaufmann, 2019, ch. 5 "Thread-Level Parallelism", §5.2 "Centralized Shared-Memory Architectures" — snooping coherence and the MESI/MOESI extensions (secondary source).
- Chipressian. *Crack the Hardware Interview - from RTL Designers' Perspective*, Part 1 ch. 6 "Cache Coherency" — snooping coherence (secondary source).
- `projects/components/cache-ip/References/AMBA_ACE_Interface_Definition.md` — working interface definition for this family
- Indexed in `rtl/amba/references/README.md` (local PDF: `LatencyInsensitiveDesign__Carloni2001.pdf`, `MoesiCoherenceClass__Sweazey1986.pdf`, `projects/components/cache-ip/References/Papamarcos_Patel_1984_ISCA_Snoopy_Coherence.pdf`, `projects/components/cache-ip/References/Sorin_Hill_Wood_2020_Primer_Memory_Consistency_Cache_Coherence_2ed.pdf`)

---

**Last Updated:** 2026-10-12

---

## Navigation

- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
