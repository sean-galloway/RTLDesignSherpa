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

# AXI5 (Advanced eXtensible Interface - AMBA 5) Modules

**Location:** `rtl/amba/axi5/`
**Test Location:** `val/amba/`
**Status:** Production Ready

---

## Overview

The AXI5 subsystem provides read/write master and slave channel modules for the ARM AMBA 5 AXI (Advanced eXtensible Interface) protocol, plus clock-gated variants and combined module+monitor variants for efficient system integration. Read *Scope of This Implementation* below before treating these as a full AXI5 protocol stack.

AXI5 extends AXI4 with significant enhancements for modern high-performance SoC designs, including atomic transactions, memory tagging, memory partitioning, and data poisoning.

---

## Scope of This Implementation

These modules are **channel-transport blocks**: they carry a full AXI5 signal set across configurable SKID buffers between a FUB (Functional Unit Block) interface and an external AXI5 interface. They are the AXI5 equivalents of the `axi4_master_*` / `axi4_slave_*` modules.

**What the RTL does:**

- Transports every implemented AXI5 sideband signal end-to-end without modification.
- Packs and unpacks channel payloads conditionally, so disabled features cost zero area.
- Provides a `busy` status output for clock gating and power management.

**What the RTL does not do:**

- It does not *execute* AXI5 semantics. `AWATOP` is transported, but no atomic read-modify-write is performed; `AxTAGOP`/`RTAG`/`WTAG` are transported, but no tag checking or `RTAGMATCH` generation is performed; chunk fields are transported, but no chunk reassembly is performed. Those behaviors belong to the endpoint (memory controller, interconnect, or FUB logic) on either side.
- It does not track or limit outstanding transactions. Depth is bounded by the endpoints, not by these modules.

Consult the per-module pages for the exact signal set each module carries.

---

## AXI5 Features Implemented

| AXI5 feature | Signals | Status in `rtl/amba/axi5/` |
|--------------|---------|----------------------------|
| Non-secure access identifier | ARNSAID / AWNSAID | Transported (`ENABLE_NSAID`) |
| Trace | ARTRACE / AWTRACE / RTRACE / BTRACE | Transported (`ENABLE_TRACE`) |
| Memory partitioning and monitoring (MPAM) | ARMPAM / AWMPAM | Transported (`ENABLE_MPAM`) |
| Memory encryption context | ARMECID / AWMECID | Transported (`ENABLE_MECID`) |
| Unique access indicator | ARUNIQUE / AWUNIQUE | Transported (`ENABLE_UNIQUE`) |
| Read data chunking | ARCHUNKEN / RCHUNKV / RCHUNKNUM / RCHUNKSTRB | Transported (`ENABLE_CHUNKING`, read path only) |
| Memory Tagging Extension (MTE) | ARTAGOP / AWTAGOP / AWTAG / WTAG / WTAGUPDATE / RTAG / BTAG / RTAGMATCH / BTAGMATCH | Transported (`ENABLE_MTE`) |
| Data poison | RPOISON / WPOISON | Transported (`ENABLE_POISON`) |
| Atomic transactions | AWATOP | Signal transported (`ENABLE_ATOMIC`); atomic execution is the endpoint's responsibility |

## AXI5 Features Not Implemented

| AXI5 feature | Signals | Notes |
|--------------|---------|-------|
| Loopback signalling | ARLOOP / AWLOOP | No ports; not carried |
| QoS acceptance | ARQOSACCEPT / AWQOSACCEPT | No ports; not carried |
| Untranslated transactions (SMMU) | AxMMUSID / AxMMUSSID / AxMMUSSIDV / AxMMUATST / AxMMUFLOW | No ports; not carried |
| Cache stash and CMO transactions | AWSTASHNID / AWSTASHLPID, CMO opcodes | Not implemented |
| Region identifier | ARREGION / AWREGION | Not implemented. AxREGION is still a valid optional AXI5 signal; it is simply omitted here. Route or decode by address instead |

---

## AXI4 vs AXI5

| Feature | AXI4 | AXI5 |
|---------|------|------|
| Outstanding transactions | No architectural limit; bounded by implementation | Unchanged; no architectural limit |
| Atomic transactions | Not supported | AWATOP: AtomicStore, AtomicLoad, AtomicSwap, AtomicCompare |
| Memory tagging | Not supported | MTE: AxTAGOP, AxTAG, WTAGUPDATE, RTAG/BTAG, xTAGMATCH |
| Security identification | ARPROT/AWPROT[1] non-secure bit | AxPROT retained, plus AxNSAID for finer-grained security domains |
| QoS | ARQOS/AWQOS | AxQOS retained, plus optional AxQOSACCEPT |
| Memory partitioning | Not supported | MPAM (PartID + PMG) |
| Encryption context | Not supported | MECID |
| Trace | Not supported | AxTRACE / RTRACE / BTRACE |
| Read data chunking | Not supported | ARCHUNKEN, RCHUNKV, RCHUNKNUM, RCHUNKSTRB |
| Data poison | Not supported | RPOISON, WPOISON |
| Region identifier | ARREGION/AWREGION (optional) | ARREGION/AWREGION retained (optional) |

---

## Module Categories

### Master Components

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axi5_master_rd** | AXI5 read master with skid buffers and burst support | [axi5_master_rd.md](axi5_master_rd.md) | Documented |
| **axi5_master_rd_cg** | Clock-gated AXI5 read master | [axi5_master_rd_cg.md](axi5_master_rd_cg.md) | Documented |
| **axi5_atomic_filter** | Read-return atomic termination (store-class passes, load-class DECERRs) | [axi5_atomic_filter.md](axi5_atomic_filter.md) | Documented |
| **axi5_master_wr** | AXI5 write master with address/data coordination | [axi5_master_wr.md](axi5_master_wr.md) | Documented |
| **axi5_master_wr_cg** | Clock-gated AXI5 write master | [axi5_master_wr_cg.md](axi5_master_wr_cg.md) | Documented |

### Slave Components

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axi5_slave_rd** | AXI5 read slave with configurable response handling | [axi5_slave_rd.md](axi5_slave_rd.md) | Documented |
| **axi5_slave_rd_cg** | Clock-gated AXI5 read slave | [axi5_slave_rd_cg.md](axi5_slave_rd_cg.md) | Documented |
| **axi5_slave_wr** | AXI5 write slave with write response generation | [axi5_slave_wr.md](axi5_slave_wr.md) | Documented |
| **axi5_slave_wr_cg** | Clock-gated AXI5 write slave | [axi5_slave_wr_cg.md](axi5_slave_wr_cg.md) | Documented |

### Monitor Components

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axi5_master_rd_mon** | AXI5 read master with integrated transaction monitor | [axi5_master_rd_mon.md](../axi5/axi5_master_rd_mon.md) | Documented |
| **axi5_master_rd_mon_cg** | Clock-gated read master with monitor | [axi5_master_rd_mon_cg.md](../axi5/axi5_master_rd_mon_cg.md) | Documented |
| **axi5_master_wr_mon** | AXI5 write master with integrated transaction monitor | [axi5_master_wr_mon.md](../axi5/axi5_master_wr_mon.md) | Documented |
| **axi5_master_wr_mon_cg** | Clock-gated write master with monitor | [axi5_master_wr_mon_cg.md](../axi5/axi5_master_wr_mon_cg.md) | Documented |
| **axi5_slave_rd_mon** | AXI5 read slave with integrated transaction monitor | [axi5_slave_rd_mon.md](../axi5/axi5_slave_rd_mon.md) | Documented |
| **axi5_slave_rd_mon_cg** | Clock-gated read slave with monitor | [axi5_slave_rd_mon_cg.md](../axi5/axi5_slave_rd_mon_cg.md) | Documented |
| **axi5_slave_wr_mon** | AXI5 write slave with integrated transaction monitor | [axi5_slave_wr_mon.md](../axi5/axi5_slave_wr_mon.md) | Documented |
| **axi5_slave_wr_mon_cg** | Clock-gated write slave with monitor | [axi5_slave_wr_mon_cg.md](../axi5/axi5_slave_wr_mon_cg.md) | Documented |

---

## Key Features

### AXI5 Channel Support
- **Full AXI5 signal set** for the features listed in *AXI5 Features Implemented* above
- **Burst types:** INCR, FIXED, and WRAP transported unmodified
- **ID transport:** Full `AXI_ID_WIDTH` transaction IDs; ordering and reordering are left to the endpoints
- **Transaction depth:** Not limited by these modules; set by the endpoints
- **Atomic transactions:** AWATOP transported for AtomicStore, AtomicLoad, AtomicSwap, and AtomicCompare

### Advanced Features
- **Memory Tagging (MTE):** AxTAGOP, AxTAG, WTAGUPDATE, RTAG/BTAG, xTAGMATCH
- **Memory partitioning:** MPAM (PartID + PMG) and MECID encryption context
- **Poison support:** RPOISON/WPOISON for error propagation
- **Chunking:** ARCHUNKEN and the RCHUNK* response fields on the read path

### Power Management
- **Clock Gating:** Per-module clock gating for power reduction
- **Idle Detection:** Automatic clock gate when interface is idle
- **Low-Power Modes:** Support for system low-power state integration

### Monitoring and Debug
- **Integrated Monitors:** Combined master/slave + monitor modules
- **Transaction Tracking:** Complete transaction lifecycle monitoring
- **Performance Metrics:** Bandwidth, latency, and utilization
- **64-bit Monitor Bus:** Standardized packet format

---

## Quick Start

The examples below are abbreviated: `.m_axi_ar*` style wildcards stand in for the full port list, and the AXI5 sideband ports are omitted for brevity. All AXI5 sideband ports exist on the module unconditionally — the `ENABLE_*` parameters control whether a signal is packed through the SKID buffer, not whether the port is present — so a real instantiation must connect or explicitly tie off every one of them. See the per-module pages for complete, connect-every-port examples.

### Using AXI5 Read Master

```systemverilog
axi5_master_rd #(
    .SKID_DEPTH_AR(2),
    .SKID_DEPTH_R(4),
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(64),
    .AXI_DATA_WIDTH(128),
    .AXI_USER_WIDTH(4)
) u_axi5_rd_master (
    .aclk               (clk),
    .aresetn            (resetn),

    // FUB (Functional Unit Block) interface
    .fub_axi_arid       (fub_arid),
    .fub_axi_araddr     (fub_araddr),
    .fub_axi_arlen      (fub_arlen),
    .fub_axi_arsize     (fub_arsize),
    .fub_axi_arburst    (fub_arburst),
    .fub_axi_arlock     (fub_arlock),
    .fub_axi_arcache    (fub_arcache),
    .fub_axi_arprot     (fub_arprot),
    .fub_axi_arqos      (fub_arqos),
    .fub_axi_aruser     (fub_aruser),
    .fub_axi_arvalid    (fub_arvalid),
    .fub_axi_arready    (fub_arready),

    .fub_axi_rid        (fub_rid),
    .fub_axi_rdata      (fub_rdata),
    .fub_axi_rresp      (fub_rresp),
    .fub_axi_rlast      (fub_rlast),
    .fub_axi_ruser      (fub_ruser),
    .fub_axi_rvalid     (fub_rvalid),
    .fub_axi_rready     (fub_rready),

    // AXI5 master interface
    .m_axi_ar*          (mem_ar*),
    .m_axi_r*           (mem_r*)
);
```

### Using AXI5 Write Master

```systemverilog
axi5_master_wr #(
    .SKID_DEPTH_AW(2),
    .SKID_DEPTH_W(4),
    .SKID_DEPTH_B(2),
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(64),
    .AXI_DATA_WIDTH(128),
    .AXI_USER_WIDTH(4)
) u_axi5_wr_master (
    .aclk               (clk),
    .aresetn            (resetn),

    // FUB interface
    .fub_axi_awid       (fub_awid),
    .fub_axi_awaddr     (fub_awaddr),
    .fub_axi_awlen      (fub_awlen),
    .fub_axi_awsize     (fub_awsize),
    .fub_axi_awburst    (fub_awburst),
    .fub_axi_awlock     (fub_awlock),
    .fub_axi_awcache    (fub_awcache),
    .fub_axi_awprot     (fub_awprot),
    .fub_axi_awqos      (fub_awqos),
    .fub_axi_awuser     (fub_awuser),
    .fub_axi_awvalid    (fub_awvalid),
    .fub_axi_awready    (fub_awready),

    .fub_axi_wdata      (fub_wdata),
    .fub_axi_wstrb      (fub_wstrb),
    .fub_axi_wlast      (fub_wlast),
    .fub_axi_wuser      (fub_wuser),
    .fub_axi_wvalid     (fub_wvalid),
    .fub_axi_wready     (fub_wready),

    .fub_axi_bid        (fub_bid),
    .fub_axi_bresp      (fub_bresp),
    .fub_axi_buser      (fub_buser),
    .fub_axi_bvalid     (fub_bvalid),
    .fub_axi_bready     (fub_bready),

    // AXI5 master interface
    .m_axi_aw*          (mem_aw*),
    .m_axi_w*           (mem_w*),
    .m_axi_b*           (mem_b*)
);
```

### Using Integrated Monitor Modules

```systemverilog
// AXI5 master with built-in transaction monitoring
axi5_master_rd_mon #(
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(64),
    .AXI_DATA_WIDTH(128)
) u_axi5_rd_master_mon (
    .aclk               (clk),
    .aresetn            (resetn),

    // FUB and AXI interfaces (same as non-monitor version)
    .fub_axi_ar*        (...),
    .fub_axi_r*         (...),
    .m_axi_ar*          (...),
    .m_axi_r*           (...),

    // Monitor bus output
    .mon_valid          (rd_mon_valid),
    .mon_ready          (rd_mon_ready),
    .mon_data           (rd_mon_data)
);
```

---

## Testing

All AXI5 modules are verified using CocoTB-based testbenches located in `val/amba/`:

```bash
# Run all AXI5 tests
pytest val/amba/test_axi5*.py -v

# Run specific module tests
pytest val/amba/test_axi5_master_rd.py -v
pytest val/amba/test_axi5_master_wr.py -v
pytest val/amba/test_axi5_slave_rd.py -v
pytest val/amba/test_axi5_slave_wr.py -v
```

---

## Protocol Details

### AXI5 Channel Overview

AXI5 maintains the five-channel architecture from AXI4:

| Channel | Direction | Purpose |
|---------|-----------|---------|
| AR (Address Read) | Master to Slave | Read address and control |
| R (Read Data) | Slave to Master | Read data and response |
| AW (Address Write) | Master to Slave | Write address and control |
| W (Write Data) | Master to Slave | Write data |
| B (Write Response) | Slave to Master | Write response |

### AXI5 Sideband Signals Carried by These Modules

| Signal | Channel | Description |
|--------|---------|-------------|
| AWATOP | AW | Atomic transaction type (see `axi5_master_wr.md` for the encoding) |
| ARNSAID / AWNSAID | AR / AW | Non-secure access identifier |
| ARTRACE / AWTRACE | AR / AW | Request trace marker |
| ARMPAM / AWMPAM | AR / AW | Memory partitioning and monitoring (PartID + PMG) |
| ARMECID / AWMECID | AR / AW | Memory encryption context identifier |
| ARUNIQUE / AWUNIQUE | AR / AW | Unique access indicator |
| ARCHUNKEN | AR | Read data chunking enable |
| ARTAGOP / AWTAGOP | AR / AW | MTE tag operation |
| AWTAG | AW | MTE address tags |
| WPOISON | W | Write data poisoned indicator |
| WTAG / WTAGUPDATE | W | MTE write data tags and update mask |
| RPOISON | R | Read data poisoned indicator |
| RTRACE / BTRACE | R / B | Response trace marker |
| RCHUNKV / RCHUNKNUM / RCHUNKSTRB | R | Read chunk valid, number, and strobe |
| RTAG / BTAG | R / B | MTE response tags |
| RTAGMATCH / BTAGMATCH | R / B | MTE tag match result |

Signals absent from this list (ARLOOP/AWLOOP, ARQOSACCEPT/AWQOSACCEPT, ARREGION/AWREGION, the SMMU `AxMMU*` group, and stash/CMO encodings) have no ports on these modules. See *AXI5 Features Not Implemented* above.

### Burst Types

| ARBURST/AWBURST | Type | Description |
|-----------------|------|-------------|
| 2'b00 | FIXED | Fixed address for FIFO access |
| 2'b01 | INCR | Incrementing address burst |
| 2'b10 | WRAP | Wrapping burst for cache line |
| 2'b11 | Reserved | Not used |

---

## Design Notes

### FUB Interface Pattern

All AXI5 modules use the FUB (Functional Unit Block) interface pattern:
- **fub_axi_*** signals connect to internal logic
- **m_axi_*** or **s_axi_*** signals connect to external AXI bus
- Skid buffers between FUB and external interfaces for timing closure

### Migration from AXI4

These modules carry an AXI4-compatible core signal set, so an AXI4 agent can drive them:
- Core protocol unchanged (5-channel architecture)
- Every AXI5 sideband port can be tied off to its default value, and the matching `ENABLE_*` parameter set to 0 so the field costs no SKID buffer area
- AWATOP tied to `6'b000000` (NonAtomic) makes every write a normal AXI4 write
- User signal widths can match AXI4 configurations
- **Exception:** AXI4's ARREGION/AWREGION have no port here. An AXI4 agent that relies on AxREGION must decode by address instead, or use the `axi4_master_*` / `axi4_slave_*` modules

### Monitor Integration

The `*_mon` variants combine master/slave with integrated monitor:
- Single instantiation for both data path and monitoring
- Shared clock and reset
- Monitor bus output for transaction visibility
- Reduced resource usage vs. separate monitor instantiation

---

## Performance Characteristics

These modules are SKID-buffer pipelines, so their cost is a small, fixed latency adder and their throughput ceiling is simply the bus bandwidth. No synthesis has been run against a specific ASIC node; the frequency figure below is an FPGA-oriented design target, not a signed-off characterization result.

| Metric | Value |
|--------|-------|
| Maximum frequency | Design target; not characterized against a specific technology node |
| Added latency (per channel) | 1 clock cycle per SKID stage |
| Throughput | One beat per clock, sustained (`AXI_DATA_WIDTH` bits/cycle) |
| Peak bandwidth, 128-bit bus at 500 MHz | 8 GB/s per direction |
| Outstanding transactions | Not limited by these modules; bounded by the endpoints |

---

## Related Documentation

- **[AXI4 Modules](../axi4/README.md)** - AXI4 protocol components
- **[APB5 Modules](../apb5/README.md)** - APB5 protocol components
- **[AXIS5 Modules](../axis5/README.md)** - AXI5-Stream components
- **[GAXI Modules](../gaxi/README.md)** - Generic AXI utilities
- **[Shared Infrastructure](../shared/README.md)** - Common components

---

## References

### Specifications
- ARM AMBA 5 AXI Protocol Specification
- ARM AMBA AXI and ACE Protocol Specification (AXI4)

### Source Code
- RTL: `rtl/amba/axi5/`
- Tests: `val/amba/test_axi5*.py`
- Framework: `bin/TBClasses/components/axi4/`

---

**Last Updated:** 2026-07-19

---

## Navigation

- **[Back to rtl-amba Index](../index.md)**
- **[Back to Main Documentation Index](../../index.md)**
