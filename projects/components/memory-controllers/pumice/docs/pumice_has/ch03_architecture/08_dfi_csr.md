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

# DFI Master and CSR Slave

The two final modules in the controller hierarchy: `dfi_master` (final DFI signal aggregation) and `csr_slave` (APB3 configuration interface).

## `dfi_master`

### Purpose

Aggregate command, write-data, read-data, and init-control signals into the final DFI v2.1 signal set. Tie off the unused DFI sub-interfaces to their idle values. Provide a single point of contact with the PHY for clean integration.

### Sub-Interfaces Driven

This controller drives only the three core DFI sub-interfaces required for v2.1 LPDDR2 operation:

- **Command Interface** (MC → PHY): all command-bus signals
- **Write Data Interface** (MC → PHY): `wrdata`, `wrdata_en`, `wrdata_mask`
- **Read Data Interface** (MC ↔ PHY): `rddata`, `rddata_valid`, `rddata_en`, and LPDDR2's `rddata_dnv`

### Sub-Interfaces Tied Idle

The remaining DFI v2.1 sub-interfaces are present in the port list (for ABI compatibility) but driven to their idle values:

- **Status Interface** — only `init_complete` is consumed; others tied off
- **Update Interface** — MC drives `ctrlupd_req = 0`; PHY's `phyupd_req` is acked but no action taken
- **Training Interface** — held idle; no training in DDR2 / LPDDR2
- **Low Power Control Interface** — held idle; we use CKE-based power management directly

This means the controller is compatible with PHYs that support full DFI v2.1 but doesn't require them to.

### Signal Aggregation

All per-phase signals from `cmd_encoder` (through `gear_out`), `wdata_path`, and `rdata_path` arrive at `dfi_master` and are routed to the appropriate output ports. The module is essentially a wiring stub plus tie-offs.

### Why a Dedicated Module

Putting the tie-offs in a single module keeps the rest of the controller PHY-detail-free. If we later need to enable a sub-interface (e.g., the training interface for a real PHY that requires it), the change is localized.

---

## `csr_slave`

### Purpose

APB3 slave for configuration and observation. All controller parameters that need to be programmable at runtime (rather than build time) are exposed here.

### Bus Protocol

Standard APB3 slave. Signals:

| Signal       | Width | Direction | Purpose                                       |
|--------------|-------|-----------|-----------------------------------------------|
| `psel`       | 1     | input     | Slave selected by APB master                  |
| `penable`    | 1     | input     | Access phase 2 (data transfer)                |
| `pwrite`     | 1     | input     | Write (1) or read (0)                         |
| `paddr`      | 12    | input     | Address (4 KB region)                         |
| `pwdata`     | 32    | input     | Write data                                    |
| `prdata`     | 32    | output    | Read data                                     |
| `pready`     | 1     | output    | Slave ready to complete                       |
| `pslverr`    | 1     | output    | Error response                                |

### Address Map Overview

A 4 KB region with the following high-level partitioning:

| Range            | Purpose                                       |
|------------------|-----------------------------------------------|
| `0x000` – `0x00F` | Top-level control and status                 |
| `0x010` – `0x01F` | Packed timing parameters                     |
| `0x020` – `0x02F` | Mode-register configuration values           |
| `0x030` – `0x03F` | LPDDR2-specific (PASR, etc.)                 |
| `0x040` – `0x04F` | Scheduler / refresh / page-policy tuning     |
| `0x080` – `0x0FF` | Per-bank observation counters                |
| `0x100` – `0x1FF` | System-wide observation counters             |
| `0xFF0` – `0xFFC` | Module identification                        |

The full register map is documented in Section 6.3.

### Clock Domain Crossing

The CSR slave runs on `apb_pclk`, which is independent of `mc_clk`. A 2-flop synchronizer with handshake protocol crosses configuration writes into the `mc_clk` domain. The handshake guarantees atomic register update from the controller's perspective.

### Read Latency

APB read latency is implementation-defined. This slave uses single-cycle reads for control / status registers (the `paddr ≤ 0x07F` range) and 2-cycle reads for observation counters (which require CDC of the live counter value into the APB domain). `pready` deasserts during the second cycle of an observation-counter read.

### Configuration Quiet Period

Certain parameters (e.g., MR values, timings) can only take effect during a "quiet period" — when no DRAM commands are in flight. The CSR slave does not enforce quiet-period writes; the SoC is responsible for sequencing. Writing during normal operation may cause subtle protocol violations.

### Recommended Programming Sequence

1. Hold `mc_rstn` asserted.
2. Program all timing parameters and MR values via CSR.
3. Configure PASR mask (LPDDR2 only).
4. Configure characterization parameters (`PAGE_POLICY` runtime override, `REFPB_POLICY` runtime override, etc.).
5. Release `mc_rstn`.
6. Wait for `STATUS.init_done == 1`.
7. Begin AXI traffic.

Skipping CSR programming uses the build-time defaults, which are conservative (HAPPY_HYBRID for LPDDR2 page policy, DARP for REFPB policy).
