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

# amber_ace_issue: Coherent Transaction Mapping

**Module:** `amber_ace_issue.sv`
**Location:** `projects/components/cache-ip/amber-mesi-l1/rtl/fub/`
**Status:** Pre-RTL micro-architecture contract

---

## Overview

`amber_ace_issue` maps cache-side events to the onyx D2 coherent-transaction subset. It lives only in the `amber_ace` rig; the pair-rig `amber` top does not instantiate it. The module sits between `amber_control` / `amber_fill` / `amber_drain` and the `axi4ace_master_rd` / `axi4ace_master_wr` wrappers.

---

## Event-to-Transaction Mapping

| Cache event | ACE transaction | Snoop field | Notes |
|---|---|---|---|
| Read miss, shared intent | `ReadShared` | `fub_axi_arsnoop[3:0]` | Line will be installed in S. |
| Read miss, exclusive intent | `ReadUnique` | `fub_axi_arsnoop[3:0]` | Line will be installed in E. |
| Write to Shared line | `CleanUnique` | `fub_axi_awsnoop[2:0]` | Upgrades S → M without data transfer. |
| Write to Invalid line (whole line) | `MakeUnique` | `fub_axi_awsnoop[2:0]` | Invalidates other copies; line installed in M. |
| Dirty eviction | `WriteBack` | `fub_axi_awsnoop[2:0]` | Whole-line write-back with data. |
| Clean eviction | `Evict` | `fub_axi_awsnoop[2:0]` | No data; notifies interconnect. |

: Table 2.8.1: Cache events to ACE transactions

---

## Interface

### From amber_control / fill / drain

| Signal | Direction | Meaning |
|--------|-----------|---------|
| `ace_rd_req` | input | Read transaction request. |
| `ace_rd_type` | input | Encoded event type (shared read / unique read). |
| `ace_rd_addr` | input | Line-aligned address. |
| `ace_rd_len` | input | Burst length. |
| `ace_wr_req` | input | Write transaction request. |
| `ace_wr_type` | input | Encoded event type (CleanUnique / MakeUnique / WriteBack / Evict). |
| `ace_wr_addr` | input | Line-aligned address. |
| `ace_wr_len` | input | Burst length. |

### To axi4ace_master_rd / axi4ace_master_wr

`amber_ace_issue` drives the `fub_axi_*` ports of the ACE master wrappers. It supplies `arsnoop`/`awsnoop` and the standard AXI address/data fields. The wrappers auto-pulse `RACK`/`WACK`.

---

## CleanUnique / MakeUnique Data Behavior

- `CleanUnique` is an AW-only transaction (no W data). It tells the interconnect to invalidate other copies so the local write can proceed. `amber_control` performs the actual data write into `amber_data_array` and promotes the line to M.
- `MakeUnique` is also an AW-only transaction for the full-line case. It invalidates other copies and grants exclusive ownership; the local line is installed or promoted to M.
- `WriteBack` is an AW+W burst with the dirty victim data.
- `Evict` is an AW-only transaction with no data.

---

## Timing

`amber_ace_issue` is combinational for address/snoop mapping. It does not add pipeline stages; the timing path is from `amber_control` through this module into the `axi4ace_master_*` skid buffers.

---

**Last Updated:** 2026-10-06
