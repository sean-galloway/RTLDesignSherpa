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

# amber_snoop_resp: Snoop Responder Adapter

**Module:** `amber_snoop_resp.sv`
**Location:** `projects/components/cache-ip/amber-mesi-l1/rtl/fub/`
**Status:** RTL landed 2026-10-06; this chapter is the contract the RTL
implements. Wraps the house `axi4ace_snoop_slave` transport (which exists in
`rtl/amba/ace` — confirmed). DV: `dv/tests/fub/test_amber_snoop_resp.py`,
green at gate/func/full on both geometries; the FULL level is a 3000-snoop
randomized soak over an evolving line-state model with per-transaction ACE
compliance checks, not a token rerun.

---

## Overview

`amber_snoop_resp` is the ACE-shaped snoop responder. It wraps the house `axi4ace_snoop_slave` module and adds the small state machine that sequences CR and CD for each snoop transaction. Inside `amber_core` the snoop is bus-agnostic; only `amber_snoop_resp` speaks ACE.

---

## External Interface

The external side is the standard `axi4ace_snoop_slave` port:

| Signal | Direction | Width | Purpose |
|--------|-----------|-------|---------|
| `m_axi_acaddr` | input | `ADDR_WIDTH` | Snoop address |
| `m_axi_acsnoop` | input | 4 | Snoop type |
| `m_axi_acprot` | input | 3 | Snoop protection |
| `m_axi_acvalid` | input | 1 | AC valid |
| `m_axi_acready` | output | 1 | AC ready |
| `m_axi_crresp` | output | 5 | CR response |
| `m_axi_crvalid` | output | 1 | CR valid |
| `m_axi_crready` | input | 1 | CR ready |
| `m_axi_cddata` | output | `DATA_WIDTH` | CD data |
| `m_axi_cdlast` | output | 1 | CD last |
| `m_axi_cdvalid` | output | 1 | CD valid |
| `m_axi_cdready` | input | 1 | CD ready |

## Internal Interface

The core-facing side is a bus-agnostic handshake:

| Signal | Direction | Meaning |
|--------|-----------|---------|
| `ctrl_snoop_req` | output to `amber_control` | Valid snoop address + type. |
| `ctrl_snoop_addr` | output | Snoop line address. |
| `ctrl_snoop_type` | output | Encoded snoop type. |
| `ctrl_snoop_ready` | input from `amber_control` | Control accepts snoop. |
| `ctrl_crresp` | input from `amber_control` | 5-bit response. |
| `ctrl_cddata` | input from `amber_control` | CD beat data. |
| `ctrl_cdlast` | input from `amber_control` | CD last beat. |
| `ctrl_cdvalid` | input from `amber_control` | CD beat valid. |
| `ctrl_cdready` | output to `amber_control` | Adapter ready for CD beat. |

---

## Adapter State Machine

| State | Meaning |
|-------|---------|
| `SR_IDLE` | Waiting for AC handshake. |
| `SR_LOOKUP` | Snoop accepted; waiting for `amber_control` CRRESP. |
| `SR_DATA` | Driving CD beats. |
| `SR_RESP` | Driving CR after CDLAST. |

### State transitions

1. `SR_IDLE` → `SR_LOOKUP`: AC handshake completes (`m_axi_acvalid && m_axi_acready`).
2. `SR_LOOKUP` → `SR_DATA`: `amber_control` returns `ctrl_crresp` and `CRRESP.DataTransfer` is 1.
3. `SR_LOOKUP` → `SR_RESP`: `amber_control` returns `ctrl_crresp` and `CRRESP.DataTransfer` is 0.
4. `SR_DATA` → `SR_RESP`: Last CD beat accepted (`m_axi_cdvalid && m_axi_cdready && m_axi_cdlast`).
5. `SR_RESP` → `SR_IDLE`: CR handshake completes (`m_axi_crvalid && m_axi_crready`).

---

## CR-after-CDLAST Ordering

amber strengthens the protocol by completing all CD beats before asserting CR. This matches:

- IHI0022: the snoop response is required only after the final CD beat.
- The cocotb-framework 1.2.0 ACE compliance checker (`check_cr_order` / `check_cd_order`).
- The family convention recorded with onyx D4.

The CR channel is held low while the adapter is in `SR_DATA`. This makes the gather logic simple: one closed response at a time.

---

## Snoop Type Decoding

`m_axi_acsnoop` carries the six IHI0022 snoop encodings used by amber:

| Encoding | Type |
|----------|------|
| `ReadShared` | Shared read snoop |
| `ReadOnce` | Single read snoop |
| `ReadUnique` | Exclusive read snoop |
| `CleanShared` | Clean shared snoop |
| `CleanInvalid` | Clean invalidate snoop |
| `MakeInvalid` | Invalidate snoop |

`CleanUnique` and `MakeUnique` are transactions a master issues, not snoop encodings, so they do not appear on the AC channel. The CRRESP bits for each {state, snoop} pair are the authority of the HAS Table 3.0 and are captured as K-maps in the workbook.

---

**Last Updated:** 2026-10-06
