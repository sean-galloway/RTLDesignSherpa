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

# 3.16 AXI3 to AXI4 Converter

The **axi3_to_axi4** converter family bridges an AXI3 master to an AXI4 slave. It is the complement of the AXI4-to-AXI3 converter and is used on the DE10 leg-bridge `h2f_axi_master` seam when traffic flows from the AXI3 hard processor subsystem toward AXI4 fabric logic.

## 3.16.1 Module Organization

```
axi3_to_axi4.sv          # Full bidirectional wrapper
├── axi3_to_axi4_rd.sv   # Read path: AR/R qualifier mapping
└── axi3_to_axi4_wr.sv   # Write path: AW/W/B with WID stripping
```

As with the opposite direction, read and write are independent modules for selective instantiation and targeted verification.

## 3.16.2 Protocol Deltas

| Aspect | AXI3 (slave side) | AXI4 (master side) | Converter action |
| --- | --- | --- | --- |
| `AxLEN` width | 4 bits (1–16 beats) | 8 bits (1–256 beats) | Zero-extend `AxLEN` (`{4'b0, s_axi3_axlen}`). No chopping needed. |
| `AxLOCK` | 2 bits (`2'b00` normal, `2'b10` exclusive) | 1 bit (normal / exclusive) | Map `2'b10 → 1'b1`, all other values → `1'b0`. |
| Write data ID | `WID` per beat | None | Strip `WID`; AXI4 W has no ID concept. |
| `QoS` / `REGION` | Absent | Present on AW/AR | Drive to zero. |
| Data width | Must match | Must match | No width conversion. |

: Table 3.49: AXI3 to AXI4 protocol differences

### Exclusive-access caveat

The DE10 leg-bridge `h2f_axi_master` seam does not support AXI exclusive accesses. The converter maps an AXI3 exclusive request (`AxLOCK = 2'b10`) to the AXI4 encoding (`AxLOCK = 1'b1`), but an AXI3 locked transaction (`AxLOCK = 2'b01`) is collapsed to normal (`AxLOCK = 1'b0`) because the HPS interface does not implement locked-transaction semantics.

## 3.16.3 Read Path (axi3_to_axi4_rd)

The read path is a straight qualifier mapping block:

* `ARID`, `ARADDR`, `ARSIZE`, `ARBURST`, `ARCACHE`, `ARPROT`, and `ARUSER` pass through unchanged.
* `ARLEN` is zero-extended from 4 bits to 8 bits.
* `ARLOCK` is mapped from AXI3 2-bit encoding to AXI4 1-bit encoding.
* `ARQOS` and `ARREGION` are driven to `4'b0`.
* The R channel passes through unchanged (`RID`, `RDATA`, `RRESP`, `RLAST`, `RUSER`).

No burst chopping is required because AXI3 bursts are already bounded to 16 beats, which fits comfortably in a single AXI4 transaction.

## 3.16.4 Write Path (axi3_to_axi4_wr)

### Operation

The write path maps the AXI3 AW/W/B channels to AXI4:

* `AWID`, `AWADDR`, `AWSIZE`, `AWBURST`, `AWCACHE`, `AWPROT`, and `AWUSER` pass through.
* `AWLEN` is zero-extended from 4 bits to 8 bits.
* `AWLOCK` is mapped from 2-bit AXI3 to 1-bit AXI4.
* `AWQOS` and `AWREGION` are driven to `4'b0`.
* `WID` is stripped; the AXI4 W channel has no ID.
* `WDATA`, `WSTRB`, `WLAST`, and `WUSER` pass through.
* B channel (`BID`, `BRESP`, `BUSER`) passes through.

### Single-Active-Write Contract

`axi3_to_axi4_wr` enforces exactly one outstanding write transaction at a time:

* `s_axi3_awready` is gated by `!active`, where `active` is set on AW handshake and cleared on B handshake.
* `s_axi3_wready`, `m_axi_wvalid`, `s_axi3_bvalid`, and `m_axi_bready` are all qualified by `active`.

This is a deliberate simplification. AXI3 allows write-data interleaving, but supporting it would require demuxing W beats by `WID` before presenting them to AXI4; the converter instead requires the upstream AXI3 master to present one complete write transaction at a time.

### WID Stability Assertion

Because the converter relies on a single active AWID, it asserts `ASSERT_A3_WID_STABLE` if `s_axi3_wid` changes mid-burst or differs from the active `AWID`. This is enforced by a simulation assertion, and a dedicated negative test (`test_axi3_to_axi4_wr_wid_mismatch`) verifies that the assertion fires.

## 3.16.5 Bidirectional Wrapper (axi3_to_axi4)

The top wrapper instantiates the read and write converters, ties off the AXI4-only `QOS`/`REGION` outputs to zero, and exposes the union of both submodule port lists. No additional protocol logic is present in the wrapper.

## 3.16.6 Parameters

| Parameter | Type | Default | Description |
| --- | --- | --- | --- |
| AXI_ID_WIDTH | int | 8 | Transaction ID width (1–16). |
| AXI_ADDR_WIDTH | int | 32 | Address width (12–64). |
| AXI_DATA_WIDTH | int | 32 | Data width; must match on both sides (32/64/128/256). |
| AXI_USER_WIDTH | int | 1 | User-signal width (0–1024). |

: Table 3.50: AXI3 to AXI4 parameters

## 3.16.7 Non-goals

The following features are intentionally outside the scope of this converter:

* **Interleaved W IDs.** Only one outstanding write transaction is accepted; interleaved W data from different IDs is rejected by `ASSERT_A3_WID_STABLE`.
* **Data-width conversion.** `AXI_DATA_WIDTH` must be identical on both sides.
* **QoS / REGION generation.** These AXI4-only qualifiers are driven to zero.

## 3.16.8 Resource Utilization

| Module | Registers | LUTs | BRAM |
| --- | --- | --- | --- |
| axi3_to_axi4_rd | ~20 | ~30 | 0 |
| axi3_to_axi4_wr | ~40 | ~50 | 0 |
| axi3_to_axi4 (combined) | ~60 | ~80 | 0 |

: Table 3.51: AXI3 to AXI4 resources

The tables are approximate hand estimates; no post-route characterization has been run.

## 3.16.9 Testing

**Test Suite:** `test_axi3_to_axi4_rd.py`, `test_axi3_to_axi4_wr.py`, `test_axi3_to_axi4.py`, `test_axi3_loopback.py`.

| Test Category | Coverage | Status |
| --- | --- | --- |
| Single-beat read | Pass-through, ARLEN zero-extension, ARLOCK mapping | Pass |
| Burst read ≤ 16 beats | Pass-through, RID/RRESP/RLAST integrity | Pass |
| Single-beat write | Pass-through, WID strip | Pass |
| Burst write ≤ 16 beats | WLAST/B pass-through | Pass |
| Single-active-write backpressure | Second AW held off until B accepted | Pass |
| WID mismatch negative test | `ASSERT_A3_WID_STABLE` fires on wrong WID | Pass |
| Loopback equivalence | `axi4_to_axi3 → axi3_to_axi4` identity for legal AXI4 traffic | Pass |

: Table 3.52: AXI3 to AXI4 test coverage

---

**Next:** [Verification](../ch05_verification/01_test_strategy.md)

## References

* ARM, *AMBA 3 AXI Protocol Specification*, ARM IHI 0022 — verified against this spec for AXI3-specific behavior: 4-bit `AxLEN`, 2-bit `AxLOCK`, write-data `WID`, and absence of `QoS`/`REGION`.
* ARM, *AMBA AXI and ACE Protocol Specification*, ARM IHI 0022E — verified against this spec for AXI4-specific behavior: 8-bit `AxLEN`, 1-bit `AxLOCK`, no `WID`, and `QoS`/`REGION` qualifiers.
