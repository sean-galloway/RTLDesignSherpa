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

# 3.15 AXI4 to AXI3 Converter

The **axi4_to_axi3** converter family bridges an AXI4 master to an AXI3 slave. The first customer is the DE10 leg-bridge `f2h` seam, where the programmable-logic fabric speaks AXI4 and the hard processor subsystem presents an AXI3 interface.

## 3.15.1 Module Organization

```
axi4_to_axi3.sv          # Full bidirectional wrapper
├── axi4_to_axi3_rd.sv   # Read path: AR/R with burst chopping and response merge
└── axi4_to_axi3_wr.sv   # Write path: AW/W/B with WID stamping and B merge
```

Read and write are split into independent modules so a user can instantiate only the path that is needed and so verification can target each path separately.

## 3.15.2 Protocol Deltas

| Aspect | AXI4 (slave side) | AXI3 (master side) | Converter action |
| --- | --- | --- | --- |
| `AxLEN` width | 8 bits (1–256 beats) | 4 bits (1–16 beats) | Chop long bursts into ≤16-beat chunks; truncate `AxLEN` per chunk. |
| `AxLOCK` | 1 bit (normal / exclusive) | 2 bits (`2'b00` normal, `2'b01` exclusive, `2'b10` locked) | Map `1'b0 → 2'b00`, `1'b1 → 2'b01`. AXI4 cannot express locked; none is generated. |
| Write data ID | None | `WID` per beat | Stamp every AXI3 W beat with the owning AWID. |
| `QoS` / `REGION` | Present on AW/AR | Absent | Drop silently. |
| Data width | Must match | Must match | No width conversion. |

: Table 3.45: AXI4 to AXI3 protocol differences

### Exclusive-access caveat

The DE10 leg-bridge `f2h` seam is not expected to exercise AXI exclusive accesses. The converter still maps an AXI4 exclusive request (`AxLOCK = 1'b1`) to the AXI3 exclusive encoding (`2'b01`, per ARM IHI 0022), but the upstream system does not implement exclusive-monitor semantics at this boundary. If a legacy AXI3 locked (`2'b10`) transaction arrives on a downstream return path, it is treated as a normal access. (The encoding was swapped — exclusive emitted as `2'b10` — until bridge GitHub #98; the RTL, this table, and the directed lock-map DV now agree with the ARM encoding.)

## 3.15.3 Read Path (axi4_to_axi3_rd)

### Operation

The read path accepts an AXI4 AR burst and issues one or more AXI3 AR bursts:

* **Single-beat and short bursts** (`ARLEN ≤ 15`) pass through with only field-width changes.
* **Long bursts** (`ARLEN ≥ 16`) are chopped into sequential AXI3 bursts of up to 16 beats each.
* Returning R beats are streamed back to the AXI4 master with `RLAST` suppressed on every chunk except the last, so the master sees one logical burst.
* `RRESP` from all chunks is merged using worst-rank order (`OKAY < EXOKAY < SLVERR < DECERR`); the merged value is driven on the final beat of the reconstructed burst.

### Per-ID Merge Isolation

Each transaction ID has its own outstanding-chunk counter and worst-response accumulator. This keeps concurrent chopped bursts from different IDs from crossing: a late R beat on ID *M* cannot corrupt the merge state for ID *N*.

### Address Advance

For `INCR` bursts the start address of chunk *n+1* is computed from the previous chunk's start address plus `chunk_beats << size`. `FIXED` bursts reuse the same address for every chunk; `WRAP` bursts longer than 16 beats are unsupported (see 3.15.7 Non-goals).

## 3.15.4 Write Path (axi4_to_axi3_wr)

### Operation

The write path mirrors the read path on AW/W/B:

* AW bursts longer than 16 beats are chopped into multiple AXI3 AW bursts.
* Each AXI3 W beat is stamped with the owning AWID on `m_axi3_wid`.
* `WLAST` is forced at the end of every chopped chunk, producing a legal AXI3 WLAST for each sub-burst.
* Per-chunk B responses are merged worst-rank and returned as a single `s_axi_bresp` after the last chunk's B.

### Early-W Buffering

AXI4 allows W to arrive before AW. The converter buffers up to 16 full W beats ahead of the matching AW handshake. When the buffer is full, `s_axi_wready` is deasserted, which is the legal AXI4 mechanism for throttling early write data.

The write segmenter consumes the buffered beats using a chunk-descriptor FIFO pushed at AW acceptance. The descriptor carries the chunk's AWID and beat count, so WID and WLAST can be generated even for beats that arrived before the AW.

### Single-Active-Write Contract

The same AWID cannot have two outstanding bursts in flight at the same time: `s_axi_awready` is deasserted for an ID from the acceptance of its AW until the final merged B for that ID is accepted. Different IDs remain concurrent, and the read path is fully pipelined independently.

## 3.15.5 Bidirectional Wrapper (axi4_to_axi3)

The top wrapper instantiates the read and write converters, routes the clock and reset, and exposes the union of both submodule port lists: a full AXI4 slave interface and a full AXI3 master interface. The wrapper adds no logic beyond the submodule instantiations.

## 3.15.6 Parameters

| Parameter | Type | Default | Description |
| --- | --- | --- | --- |
| AXI_ID_WIDTH | int | 8 | Transaction ID width (1–16). |
| AXI_ADDR_WIDTH | int | 32 | Address width (12–64). |
| AXI_DATA_WIDTH | int | 32 | Data width; must match on both sides (32/64/128/256). |
| AXI_USER_WIDTH | int | 1 | User-signal width (0–1024). |

: Table 3.46: AXI4 to AXI3 parameters

## 3.15.7 Non-goals

The following AXI3/AXI4 features are intentionally outside the scope of this converter:

* **WRAP bursts longer than 16 beats.** AXI3 itself limits all bursts to 16 beats; an AXI4 WRAP burst longer than that has no legal AXI3 representation and is rejected by an assertion.
* **Write-data interleaving.** The converter stamps every W beat with the current AWID and does not support AXI3 interleaved W IDs.
* **Data-width conversion.** `AXI_DATA_WIDTH` must be identical on both sides.
* **QoS / REGION propagation.** These AXI4-only qualifiers are dropped.

## 3.15.8 Resource Utilization

| Module | Registers | LUTs | BRAM |
| --- | --- | --- | --- |
| axi4_to_axi3_rd | ~200 | ~250 | 0 |
| axi4_to_axi3_wr | ~300 | ~350 | 0 |
| axi4_to_axi3 (combined) | ~500 | ~600 | 0 |

: Table 3.47: AXI4 to AXI3 resources

The tables are approximate hand estimates; no post-route characterization has been run.

## 3.15.9 Testing

**Test Suite:** `test_axi4_to_axi3_rd.py`, `test_axi4_to_axi3_wr.py`, `test_axi4_to_axi3.py`.

| Test Category | Coverage | Status |
| --- | --- | --- |
| Single-beat read | Pass-through, ID preservation, ARLOCK mapping | Pass |
| Burst read ≤ 16 beats | Pass-through, RLAST/RRESP integrity | Pass |
| Burst read > 16 beats | Chopping, address advance, worst-response merge | Pass |
| Multi-ID concurrent reads | Per-ID merge isolation | Pass |
| Single-beat write | Pass-through, WID stamping | Pass |
| Burst write ≤ 16 beats | WLAST, B pass-through | Pass |
| Burst write > 16 beats | AW chopping, per-chunk WLAST, B merge | Pass |
| Early-W before AW | 16-beat buffer, backpressure on 17th beat | Pass |
| Multi-outstanding writes across IDs | Single-ID serialization, inter-ID concurrency | Pass |

: Table 3.48: AXI4 to AXI3 test coverage

---

**Next:** [AXI3 to AXI4](16_axi3_to_axi4.md)

## References

* ARM, *AMBA 3 AXI Protocol Specification*, ARM IHI 0022 — verified against this spec for AXI3-specific behavior: 4-bit `AxLEN`, 2-bit `AxLOCK`, write-data `WID`, and absence of `QoS`/`REGION`.
* ARM, *AMBA AXI and ACE Protocol Specification*, ARM IHI 0022E — verified against this spec for AXI4-specific behavior: 8-bit `AxLEN`, 1-bit `AxLOCK`, no `WID`, and `QoS`/`REGION` qualifiers.
