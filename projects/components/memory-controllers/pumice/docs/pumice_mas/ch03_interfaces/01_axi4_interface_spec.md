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

# AXI4 Slave Protocol

> Per HAS §2.4 §1 for the full per-channel signal list. This chapter is the **wire-level contract** specific to this controller — what's supported, what's relaxed, what's omitted, and the timing / ordering / backpressure semantics the integrator can rely on.
>
> For the FUB that implements this interface, see §2.2 (`axi4_slave_fub`).

---

## Compliance Profile

| Aspect                          | Support level                                              |
|---------------------------------|------------------------------------------------------------|
| AXI4 (ARM IHI 0022) signal set  | Full AW/W/B/AR/R                                            |
| AXI4-Lite                       | Not supported (use APB CSR for control)                    |
| AXI4-Stream                     | Not applicable                                              |
| AXI5                            | Not supported                                              |

## Supported Features (v1)

- INCR burst type (mandatory)
- Burst length 1..256 beats
- Burst size 2^0..2^7 bytes
- ID-aware OoO completion (when `AXI_OOO_ACROSS_IDS = true`; default)
- Per-ID in-order completion (AXI4 spec mandate; always enforced)
- 4 KB burst boundary check (slave returns `SLVERR` on cross-4KB bursts)
- `awqos`/`arqos` observed and forwarded to scheduler (not yet used in v1 priority function)

## Optional Features (build-time)

| Feature              | Parameter                | Default |
|----------------------|--------------------------|---------|
| FIXED burst type     | `SUPPORT_FIXED_BURST`    | `false` |
| WRAP burst type      | `SUPPORT_WRAP_BURST`     | `false` |
| OoO across IDs       | `AXI_OOO_ACROSS_IDS`     | `true`  |

When `SUPPORT_FIXED_BURST = false`, an AW or AR with `awburst = 00` returns `SLVERR` on the corresponding B / R response.

## Unsupported Features

- AXI4 exclusive accesses (`awlock`, `arlock` observed but ignored; behaves as normal access)
- AXI4 user signals (no `AWUSER`/`WUSER`/`BUSER`/`ARUSER`/`RUSER` ports)
- AXI4 cache-coherent extensions (`awcache`/`arcache` observed but no behavior)

## Backpressure Semantics

The slave asserts backpressure via standard AXI handshake:

| Channel | Backpressure reason                                                            |
|---------|--------------------------------------------------------------------------------|
| AW      | `aw_buf` full in `axi4_slave_fub`, or `txn_queue` at `SCHED_TUNING.txn_queue_high_water` |
| W       | `w_buf` full in `axi4_slave_fub`                                               |
| AR      | `ar_buf` full in `axi4_slave_fub`, or `txn_queue` at high water                |
| B       | Standard `bready` handshake; controller does not stall waiting for `bready`     |
| R       | Standard `rready` handshake; sustained stall triggers `STATUS.axi_r_stall` hint to scheduler (per §2.18) |

The high-water threshold (`SCHED_TUNING.txn_queue_high_water`) is software-tunable to provide a few-burst headroom before hard backpressure. Default is `TXN_QUEUE_DEPTH - 2`.

## Response Ordering

Two ordering rules apply:

1. **Per-ID in-order** — Always enforced. Two reads with the same ID complete in issue order; two writes with the same ID generate B responses in issue order.
2. **Cross-ID OoO** — Default on (`AXI_OOO_ACROSS_IDS = true`). Reads/writes with different IDs can complete in any order. When set to `false`, the slave enforces global in-order completion at the response side regardless of scheduler decisions.

Per HAS §3.1, even when scheduling is OoO at the DRAM layer, AXI response ordering is honored at the response side.

## 4 KB Burst Boundary

AXI4 specifies that a burst must not cross a 4 KB address boundary. The slave checks this at AW/AR intake:

```
boundary_cross = ( (addr & 0xFFF) + ((arlen+1) << arsize) ) > 0x1000
```

On detection, the slave still accepts the burst (the spec doesn't permit deassert of `arready`/`awready` mid-handshake on a valid request), but marks it for `SLVERR` response on B / R. The DRAM-side issue is suppressed for the offending burst.

## Timing Contract

| Path                                       | Behavior                                          |
|--------------------------------------------|---------------------------------------------------|
| `awvalid` → `awready` accept               | ≤ 1 cycle when `aw_buf` has space                  |
| `awready` accept → CAM push                | 1 cycle                                            |
| `aw_buf` → DRAM issue                      | Depends on scheduler / refresh state (typically 0–~256 cycles) |
| Last W beat → B response                   | tCWL + tWR window + scheduler backlog               |
| `arvalid` → first R beat                   | DRAM access latency (typically 30–100 ns) + bus rounding |
| Successive R beats (same burst)            | 1 per MC cycle (sustained streaming)               |

The slave does not register a registered output on its AXI ports by default. If timing closure requires it on a specific target, an external `axi_register_slice` from the AMBA library is the right answer; the controller deliberately does not embed one.

## Per-ID Outstanding Limits

| Limit                       | Parameter                  | Default |
|-----------------------------|----------------------------|---------|
| Total in-flight reads       | `RD_CAM_DEPTH`             | 16      |
| Total in-flight writes      | `WR_CAM_DEPTH`             | 16      |
| Per-ID in-flight reads      | `MAX_PER_ID_READS`         | 4       |
| Per-ID in-flight writes     | `MAX_PER_ID_WRITES`        | 4       |

When `AXI_OOO_ACROSS_IDS = false`, per-ID limits reduce to 1 (the slave enforces strict in-order across all IDs at the response side).

## Error Responses

| Condition                                              | Response       | Hint to software                    |
|--------------------------------------------------------|----------------|-------------------------------------|
| Cross-4 KB burst                                       | `SLVERR`       | None — software bug                  |
| FIXED burst when `SUPPORT_FIXED_BURST = false`         | `SLVERR`       | Recompile or rework software         |
| WRAP burst when `SUPPORT_WRAP_BURST = false`           | `SLVERR`       | Recompile or rework software         |
| Address outside `AXI_ADDR_WIDTH` range                  | `SLVERR`       | None — software bug                  |
| DFI rddata-error from PHY (rare)                       | `SLVERR`       | `irq_overflow` asserts                |
| Init not done                                          | `SLVERR`       | Poll `STATUS.init_done` before traffic |

DECERR is never returned — the slave's address space is monolithic.

## Open Questions / Future Work

- **QoS-driven priority.** `awqos`/`arqos` are observed but not yet used in the scheduler. v2 would feed them into the Stage-2 priority mask (see §2.7).
- **AXI4 user signals.** Some SoCs use USER signals for sideband info (security tags, cache hints). If the SoC needs them, add `USER_WIDTH` parameters and forward through the id_side_table.
- **AXI register slice option.** A build-time `INSERT_AXI_REGSLICE` parameter could embed register slices at the AXI boundary for very-high-frequency targets. Not in v1.
