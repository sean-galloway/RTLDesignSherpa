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

# Integration and Verification

## RAPIDS Integration

HIVE-C connects to RAPIDS through two complementary interfaces:

**Control interface (HIVE-C AXI4-Lite master → RAPIDS registers):** status
reads, queue base addresses, DMA parameter configuration. Used for setup
and status; not on the data path.

**Descriptor injection (HIVE-C AXIS master → Delta → RAPIDS):** 256-bit CDA
packets classified by `tuser=2'b01` and routed to the RAPIDS descriptor
FIFO at virtual tile 16. No memory round-trip — 10-20 cycles vs. 100+ for
memory-mapped descriptor writes.

The contract with RAPIDS is exactly the CDA descriptor format in §4.2 plus
the channel-aware S2MM rule in §5.2. See the RAPIDS Beats HAS for the
consumer side.

## Delta Integration

HIVE and Delta meet at three seams:

1. **Packet classes** — HIVE originates CDA/PKT_CONFIG/PKT_STATUS; Delta
   routes them by `tuser`/`tdest` under contexts HIVE selects.
2. **Virtual tiles** — RAPIDS = 16, HIVE-C = 17, edge-attached to the mesh.
3. **Router configuration** — the register block in §4.3, written via
   PKT_CONFIG broadcast (Configuration Manager) or HIVE-C's AXIL window.

The tile internals (NI, router, compute element) are Delta's architecture:

```
┌─────────────────────────────────────┐
│         Compute Tile N              │
│  ┌──────────────────────────────┐  │
│  │   SERV Monitor (HIVE Block 2)│  │
│  │  - Traffic counters          │  │
│  │  - Trigger logic             │  │
│  │  - AXIS TX injector          │  │
│  └──────────┬───────────────────┘  │
│             │ Control signals      │
│  ┌──────────▼───────────────────┐  │
│  │   Network Interface (Delta)  │  │
│  │  - AXIS packetizer           │  │
│  │  - Credit flow control       │  │
│  │  - TID override (CE traffic) │  │
│  └──────────┬───────────────────┘  │
│             │                      │
│  ┌──────────▼───────────────────┐  │
│  │   Router (Delta, 5-port)     │  │
│  │  - N/S/E/W + Local           │  │
│  │  - XY routing logic          │  │
│  │  - VC buffers (8 flits ea.)  │  │
│  └──────────┬───────────────────┘  │
│             │ To/from mesh         │
└─────────────┼───────────────────────┘
              │
   ┌──────────▼───────────┐
   │  Compute Element     │
   │  (Delta: DSP MACs,   │
   │   local BRAM, PE FSM)│
   └──────────────────────┘
```

: HIVE/Delta tile seam — SERV monitor above the Delta-owned NI

## System Top Integration

```systemverilog
// Top-level integration example (architectural port names; see MAS ch.3)
module system_top (
    input  logic        clk_100mhz,
    input  logic        rst_n,
    // Host interface
    input  logic [31:0] host_cmd,
    output logic [31:0] host_resp,
    // External memory (for RAPIDS)
    // ... AXI4 memory interface ...
);

    // HIVE instance
    hive_top u_hive (
        .aclk           (clk_100mhz),
        .aresetn        (rst_n),
        .host_cmd       (host_cmd),
        .host_resp      (host_resp),
        .axis_cda_*     (hive_to_delta_cda),
        .axis_status_*  (delta_to_hive_status)
    );

    // Delta Network instance
    delta_network_4x4 u_delta (
        .aclk           (clk_100mhz),
        .aresetn        (rst_n),
        .tile16_*       (rapids_interface),  // RAPIDS virtual tile
        .tile17_*       (hive_interface)     // HIVE-C virtual tile
    );

    // RAPIDS instance
    rapids_top u_rapids (
        .aclk           (clk_100mhz),
        .aresetn        (rst_n),
        .axis_cda_*     (rapids_interface),  // From Delta
        .m_axi_*        (memory_interface)   // To external memory
    );

endmodule
```

## Verification Strategy

**Level 1 — Unit (cocotb):** every RTL module gets a dedicated testbench.
Coverage target: 100% line, 95%+ branch. Example (SERV congestion trigger):

```python
@cocotb.test()
async def test_congestion_detection(dut):
    """SERV triggers alert when buffer exceeds threshold"""
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1

    dut.congestion_threshold.value = 120  # 75% of 160-entry FIFO
    for i in range(125):                   # Inject with backpressure
        dut.pkt_rx_valid.value = 1
        dut.pkt_rx_ready.value = 0
        await RisingEdge(dut.clk)

    await RisingEdge(dut.clk)
    assert dut.congestion_alert.value == 1
    assert dut.axis_tx_valid.value == 1
    assert dut.axis_tx_tuser.value == 0b11  # PKT_STATUS
```

**Level 2 — Integration:** multi-module scenarios (SERV + router, HIVE-C +
control network + 16 SERVs, Configuration Manager + Delta); protocol
compliance checkers; randomized traffic stress.

**Level 3 — System:** full HIVE + RAPIDS + Delta against real workload
traces (matmul, convolution); SimPy prediction vs. RTL-measured performance
(±10% acceptance).

**Level 4 — Hardware:** NexysA7 bring-up, ILA capture, performance counters
vs. model validation.

**Formal property inventory** (critical properties, formal-verified):

| Property | Statement |
|----------|-----------|
| Router deadlock freedom | A request denied a grant eventually receives it (XY + 2 VC) |
| Descriptor FIFO ordering | Enqueue order preserved at dequeue per queue |
| Context switch atomicity | No packet crosses a router between `SET_ROUTING_MODE` and `CONFIG_ACTIVATE` |
| TID integrity | No compute-element PKT_DATA egresses with `tid ≠ tile_id` |
| Quiesce completeness | `STATUS.active_packets == 0` before mode update |

: Formal property inventory

## Implementation Roadmap

| Phase | Scope | Weeks |
|-------|-------|-------|
| 1 — Core infrastructure | VexRiscv integration + memories; one SERV monitor with counters; basic AXIS injection; unit tests | 1-3 |
| 2 — 2×2 prototype | 2×2 mesh + 4 SERVs; control network; config register bank; descriptor-injection integration test | 4-6 |
| 3 — Full 4×4 | 16 routers + SERVs; ≥ 2 virtual contexts; switch logic; HIVE-C scheduler firmware; RAPIDS + Delta end-to-end | 7-10 |
| 4 — Optimization | 100 MHz closure; Artix-7 fit; SimPy-guided tuning | 11-12 |
| 5 — Validation | NexysA7 hardware-in-loop; model-vs-hardware; stress; tutorials | 13-14 |

: Implementation roadmap

## Expansion Path (PoC → Production)

Kintex-7 325T scaling: 8×8 mesh (64 tiles), 64 SERV monitors, 4 VexRiscv
cores under hierarchical control, 150-200 MHz, 8 routing contexts.
Estimated control overhead: 50,000 LUTs + 288 BRAM — still leaving 153,800
LUTs and 840 DSPs for compute. Feature extensions beyond scaling: adaptive
routing, quality-of-service guarantees, fault tolerance with dynamic
rerouting, and ML-assisted traffic prediction on the SERV fabric.

---

**Last Updated:** 2026-10-12
