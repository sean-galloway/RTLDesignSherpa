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

# Verification Strategy

A layered verification approach with the existing DFI BFM as the primary reference.

## Layered Approach

### Layer 1: Module-Level Unit Tests

Each of the 17 modules gets cocotb unit tests:

| Module             | Test focus                                                       |
|--------------------|------------------------------------------------------------------|
| `axi4_slave`       | Channel handshakes, backpressure, burst splitting, ordering      |
| `addr_mapper`      | Address translation across `ADDR_MAP_SCHEME` modes               |
| `txn_queue`        | Insert / scan / removal; age saturation; row-hit caching         |
| `scheduler`        | FR-FCFS priority order; page-policy dispatch; refresh prioritization |
| `page_predictor`   | HAPPY table read/write; accuracy after warm-up                   |
| `bank_machine`     | FSM transitions; timing-counter enforcement                      |
| `xbank_timers`     | tRRD / tFAW / tWTR / tCCD against JESD79-2 / JESD209-2 truth tables |
| `refresh_mgr`      | tREFI counter; REFab / REFpb selection; DARP idle-bank logic     |
| `power_state`      | All FSM transitions; SR-entry/exit; DPD entry/exit (LPDDR2)      |
| `init_engine`      | Step-by-step execution against canonical init sequences          |
| `cmd_encoder`      | Round-trip table tests against JEDEC encoding                    |
| `gear_out`         | 1-phase to N-phase replication; idle-phase handling              |
| `wdata_path`       | CWL alignment; ID tagging; mask conversion                       |
| `rdata_path`       | CL alignment; OOO completion; back-pressure                      |
| `dfi_master`       | Tie-off behavior; aggregation correctness                        |
| `csr_slave`        | APB3 protocol; CDC; error responses                              |

### Layer 2: Subsystem Tests

Multi-module integration tests:

- **AXI frontend** (axi4_slave + addr_mapper + txn_queue): full AXI transaction flow with diverse traffic
- **Scheduler subsystem** (scheduler + page_predictor + bank_machines + xbank_timers): scheduler decisions on representative queue contents
- **Refresh subsystem** (refresh_mgr + bank_machines): REFab / REFpb sequencing on uneven bank activity
- **Init + power FSM** (init_engine + power_state): full init followed by SR entry/exit cycle

### Layer 3: End-to-End with DFI BFM Slave

The full controller drives the DFI BFM slave through our existing co-sim harness (`tests/sim/dfi/test_litedram/...` patterns in the DV repo).

- AXI4 stimulus generators issue representative traffic
- DFI BFM slave captures the controller's command stream
- Assertions check: command sequencing matches AXI, timing constraints are honored, data integrity round-trips through the slave's MemoryModel

### Layer 4: External-Reference Cross-Validation

For DDR2: cross-validate against LiteDRAM's DDR2 model.

- Generate LiteDRAM controller alongside ours
- Both drive the same DFI BFM slave with the same AXI stimulus
- Compare command streams; differences flag potential design issues

LPDDR2 has no LiteDRAM analog. Cross-validation for LPDDR2 is limited to the BFM master ↔ BFM slave path.

## Characterization Sweep

Post-functional verification, the sweep runs each characterization parameter through its choices on the benchmark suite from §5.2:

### Sweep Matrix

| Parameter            | Sweep values                                |
|----------------------|---------------------------------------------|
| `LOOKAHEAD_DEPTH`    | 0, 1, 2, 4                                  |
| `PAGE_POLICY`        | OPEN, CLOSE, HAPPY_HYBRID                   |
| `REFPB_POLICY`       | ROUND_ROBIN, OLDEST_FIRST, DARP             |
| `REFRESH_DEFER_MAX`  | 1, 2, 4, 8                                  |
| `TXN_QUEUE_DEPTH`    | 8, 16, 32                                   |
| `N_PHASES`           | (build-determined; usually 4)               |

The full cross-product would be 4 × 3 × 3 × 4 × 3 = 432 builds; in practice we sweep one parameter at a time holding others at recommended defaults, which reduces to ~17 builds per memtype. The exception is the `LOOKAHEAD_DEPTH × PAGE_POLICY` pair — these interact strongly (the fallback policy only matters when lookahead is inconclusive), so this pair is swept as a full 4 × 3 = 12-point grid.

### Sweep Outputs

Each (parameter, value) run produces a JSON report:

```json
{
  "memtype": "LPDDR2",
  "page_policy": "HAPPY_HYBRID",
  "refpb_policy": "DARP",
  "workload": "mobile-mixed",
  "metrics": {
    "read_bw_pct": 73.2,
    "write_bw_pct": 68.1,
    "read_latency_avg_ns": 142,
    "read_latency_p99_ns": 198,
    "refresh_block_pct": 4.3,
    "row_hit_rate_avg": 0.81,
    "page_predictor_accuracy": 0.91
  }
}
```

These feed into a sweep visualization tool that selects defaults from data.

### Out-of-Order Scheduler Trade-Offs

The centralized FR-FCFS scheduler proposed in §1 (Differentiating Features) is the most architecturally aggressive choice in this controller and warrants explicit characterization beyond just the sweep matrix above. Three concrete concerns:

- **Timing-critical path scales with `TXN_QUEUE_DEPTH`.** Scanning the full queue every cycle for the best candidate is a comparator pyramid: priority resolves over (ready-flag, row-hit-flag, age) for every entry simultaneously. At `TXN_QUEUE_DEPTH = 16` this is well within an embedded-SoC clock budget; at 32 it stays comfortable; at 64 it becomes the critical path on the controller side. The characterization sweep should report scheduler combinational depth at synthesis time alongside the performance numbers — the right `TXN_QUEUE_DEPTH` is the largest value that doesn't push the scheduler off the clock budget.
- **Area cost is super-linear in queue depth.** Each queue entry needs its full metadata replicated (bank, row, col, ID, age, row-hit cache). At depth 16, ~2K gates; at depth 64, ~10K gates — comparable to the rest of the scheduler combined. The HAPPY predictor's gate cost is a separate line item.
- **Verification cost is significantly higher than FIFO.** OoO issue means assertions like "request N landed at cycle X" can't be used. The DV plan relies on protocol-level scoreboarding: the BFM master records arrival order per ID, the BFM slave records issue order, and the scoreboard verifies the AXI4 per-ID ordering invariant is preserved. Within-ID ordering violations are a higher-severity bug than performance regressions and should be caught at Layer 1 unit tests, not deferred to integration.
- **Fairness tail matters under adversarial workloads.** With `AGE_MAX` as the only anti-starvation cap, pathological patterns can drive 99th-percentile latency well above mean. The `random-narrow` and `multi-master` workloads in the benchmark suite intentionally exercise this; the `mobile-mixed` workload simulates the common case. The recommended default for `AGE_MAX` should be picked based on tail-latency targets, not throughput targets.

These concerns are unique to the OoO scheduler design choice — a simpler per-bank FIFO controller (the typical open-source pattern) would not face them, at the cost of leaving row-hit reordering performance on the table.

## Verification Hooks

Internal observation outputs are exposed via CSR (see §6.3) for in-system characterization. Additionally, the controller emits internal "event" signals that can be tied to waveform-dump triggers:

- `ev_init_done`
- `ev_refresh_issued`
- `ev_page_conflict_detected`
- `ev_queue_full`
- `ev_refresh_pending_critical`

Specific events can be wired to a test-bench-controlled waveform-capture trigger during bring-up.

## Coverage Targets

Functional coverage (collected during regression):

- All FSM states reached in each module
- All page policies exercised
- All refresh policies exercised
- All scheduler priority levels exercised
- All AXI burst types exercised (if enabled)
- All `ADDR_MAP_SCHEME` modes exercised

Code coverage targets: 100% line / branch coverage for all modules.

Assertion coverage: all design assertions (registered protocol checks) hit during regression.
