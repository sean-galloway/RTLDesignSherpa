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

Each live FUB gets its own cocotb unit test (see `dv/tests/fub/`):

| Module                      | Test focus                                                             |
|-----------------------------|------------------------------------------------------------------------|
| `pumice_wr_intake`          | AW-meta + wr-data FIFO handshakes; backpressure; burst splitting into fixed-BL commands |
| `pumice_rd_intake`          | AR channel handshakes; address mapping; snarf (read-your-write) probe   |
| `pumice_wr_data_cam`        | WR CAM fill / commit-drain / snarf movers; `r_fdone` fill-complete gating |
| `pumice_rd_cmd_cam`         | RD CAM return-fill / drain movers; oldest-first, data-ready gating       |
| `addr_mapper`               | Address translation across `ADDR_MAP.bank_lsb` settings (ROW_MAJOR .. interleave) and hash on/off |
| `pumice_cmd_arbiter`        | Single-pick priority order; inline open-page decision; refresh prioritization |
| `pumice_bank_timers` / `bank_timer` | Per-(rank,bank) preset/decrement timers; combinational safe_act/rd/wr/pre readiness |
| `global_timers`             | tFAW / tRRD / tWTR / tRTW / tCCD against JESD79-2 / JESD209-2 truth tables |
| `refresh_ctrl`              | tREFI counter; refresh-deferral; refresh request/ack handshake          |
| `init_sequencer`            | Step-by-step DDR2 and LPDDR2 JEDEC MR init sequences                     |
| `mode_register`             | CL / CWL / BL / AL decode (DDR2 and LPDDR2 MR2 RL/WL enum)               |
| `dfi_cmd_formatter`         | Round-trip table tests against JEDEC encoding; LPDDR2 CA-bus branch      |
| `dfi_signal_pack`           | DW-to-phase split; idle-phase handling                                  |
| `pumice_dfi_cdc`            | The single async-FIFO clock-domain crossing; bubble-free cmd/wr/rd flow  |
| `pumice_dfi_wr_serializer`  | CWL alignment; write-data serialization onto DFI phases                  |
| `pumice_dfi_rd_aligner`     | CL alignment; read-data assembly; back-pressure                          |

The four macro wrappers and the integration levels are exercised at Layer 2/3:
`pumice_axi4_ifc`, `pumice_mem_cmd_scheduler`, `pumice_dfi_layer`, `pumice_core`,
and `pumice_top` (the PeakRDL `pumice_csr` register block is verified with the top).

### Layer 2: Subsystem Tests

Multi-module integration tests, framed around the three macro layers (see `dv/tests/macro/`):

- **AXI interface** (`pumice_axi4_ifc` = wr/rd intakes + the two CAMs): full AXI transaction flow with diverse traffic, including read-your-write snarf forwarding
- **Command scheduler** (`pumice_mem_cmd_scheduler` = cmd arbiter + bank/global timers + refresh + init + mode register): scheduler decisions on representative queue contents, inline open-page reordering, refresh interleave
- **DFI layer** (`pumice_dfi_layer` = single CDC + cmd path + wr serializer + rd aligner): command/data flow across the clock-domain crossing with the DFI BFM slave

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

This is a real, proven path. A LiteDRAM DDR2 memtest passes on the Nexys A7 board (128 MiB), which confirmed the board, PHY, pin-out, and DRAM are good. pumice itself is now board-proven on the same Nexys A7: DDR2 reads and writes are clean (0 mismatches across the characterization traffic). Both memtypes pass the full sim suite.

LPDDR2 has no LiteDRAM analog, so cross-validation for LPDDR2 is limited to the BFM master to BFM slave path. LPDDR2 is nonetheless fully functional in sim (reads and writes, bit-exact JESD209-2F CA encoding, full MR init) and passes the sim suite.

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
| `DFI_RATE`           | (build-determined; usually 4)               |
| `ADDR_MAP.bank_lsb`  | ROW_MAJOR (== COL_WIDTH), interleave, hash on/off |

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

- All FSM states reached in each module that has one (the bank timers and CAMs are FSM-free; their timer/counter states are covered instead)
- All page policies exercised
- All refresh policies exercised
- All scheduler priority levels exercised
- All AXI burst types exercised (if enabled)
- All `ADDR_MAP.bank_lsb` settings (ROW_MAJOR .. interleave) exercised, with hash on and off

Code coverage targets: 100% line / branch coverage for all modules.

Assertion coverage: all design assertions (registered protocol checks) hit during regression.
