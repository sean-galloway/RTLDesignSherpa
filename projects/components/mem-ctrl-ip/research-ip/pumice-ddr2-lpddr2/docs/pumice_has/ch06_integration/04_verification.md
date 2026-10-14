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

A planeed verification approach with the existing DFI BFM as the primary reference.

## Planeed Approach

### Plane 1: Module-Level Unit Tests

Every FUB pumice instantiates is a common-ip `mc_*` module
(`projects/components/mem-ctrl-ip/common-ip/rtl/`). Their unit tests belong
with that RTL, not in the pumice area: a pumice test points only at a pumice
DUT (owner ruling, 2026-10-13). The `mc_*` FUB tests that lived under
`dv/tests/fub/` were removed for that reason. common-ip carries no tests of
its own yet. The table lists the blocks whose pumice-area test was removed;
`mc_global_timers` and `mc_wr_splitter` keep a directed test in the scoria and
andesite areas, the rest now have none. `mc_addr_mapper`, `mc_cmd_arbiter`,
`mc_page_policy`, `mc_dfi_cdc`, `mc_dfi_cmd_path`, `mc_dfi_wr_serializer` and
`mc_dfi_rd_aligner` lost their pumice tests earlier, in the common-ip move
(scoria/andesite cover the last two; `mc_bank_timers`' leaf `mc_bank_timer`
is also tested there, the array wrapper is not):

| Module                      | Test focus a common-ip unit test should cover                          |
|-----------------------------|------------------------------------------------------------------------|
| `mc_wr_intake`          | AW-meta + wr-data FIFO handshakes; backpressure; burst splitting into fixed-BL commands |
| `mc_rd_intake`          | AR channel handshakes; address mapping; snarf (read-your-write) probe   |
| `mc_wr_splitter`        | Host burst split / pad / ragged-tail into fixed-BL sub-commands          |
| `mc_wr_data_cam`        | WR CAM fill / commit-drain / snarf movers; `r_fdone` fill-complete gating |
| `mc_rd_cmd_cam`         | RD CAM return-fill / drain movers; oldest-first, data-ready gating       |
| `mc_rd_return_ring`     | Read-return ring wrap and occupancy at each depth                        |
| `mc_bank_timers`        | Per-(rank,bank) preset/decrement timers; combinational safe_act/rd/wr/pre readiness |
| `mc_global_timers`      | tFAW / tRRD / tWTR / tRTW / tCCD against JESD79-2 / JESD209-2 truth tables |
| `mc_xddr2_refresh_ctrl` | tREFI counter; refresh-deferral; refresh request/ack handshake          |
| `mc_xddr2_init_sequencer` | Step-by-step DDR2 and LPDDR2 JEDEC MR init sequences                   |
| `mc_xddr2_mode_register` | CL / CWL / BL / AL decode (DDR2 and LPDDR2 MR2 RL/WL enum)              |
| `mc_xddr2_cmd_formatter` | Round-trip table tests against JEDEC encoding; LPDDR2 CA-bus branch     |
| `mc_lpddr2_zq_ctrl`     | ZQ interval expiry, Mode-C deferral, overdue escalation, DDR2-inert      |
| `mc_lpddr2_dq_cal`      | One-shot DQ calibration sequence                                         |

The pumice area verifies what pumice owns: `pumice_core` and `pumice_top`
(with the PeakRDL `pumice_csr` register block), at the default and the board
geometry, plus the pure-Python oracles the top tests rely on.

### Plane 2: Subsystem Tests

The three macro planes are common-ip too -- `mc_axi4_plane` (wr/rd intakes +
the two CAMs), `mc_scheduler_plane` (cmd arbiter + bank/global timers +
refresh + init + mode register + page policy) and `mc_dfi_2p1_plane` (single
CDC + cmd path + wr serializer + rd aligner). Their plane-level tests were
removed from `dv/tests/macro/` under the same ruling and have no common-ip
replacement yet. Inside pumice they are exercised only through `pumice_core`
and `pumice_top` (Plane 3). `dv/tests/macro/` keeps the JEDEC command-stream
oracle's own unit test (`test_pumice_cmd_stream_checker.py`).

### Plane 3: End-to-End with DFI BFM Slave

The full controller drives the DFI BFM slave through our existing co-sim harness (`tests/sim/dfi/test_litedram/...` patterns in the DV repo).

- AXI4 stimulus generators issue representative traffic
- DFI BFM slave captures the controller's command stream
- Assertions check: command sequencing matches AXI, timing constraints are honored, data integrity round-trips through the slave's MemoryModel

### Plane 4: External-Reference Cross-Validation

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
- **Verification cost is significantly higher than FIFO.** OoO issue means assertions like "request N landed at cycle X" can't be used. The DV plan relies on protocol-level scoreboarding: the BFM master records arrival order per ID, the BFM slave records issue order, and the scoreboard verifies the AXI4 per-ID ordering invariant is preserved. Within-ID ordering violations are a higher-severity bug than performance regressions and should be caught at Plane 1 unit tests, not deferred to integration.
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
