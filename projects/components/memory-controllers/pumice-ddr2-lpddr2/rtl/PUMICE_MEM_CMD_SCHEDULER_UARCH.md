# pumice_mem_cmd_scheduler — µarch (locked spec)

The command-scheduling layer between `pumice_axi4_ifc` (the CAMs) and the DFI
layer. LiteDRAM-inspired split:

```
pumice_axi4_ifc (CAMs)         pumice_mem_cmd_scheduler                 [DFI layer — future]
  wr/rd sched_lu  ───────────►  per-bank timers + global timers +        drains cmd FIFO,
  wr/rd oldest    ───────────►  refresh + init + ARBITER  ── cmd FIFO ──► packs onto nphases,
  wr commit / rd issue ◄──────  (single abstract command / cycle)         serializes data,
                                                                          CDC to PHY clock
```

- **Scheduler owns JEDEC timing** (via the timers); the DFI layer just places +
  serializes. Scheduler is **PHY/nphases-agnostic** and **single-issue** (one
  abstract command per controller cycle). Bandwidth comes from the DFI layer
  aggregating up to nphases commands/DFI-cycle; the **command FIFO is the CDC**
  (controller clock → PHY DFI clock). Per-phase timing (the bank-parallel
  open_page failure mode) lives entirely in the DFI layer.
- **Single controller clock** (`aclk`) for AXI-IFC + scheduler; CDC at the DFI
  boundary only.

## Sub-FUBs (review verdicts)

| FUB | verdict |
|---|---|
| `pumice_bank_timers` | NEW (open-page rework of xbank_timers) ✅ built+tested |
| `global_timers` | reuse (tFAW/tRRD per-rank; tWTR/tRTW/tCCD global) |
| `refresh_ctrl` | reuse (tREFI + 8-deep postpone; arbiter PRE-alls before REF) |
| `init_sequencer`, `mode_register` | reuse (JEDEC MRS init; gates traffic until done) |
| `powerdown_ctrl`, `page_predictor` | reuse (optional) |

## The arbiter (NEW — the only substantive new RTL)

Per controller cycle, emit ONE abstract command into the output FIFO:
`{op(ACT/RD/RDA/WR/WRA/PRE/PREA/REF/MRS/NOP), rank, bank, row, col, ap}`.

Priority:
1. **init**: `!init_done` → forward `init_sequencer` command stream.
2. **refresh**: `refresh_req` → PRE any active banks, then REF (grant);
   hold through `refresh_drain_active`.
3. **normal traffic** (reads + writes):
   - probe wr CAM & rd CAM `sched_lu[N]` with each bank's `bank_open_row`
     → per-bank row-hit candidates (+ `oldest` ports as fallback);
   - a candidate is issuable when timing-ready:
     `bank_rdwr_ready & tccd_window_ok & (RD:twtr_global_ok | WR:trtw_window_ok)`;
   - **RD/WR arbitration**: read-priority; switch to draining writes when the
     wr CAM occupancy crosses a HIGH watermark, drain to a LOW watermark;
   - **tie-break**: oldest (CAM `age`) wins among ready candidates;
   - if no ready row-hit: **ACT** the row for the oldest pending op
     (`bank_act_ready & tfaw_window_ok & trrd_window_ok`);
   - if a row must close (conflict / idle-timeout): **PRE** (`bank_pre_ready`);
   - **oldest fallback**: if all N lookups miss, act toward the `oldest` entry.
   - drive `evt_*` to `pumice_bank_timers` + `global_timers`; drive
     `wr commit` (WR issued) / `rd issue` (RD issued) back to the CAMs.

**Page policy is configurable** (CSR): CLOSED (every column op is RDA/WRA,
auto-precharge) | HYBRID (page_predictor hint) | OPEN (leave rows open, PRE on
conflict/refresh/idle). OPEN is the target for the row-hit / 8.8x streaming case.

## Scheduler → DFI command FIFO
`gaxi_fifo_sync` of `{op, rank, bank, row, col, ap}`; scheduler pushes, DFI layer
pops at phase rate. Depth sized so the DFI layer can gather nphases/cycle.

TODO: DFI layer (phase packing + serialization + CDC) is the next layer up.
