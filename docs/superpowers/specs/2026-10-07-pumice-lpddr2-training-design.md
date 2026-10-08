# Pumice LPDDR2 Calibration & Training — Design Spec

**Date:** 2026-10-07
**Status:** Approved approach (Approach A), pending written-spec review
**IP:** `projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2`
**Spec basis:** JESD209-2F (in-repo at `reference/ddr_lpddr_specs/JESD209-2F.pdf`)

## 1. Goal

Bring pumice's LPDDR2 path from "init-only" to full JESD209-2F calibration support
before the LPDDR2 hardware arrives. Three JEDEC mechanisms exist for LPDDR2; pumice
today implements only the first bullet of the first one:

| JEDEC feature | Reference | Pumice today |
|---|---|---|
| ZQ Init calibration (MRW MR10 = 0xFF, tZQINIT) | JESD209-2F §5.13.3 | **Done** — `init_sequencer.sv` S_L_ZQ |
| ZQ Short/Long periodic calibration (MRW MR10 = 0x56 / 0xAB) | JESD209-2F §5.13.3 | **Missing** |
| MRR (Mode Register Read) command | JESD209-2F §5.12 | **Missing** — no opcode, no CA encoding |
| DQ Calibration (MRR MR32 pattern A `1010`, MRR MR40 pattern B `0011`) | JESD209-2F §5.12.2 | **Missing** |

Explicitly **not** in LPDDR2 (verified against JESD209-2F mode-register map):
write leveling, read leveling, DLL, and CA training. MR41–47 are "Do Not Use" and
MR48–62 are "Reserved" — CA training is an LPDDR4 MPC mechanism owned by andesite's
training layer. No CA-training hardware is added here.

## 2. Scope boundary (decided)

- **In:** core RTL sequencers + read-capture sideband, DV, formal invariants,
  CSR growth, docs (HAS/MAS/uarch), filelists, regenerated register artifacts.
- **PHY delay taps stay outside the core.** The DQ-cal sweep loop (walk PHY read
  delay tap, capture, compare) runs in board firmware/harness driving the FPGA
  IDELAY primitives directly. The core exposes `cal_start`/`cal_result` CSRs and
  the MRR engine; it gains **no** FPGA-primitive logic and **no** new top-level
  ports. This matches the scoria/andesite doctrine (cores are DFI-clean).
- **Out:** self-refresh-exit ZQCL trigger (powerdown path is dormant in pumice),
  temperature-sensor-driven refresh (MR4 MRR read becomes *possible* with the MRR
  engine but is not built), LPDDR2-NVM boot sequences, deep-power-down changes.

## 3. Architecture

New fourth layer, mirroring andesite's structure:

```
pumice_top / pumice_core
├── pumice_axi4_layer        (unchanged)
├── pumice_scheduler_layer   (+ trn_cmd channel, + cal_busy gate)
└── pumice_training_layer    (NEW: u_zq, u_lp_cal, trn mux, CDC)
    └── pumice_dfi_layer     (+ cmd_mrr_i passthrough, + cal capture in rd_aligner)
```

### 3.1 New FUB: `pumice_zq_ctrl.sv`

Port of `scoria_zq_ctrl` to LPDDR2 semantics. Request/grant handshake with the
arbiter; **the FUB never generates the command itself** — on grant the arbiter
issues `OP_MRS` with `mrw_row(10, OP)` where OP = `8'h56` (ZQCS) or `8'hAB` (ZQCL).
LPDDR2 has no ZQCS/ZQCL command encodings (unlike DDR3); both are MRW-to-MR10.

- Interval countdown (`ZQ_INTERVAL`, 0 = disabled). Mode-C deferral: if demand is
  high at expiry, enter `ZQ_DEFER`, wait for demand low or `overdue_max`, then
  request anyway.
- Overdue expiry requests a **ZQCL** (long) instead of ZQCS — re-establishes
  ±15% RON per §5.13.3 after deferred calibration.
- Post-grant hold window `t_zqcs` / `t_zqcl` driven back to the arbiter as
  `cal_busy`; JEDEC forbids other data-bus activity during the window.
- Run condition: `zq_en && init_done && (memtype == MEMTYPE_LPDDR2)`. DDR2 has no
  ZQ pin; the FUB is inert for DDR2 builds.
- MR10 writes are **transient commands, never shadowed** into the mode register
  FUB (same rule as `init_sequencer` S_L_ZQ today).
- ZQ on LPDDR2-S4 requires all banks precharged; LPDDR2-N allows Idle-or-Active.
  The conservative all-banks-idle grant contract satisfies both.

### 3.2 New FUB: `pumice_lp_cal.sv` (DQ calibration sequencer)

One-shot, andesite-`ca_train_ifc`-style. `cal_start` pulse runs:

1. Wait for maintenance grant (arbiter guarantees all-banks-idle + write-path
   drained via the existing `w_out_safe` guard chains — this also satisfies JEDEC
   MRR spacing: RD→MRR ≥ BL/2, WR→MRR ≥ WL+1+BL/2+tWTR).
2. Issue MRR to MR32. Formatter emits the MRR CA word; `cal_expect` is armed in
   the DFI-layer read aligner.
3. Capture the first `dfi_rddata_valid` beat (MRR data lands
   `RL·tCK + tDQSCK + tDQSQ` after the command; BL=4, only beat 0 carries MR data
   on DQ[0:7]; x16 devices also mirror the DQ-cal pattern on DQ[8]).
4. Wait `tMRR` (= 2 clocks, §5.12), issue MRR to MR40, capture beat 0.
5. Sticky `cal_done`; set `cal_err` on readout timeout.

Both captured beats land in CSRs (`CAL_MRR32_DATA`, `CAL_MRR40_DATA`). Firmware
compares each DQ lane against patterns A/B across its tap sweep — the compare
logic deliberately lives outside the core.

### 3.3 New layer: `pumice_training_layer.sv`

- Holds `u_zq` + `u_lp_cal`, muxes both onto one `trn_cmd` channel
  (priority: zq > lp_cal; one-hot pending flags like andesite).
- Owns all mc_clk ↔ dfi_clk CDC (`cal_expect` down, captured data up) using the
  repo's `cdc_synchronizer`/`sync_pulse` pattern.
- Instantiated in `pumice_top`/`pumice_core` beside the scheduler layer; nets into
  the scheduler layer's new `trn_cmd_*` ports, exactly as `andesite_core.sv:643-655`
  wires its training layer.

### 3.4 Arbiter changes (`pumice_cmd_arbiter.sv`)

One new maintenance client, andesite's contract:

- New inputs `trn_cmd_req_i / trn_cmd_op_i / trn_cmd_bank_i / trn_cmd_row_i /
  trn_cmd_mrr_i`, output `trn_cmd_grant_o`.
- Priority: `init > refresh > trn_cal > demand` (scoria puts ZQ below refresh;
  same here).
- Grant only when: all banks idle, no ACT/PRE in flight or guard window,
  `!w_rfc_busy`, no in-flight write data. The granted op is passed **verbatim**
  onto the command output (arbiter does not re-encode maintenance commands).
- During the post-grant hold window (`cal_busy` from the training layer), the
  final fire gate blocks all demand classes — **BUG-003 discipline applies:
  `w_fire_out == cmd_valid_o && cmd_ready_i` must hold by construction**; the new
  gate is folded into `w_out_safe`, never the pick cone.

### 3.5 Command path changes

- `dram_op_e` is **not** widened (all 16 opcodes consumed; MRR never enters the
  demand path). MRR rides as `OP_MRS` + a new 1-bit `cmd_mrr` flag.
- Cmd FIFO word grows by 1 bit: `{mrr, ap, col, row, bank, rank, op}`
  (`pumice_scheduler_layer.sv` pack site ~:541, `pumice_dfi_cmd_path` unpack).
- `dfi_cmd_formatter.sv` OP_MRS branch: when `cmd_mrr_i`, drive the MRR CA word —
  JESD209-2F §5.12: `CA0r=L, CA1r=L, CA2r=L, CA3r=H`, MR select
  `{CA1f,CA0f,CA9r..CA4r}` = MA[7:0] (same field packing as MRW, CA3r inverted).
  Repo reference: `docs/uarch/LPDDR2_CA_ENCODING.md` line 59 (today notes "not
  used by pumice" — that note is retired by this work).
- For LPDDR2, ZQCS/ZQCL opcodes remain NOP at the formatter (today's `default`
  branch) — LPDDR2 ZQ is pure MRW, so no formatter change is needed for ZQ.

### 3.6 Read-capture sideband (`pumice_dfi_rd_aligner.sv`)

- New inputs `cal_expect_i` (dfi_clk domain), outputs `cal_data_o` (full DFI read
  width), `cal_valid_o`.
- When `cal_expect` is armed: capture the first `dfi_rddata_valid_i` beat into a
  holding register, raise `cal_valid_o`, disarm. **No read may be outstanding**
  (arbiter contract guarantees it), so the sideband cannot collide with the normal
  read FIFO push path, which is left untouched.

## 4. CSR map additions

Allocated at `0x0A0–0x0BC` (free range between `OBS_ROW_HIT` 0x080–0x09F and the
retired 0x0C0 hole; retired holes are never reused — pumice doctrine). Regenerate
via `bin/peakrdl_generate.py`; gates: `check_rdl_regen.py`,
`check_csr_reset_parity.py` (new `sw=rw` fields must be declared
ships/swept/waived in `dv/csr_reset_parity.py`).

| Addr | Reg | Acc | Contents |
|---|---|---|---|
| 0x0A0 | `CAL_CTRL` | rw | `zq_en[0]`, `zq_defer_en[1]` (Mode C), `cal_start[4]` (wo, self-clear), `cal_abort[5]` (wo) |
| 0x0A4 | `CAL_ZQ_INTERVAL` | rw | 32-bit ZQCS interval in mc_clk cycles, 0 = off |
| 0x0A8 | `CAL_ZQ_TIMING` | rw | `t_zqcs[15:0]`, `t_zqcl[31:16]` post-grant hold windows |
| 0x0AC | `CAL_TRAIN_TIMING` | rw | `t_mrr[15:0]` (=2 default), `t_readout[31:16]` MRR issue→data timeout |
| 0x0B0 | `CAL_MRR32_DATA` | ro | Captured MRR-MR32 beat 0 (full DFI width) |
| 0x0B4 | `CAL_MRR40_DATA` | ro | Captured MRR-MR40 beat 0 |
| 0x0B8 | `CAL_STATUS` | ro | `zq_busy[0]`, `cal_busy[1]`, `cal_done[2]` (sticky), `cal_err[3]` (sticky), `zq_overdue[4]`, `zqcs_total[31:16]` |

`0x0BC` intentionally left unallocated (padding before the 0x0C0 retired hole).

## 5. Verification plan

| Level | Test | Template |
|---|---|---|
| FUB | `test_pumice_zq_ctrl.py` — interval expiry, Mode-C deferral, overdue→ZQCL select, hold window, DDR2 inert | `dv/tests/fub/test_init_sequencer.py` |
| FUB | `test_pumice_lp_cal.py` — one-shot sequence, MRR32→capture→tMRR→MRR40→capture, timeout error, abort | same |
| FUB | `test_dfi_cmd_formatter.py` — **add** MRR CA-encoding case vs JESD209-2F §5.12 (`CA3r=H`, MA select) | existing |
| FUB | `test_pumice_dfi_rd_aligner.py` — cal capture with zero reads outstanding; no interference with normal returns | existing |
| Macro | `test_pumice_scheduler_layer.py` — trn priority vs refresh/demand, all-banks-idle gating, demand blocked during `cal_busy`, fire==valid invariant | existing |
| Macro | `test_pumice_training_layer.py` — zq/lp_cal muxing, CDC | `test_pumice_scheduler_layer.py` |
| Top | `test_pumice_top.py` / CSR test — end-to-end `cal_start` → both captured patterns correct on LPDDR2 model; ZQCS MRW observed at interval with demand blocked | existing |
| Legality | `pumice_cmd_stream_checker.py` — allow MRR + MRW-MR10 maintenance ops in stream rules | existing |

Regression levels GATE/FUNC/FULL per repo convention (`REG_LEVEL`). Existing
DDR2-mode tests must stay green (training FUBs inert in DDR2).

## 6. Formal invariants (stretch but intended)

- `trn_cmd_grant_o |-> all banks idle` (arbiter bind).
- `cal_busy |-> no demand-class fire` (BUG-003-class regression guard).
- `cal_valid_o |-> cal_expect was armed` (aligner bind).

## 7. Docs to update

- `docs/uarch/PUMICE_TRAINING_LAYER_UARCH.md` (new, matching the three existing
  uarch docs) + retire the "MRR not used by pumice" note in
  `docs/uarch/LPDDR2_CA_ENCODING.md:59,162`.
- HAS rev **0.9**: training-layer chapter; MAS rev **0.8**: block pages for
  `pumice_training_layer`, `pumice_zq_ctrl`, `pumice_lp_cal` + ch04 contract rows.
- Fix the stale `**Version:** 0.4` index lines and rebuild the drifted artifacts
  (newest built today is v0.6; book content sits at HAS 0.8 / MAS 0.7).
- Run `check_kmap_rtl_sync.py`.

## 8. Risks / decisions

| Risk | Mitigation |
|---|---|
| JESD bit-level detail wrong (CA word, timing) | Spec facts extracted verbatim from in-repo JESD209-2F PDF (§5.12, §5.12.2, §5.13.3); formatter test encodes the same table |
| Cmd FIFO +1 bit breaks a width assumption | FIFO word is a `gaxi_fifo_sync` data width; no external consumers of the packing outside scheduler/dfi_cmd_path |
| MRR capture races a (forbidden) read return | Arbiter grant contract forbids outstanding reads; aligner sideband only fires when armed |
| Multi-rank ZQ overlap (shared ZQ resistor) | Pumice board targets are single-rank; rank loop left as a documented `generate` hook in `pumice_zq_ctrl` |
| Mode-register shadow corrupted by transient MR10 writes | ZQ MRWs flow through the arbiter maintenance path, never the init shadow path — asserted in scheduler-layer test |
