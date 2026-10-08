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

# Training: LPDDR2 ZQ and DQ Calibration

The training layer is `pumice_training_layer` (`rtl/macro/pumice_training_layer.sv`),
the fourth layer of the core, instantiated in `pumice_core` between the scheduler
layer and the DFI layer ("Layer 2b" in the RTL). It holds the two calibration FUBs —
`pumice_zq_ctrl` (periodic ZQ calibration) and `pumice_lp_cal` (one-shot DQ
calibration via mode-register reads) — muxes both onto a single maintenance command
channel into the scheduler's arbiter, and owns the `mc_clk` ↔ `dfi_clk` clock
crossing for the read-aligner calibration sideband.

Both FUBs run only when `init_done` is set and `memtype == MEMTYPE_LPDDR2`; DDR2
has no ZQ pin and no MRR mechanism, so the entire layer is inert for DDR2 builds.
That is an elaboration-free inertness — same RTL, gates low — so the existing DDR2
test suites run unchanged beside it.

## The family rule: interfaces in hardware, searches in firmware

Scoria settled this for DDR3 write leveling (decision D2), andesite carried it to
read leveling and LPDDR4 CA training, and pumice makes the same decision for the
same reasons: the controller provides the interface — the MRR engine, the timing
windows, the capture sideband, the telemetry — and the search runs in firmware. A
DQ-vs-read-delay-tap sweep's step size, tap count and temperature behaviour are PHY
properties, not controller properties; a calibration bug should be a script edit,
not a respin. Concretely, the DQ-cal sweep (walk the board's FPGA IDELAY taps,
capture, compare) lives in board firmware driving the PHY primitives directly. The
core exposes `cal_start` and the captured MRR data; it deliberately contains **no**
PHY-primitive logic and gained **no** new top-level ports for training.

LPDDR2's JEDEC menu is also smaller than DDR3/LPDDR4's, and the layer does not
invent the missing entries. Write leveling, read leveling, DLL calibration and CA
training do not exist in LPDDR2 — verified against the JESD209-2F mode-register map
(MR41–47 are "Do Not Use", MR48–62 are reserved; CA training is an LPDDR4 MPC
mechanism owned by andesite's training layer). What LPDDR2 actually offers is two
mechanisms, both implemented here: ZQ calibration through MR10 writes, and DQ
calibration through MRR reads of MR32/MR40.

## `pumice_training_layer`: arbitration and CDC

The layer is a passive wiring and arbitration shell; run gating lives inside the
two FUBs.

| Responsibility | Detail |
|---|---|
| FUB holder | `u_zq` (`pumice_zq_ctrl`) + `u_lp_cal` (`pumice_lp_cal`) |
| One-active command mux | Both FUBs share one `trn_cmd_*` channel; priority ZQ > lp_cal, because ZQ is periodic maintenance while lp_cal is a firmware-initiated one-shot. `trn_cmd_mrr_o` is `0` for ZQ (MRW) and `1` for lp_cal (MRR) |
| Calibration sideband CDC | `cal_expect` crosses `mc_clk` → `dfi_clk` as a `sync_pulse` (one mc_clk assertion produces exactly one dfi_clk pulse); the captured beat crosses back through a `cdc_synchronizer` (data held stable by the aligner until the next arm) with a `sync_pulse` for the valid strobe |
| Status aggregation | `cal_busy_o = zq_busy \|\| lp_busy`; `cal_done` / `cal_err` come from lp_cal; `zq_busy` / `zq_overdue` / `zqcs_total` from ZQ |

: Table 3.0: `pumice_training_layer` responsibilities

`pumice_core` wires the layer exactly as andesite wires its training layer: the
`trn_cmd_*` channel nets into the scheduler layer's new maintenance client ports,
and `cal_expect_o` / `cal_data_i` / `cal_valid_i` net into the DFI layer's read
aligner. `pumice_top` connects the CSR side (`CAL_CTRL` fields, timing registers)
and harvests status back into `CAL_STATUS` and the `CAL_MRR32/40_DATA` slices.

## `pumice_zq_ctrl`: periodic ZQ calibration as maintenance traffic

LPDDR2 has no dedicated ZQCS/ZQCL command (unlike DDR3); both are **MRW writes to
MR10**, OP = `0x56` (short, ZQCS) or `0xAB` (long, ZQCL), per JESD209-2F §5.13.3.
ZQ Init (`0xFF`, tZQINIT) already exists in `init_sequencer` state `S_L_ZQ`; this
FUB owns everything after init: the periodic calibration that keeps the output
impedance inside its ±15% window as temperature and voltage drift.

The FUB **never generates the command itself**. It raises a request and, on grant,
the arbiter issues the FUB's payload verbatim — `OP_MRS` with the row packed as
`{MR10_index[5:0], OP[7:0]}` in the row field (bank 0; the MR index rides the row
field, the same packing init MRW uses). The four-state FSM:

1. **Interval countdown** — `CAL_ZQ_INTERVAL` MC cycles between calibrations;
   `0` disables the engine entirely. `zq_en` gates the whole FUB.
2. **Request** — on expiry, raise `zq_req` and hold it. While waiting ungranted
   under demand, the FUB marks itself `zq_overdue`.
3. **Mode-C deferral** (`zq_defer_en`) — at expiry, if the scheduler reports
   sustained demand, the request can be held in `ZQ_DEFER` instead, up to
   `zq_overdue_max` MC cycles (13-bit, `0` = no cap), after which the request fires
   regardless. A deferral that overruns its cap — or any nonzero deferral that
   exits on demand loss — escalates the request to **ZQCL**: after deferred
   calibration the long calibration re-establishes the ±15% RON budget that the
   short one only trims.
4. **Post-grant hold** — on grant the FUB loads `t_zqcs` or `t_zqcl`
   (`CAL_ZQ_TIMING`) and asserts `cal_busy` for that window: JEDEC forbids other
   data-bus activity during calibration, so the arbiter must keep demand quiet
   until the window expires. Only then does the interval reload.

Two integration facts worth recording. First, the FUB's `demand_i` port exists
for the Mode-C policy but is **tied to `1'b0` in the committed layer** — the
scheduler's demand sideband is not wired through the training layer yet, so in
the current integration expiry requests immediately (ZQCS, never deferred), and
`zq_overdue` can never assert — both the deferral entry condition and the
request-state overdue set read `demand_i`. The deferral policy is implemented
and FUB-tested; the hookup is the remaining wiring. Second, the
MR10 writes are **transient commands, never shadowed**: the ZQ MRW flows through
the arbiter's maintenance path straight to the formatter, and `mode_register`'s
shadow is written only by `init_sequencer`, so a periodic ZQ calibration can never
disturb the decoded CL/CWL/BL. Multi-rank ZQ (a shared ZQ resistor across ranks)
is left as a documented `generate` hook; the board targets are single-rank, and
the arbiter's pick is single-rank in v1 anyway.

ZQ bus placement follows the all-banks-idle grant contract rather than the JEDEC
minimum: LPDDR2-S4 requires all banks precharged for ZQ calibration while
LPDDR2-N permits Idle-or-Active; the conservative contract satisfies both.

## `pumice_lp_cal`: one-shot DQ calibration over MRR

JESD209-2F §5.12.2 defines DQ calibration: MRR reads of MR32 (pattern A, `1010`)
and MR40 (pattern B, `0011`) make the DRAM drive a known, training-only pattern
onto DQ, so firmware can observe the read-capture timing without any memory array
in the loop. `pumice_lp_cal` is the one-shot sequencer that issues those two
reads and captures the answers; what firmware does with the answers — the tap
sweep — is deliberately outside the core.

The eight-state FSM, started by a `cal_start` pulse (a self-clearing CSR write):

1. Wait for the maintenance grant (the arbiter's all-banks-idle contract plus the
   `w_out_safe` demand gate leave no read or write data in flight — which also
   satisfies the JEDEC MRR spacings: RD→MRR ≥ BL/2, WR→MRR ≥ WL+1+BL/2+tWTR).
2. Issue MRR to **MR32** — `OP_MRS` with the MRR flag set, row
   `{MR32_index[5:0], OP=8'h00}` — and pulse `cal_expect` for one cycle, arming
   the DFI-layer read aligner.
3. Capture the first `dfi_rddata_valid` beat (MRR data lands
   `RL·tCK + tDQSCK + tDQSQ` after the command; BL=4, only beat 0 carries the MR
   data on DQ[7:0], with x16 devices mirroring the pattern on DQ[8]). A
   `t_readout` timeout without a beat sets sticky `cal_err` and ends the run.
4. Wait `t_mrr` (JEDEC §5.12: 2 clocks, the CSR reset default), then repeat for
   **MR40**.
5. On the MR40 capture set sticky `cal_done`. Both captured beats are exposed to
   firmware through `CAL_MRR32_DATA` / `CAL_MRR40_DATA` (full DFI read width,
   four 32-bit slices each at the default 128-bit geometry).

`cal_abort` (or losing the run condition mid-sequence) returns the FSM to idle;
abort additionally drops the captured-data valids. The sticky `cal_done` /
`cal_err` survive both — they are cleared only by soft reset — so a host can
always distinguish "never ran", "ran and converged", "ran and timed out", and
"ran, aborted" after the fact.

## The MRR path: one new bit, not a new opcode

`dram_op_e` stays exactly as wide as it was — all 16 opcodes are consumed and MRR
never enters the demand path. Instead MRR rides the existing `OP_MRS` as a new
1-bit flag, end to end:

- The arbiter passes the granted maintenance op **verbatim** (no re-encoding) and
  latches the requester's `trn_cmd_mrr_i` into the command word.
- The scheduler's output cmd FIFO word grows by one bit to
  `{mrr, ap, col, row, bank, rank, op}` (pack site `pumice_scheduler_layer.sv`,
  unpack site `pumice_dfi_cmd_path.sv`). Demand commands simply carry `mrr = 0`.
- In `dfi_cmd_formatter`'s `OP_MRS` branch, `cmd_mrr_i` drives **CA3r**: MRW and
  MRR share the same MA/OP field packing — MA[7:0] on
  `{CA1f, CA0f, CA9r..CA4r}` — and MRR is MRW with CA3r inverted, bit-exact to
  JESD209-2F §5.12 (the OP field is don't-care-zero for MRR; the lp_cal row packs
  it 0). The `lpddr2_mrr` formatter test encodes the same table.
- No formatter change was needed for ZQ: LPDDR2 has no ZQCS/ZQCL opcodes, so
  those encodings remain NOP at the formatter's default branch — LPDDR2 ZQ is
  pure MRW.

On the return side, `pumice_dfi_rd_aligner` gains a calibration capture sideband
in the `dfi_clk` domain: a single-cycle `cal_expect_i` arms a capture register;
the first `dfi_rddata_valid` beat is latched into `cal_data_o` (full DFI read
width, held until the next arm) with a one-cycle `cal_valid_o` pulse, and the
register disarms. The sideband cannot collide with the normal read FIFO push
path because it only fires while armed, and the arbiter's grant contract
guarantees no read is outstanding when calibration runs.

## Arbitration policy

The scheduler's arbiter gains exactly one maintenance client (`trn_cmd_*`), in
the family's standing shape — the same contract scoria and andesite use for ZQ
and training. Priority, descending: **init > refresh > trn > demand** (column,
then ACT, then PRE). The training branch fires only under `w_trn_safe`: every
bank idle in the registered view, no row-affecting command in flight or inside
its 2-cycle guard window, no tRFC recovery running, and no grant in flight. The
granted op passes through verbatim; the grant is a single-cycle pulse on the fire.
Refresh outranks training, so a pending refresh drains banks and wins the bus
first; training outranks every demand class.

The post-grant hold is where BUG-003 discipline matters. Both FUBs drive
`cal_busy` during their bus-quiet windows (ZQ hold, lp_cal until done), and the
arbiter folds `cal_busy_i` into `w_out_safe` for **every demand class** — ACT,
RD/WR and PRE all carry a `!cal_busy_i` term, while the training class itself is
unconditional. The gate lives in the fire stage, never the pick cone:
`cmd_valid_o = r_pick_valid && w_out_safe` and
`w_fire_out = r_pick_valid && cmd_ready_i && w_out_safe`, so a pick the safety
gate rejects is never pushed to the cmd FIFO and the fire is the push by
construction. That is precisely the invariant BUG-003 restored for the bank
timers; the training gate had to land there, not in the pick pipeline, or it
would have reopened the same divergence.

## CSR summary

The layer is controlled and observed through seven registers in the 0x0A0 block
of `pumice_csr` (field definitions and resets: `rtl/macro/pumice_csr.rdl`):

| Address | Register | Access | Contents |
|---|---|---|---|
| 0x0A0 | `CAL_CTRL` | rw | `zq_en[0]`, `zq_defer_en[1]` (Mode-C), `cal_start[4]` (wo, self-clearing), `cal_abort[5]` (wo), `zq_overdue_max[28:16]` (max deferral, 0 = no cap) |
| 0x0A4 | `CAL_ZQ_INTERVAL` | rw | ZQCS interval in MC cycles, 0 = disabled |
| 0x0A8 | `CAL_ZQ_TIMING` | rw | `t_zqcs[15:0]`, `t_zqcl[31:16]` post-grant hold windows |
| 0x0AC | `CAL_TRAIN_TIMING` | rw | `t_mrr[15:0]` (reset 2), `t_readout[31:16]` MRR issue→data timeout |
| 0x0B0 +4× | `CAL_MRR32_DATA[0..3]` | ro | Captured MR32 beat 0, four 32-bit slices of the DFI read width |
| 0x0E0 +4× | `CAL_MRR40_DATA[0..3]` | ro | Captured MR40 beat 0, four 32-bit slices |
| 0x0F0 | `CAL_STATUS` | ro | `zq_busy[0]`, `cal_busy[1]`, `cal_done[2]` (sticky), `cal_err[3]` (sticky), `zq_overdue[4]`, `zqcs_total[31:16]` |

: Table 3.1: Training-layer CSR summary

The data arrays start at 0x0B0 and 0x0E0 because the retired 0x0C0–0x0DC hole is
never reused (pumice doctrine) — 0x0E0 clears it. `cal_done` / `cal_err` are
sticky and clear only on soft reset.

## Verification and integration notes

- **FUB**: `test_pumice_zq_ctrl.py` (interval expiry, Mode-C deferral, overdue →
  ZQCL select, hold window, DDR2-inert) and `test_pumice_lp_cal.py` (one-shot
  sequence, MRR32 → capture → tMRR → MRR40 → capture, timeout error, abort).
- **FUB**: `test_dfi_cmd_formatter.py::lpddr2_mrr` checks the MRR CA encoding
  against JESD209-2F §5.12; `test_pumice_dfi_rd_aligner.py::test_pumice_dfi_rd_aligner_cal_capture`
  checks the sideband capture with zero reads outstanding and no interference
  with normal returns.
- **Macro**: `test_pumice_scheduler_layer.py` (training priority vs refresh /
  demand, all-banks-idle gating, demand blocked during `cal_busy`, the
  fire==valid invariant). The command-stream checker allows MRR and MRW-MR10 in
  its stream rules.
- **Top**: the CSR/top tests drive an end-to-end `cal_start` on the LPDDR2 model
  and observe both captured patterns; ZQCS MRW at interval with demand blocked.
- **TB tie-off**: `pumice_core_tb_top.sv` ties every training input to 0
  (`zq_en`, `zq_defer_en`, `zq_interval`, `t_zqcs/t_zqcl`, `zq_overdue_max`,
  `cal_start`, `cal_abort`, `t_mrr`, `t_readout`) and leaves the status outputs
  open — that TB scores the datapath and paging sweep, not calibration. Enables
  at 0 make both FUBs inert by construction.
