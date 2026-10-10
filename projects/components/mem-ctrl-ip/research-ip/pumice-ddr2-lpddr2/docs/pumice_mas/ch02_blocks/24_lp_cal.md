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

# LPDDR2 DQ-Calibration Sequencer (`pumice_lp_cal`)

**Module:** `pumice_lp_cal.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent macro:** `pumice_training_layer`
**Status:** implemented and FUB-tested (LPDDR2); inert for DDR2 builds — no MRR

> The DQ-vs-tap sweep lives outside the core, on purpose. This FUB is the
> MRR engine and capture sideband only: it issues the two mode-register
> reads, catches the first return beat of each, and hands the data to
> firmware. The PHY read-delay tap walk and the per-lane compare against
> patterns A/B run in board firmware driving the FPGA IDELAY primitives —
> the core stays DFI-clean.

---

## Purpose

One-shot DQ calibration for LPDDR2 via MRR (Mode Register Read,
JESD209-2F §5.12.2). MR32 returns calibration pattern A (`1010` on DQ0,
mirrored on DQ8 for x16); MR40 returns pattern B (`0011`). Firmware compares
each DQ lane against the expected pattern across its tap sweep and picks
the working window. The FSM here just runs the sequence:

1. Wait for a `cal_start_i` pulse, then wait for the arbiter grant
   (which guarantees all banks idle, no ACT/PRE in flight or guard window,
   no REF recovery, and a drained write path — the JESD209-2F MRR spacing
   rules RD→MRR ≥ BL/2, WR→MRR ≥ WL+1+BL/2+tWTR come along for free).
2. Issue MRR to MR32: `OP_MRS` + `cmd_mrr_o = 1`, row `{4'd0, MA=32, OP=0}`.
   Pulse `cal_expect_o` for one cycle to arm the DFI-layer read aligner.
3. Capture the first `dfi_rddata_valid` beat (MRR data lands
   `RL·tCK + tDQSCK + tDQSQ` after the command; BL=4, but only beat 0
   carries the MR data).
4. Wait `t_mrr_i` cycles (JEDEC tMRR = 2 clocks), issue MRR to MR40,
   capture beat 0 the same way.
5. Set sticky `cal_done_o`. If either readout times out (`t_readout_i`
   cycles with no valid beat), set sticky `cal_err_o` and finish anyway.

The run condition is `init_done_i && (memtype_i == MEMTYPE_LPDDR2)`; DDR2
has no MRR, so the FUB is inert there.

## Parameters

| Parameter        | Default | Meaning                                            |
|------------------|---------|----------------------------------------------------|
| `DFI_DATA_WIDTH` | 128     | Full DFI read-data width; sizes the captured-beat registers. |
| `MR32_INDEX`     | 32      | Pattern-A mode-register index.                     |
| `MR40_INDEX`     | 40      | Pattern-B mode-register index.                     |

## The Eight FSM States

`r_state` is 3 bits, one state per beat of the handshake:

```text
CAL_IDLE           — waiting for cal_start_i
CAL_WAIT_GRANT32   — requesting the arbiter for the MR32 MRR
CAL_PULSE_EXPECT32 — granted; pulsing cal_expect_o to arm the aligner
CAL_WAIT_DATA32    — waiting for the captured MR32 beat / readout timeout
CAL_WAIT_TMRR      — t_mrr_i spacing before the second MRR
CAL_WAIT_GRANT40   — requesting the arbiter for the MR40 MRR
CAL_PULSE_EXPECT40 — granted; pulsing cal_expect_o again
CAL_WAIT_DATA40    — waiting for the captured MR40 beat / readout timeout
```

Grant loads `r_timeout` from `t_readout_i`; each wait-data state decrements
it and escalates to `cal_err` + done at zero. Both captured beats and their
valids are held in registers; data is stable until the next `cal_start`
clears the valids.

`cal_abort_i` (or run-gate loss) returns the FSM to `CAL_IDLE` immediately.
The sticky done/err bits are **not** cleared by abort — only a fresh
`cal_start` or soft reset moves them, matching the `CAL_STATUS` "sticky,
cleared by soft reset" contract. The captured-data valids, though, are
cleared by abort, so a cancelled sequence can't present stale captures as
fresh.

## Interface

### Control, timing, and run gating

| Signal           | Direction | Width | Description                                            |
|------------------|-----------|-------|--------------------------------------------------------|
| `mc_clk`         | in        | 1     | controller clock                                        |
| `mc_rst_n`       | in        | 1     | active-low reset                                        |
| `cal_start_i`    | in        | 1     | start one shot (`CAL_CTRL.cal_start`, self-clearing)    |
| `cal_abort_i`    | in        | 1     | cancel the current sequence (`CAL_CTRL.cal_abort`)      |
| `init_done_i`    | in        | 1     | scheduler init complete                                  |
| `memtype_i`      | in        | —     | `MEMTYPE_LPDDR2` required                                |
| `t_mrr_i`        | in        | 16    | MRR-to-MRR spacing, MC cycles (`CAL_TRAIN_TIMING.t_mrr`, reset 2) |
| `t_readout_i`    | in        | 16    | MRR issue → data timeout (`CAL_TRAIN_TIMING.t_readout`) |

### Maintenance command channel (to the training-layer mux, then the arbiter)

| Signal          | Direction | Width | Description                                           |
|-----------------|-----------|-------|-------------------------------------------------------|
| `cmd_req_o`     | out       | 1     | request in the WAIT_GRANT states                        |
| `cmd_grant_i`   | in        | 1     | arbiter grant back through the mux                      |
| `cmd_op_o`      | out       | —     | always `OP_MRS` — MRR rides the MRS opcode + mrr flag   |
| `cmd_bank_o`    | out       | 3     | 0; the MR index lives in the row field                  |
| `cmd_row_o`     | out       | 18    | `{4'd0, MA[5:0], 8'd0}` — OP field = 0 for MRR          |
| `cmd_mrr_o`     | out       | 1     | formatter MRR select; 1 whenever this FUB drives        |

### Calibration capture handshake (mc_clk domain, synchronized by the layer)

| Signal             | Direction | Width            | Description                                      |
|--------------------|-----------|------------------|--------------------------------------------------|
| `cal_expect_o`     | out       | 1                | single-cycle arm for the rd_aligner sideband      |
| `cal_data_i`       | in        | `DFI_DATA_WIDTH` | captured beat, synchronized up from dfi_clk       |
| `cal_data_valid_i` | in        | 1                | single-cycle "data landed" strobe                 |

### Status and captured data

| Signal           | Direction | Width            | Description                                     |
|------------------|-----------|------------------|-------------------------------------------------|
| `mrr32_data_o`   | out       | `DFI_DATA_WIDTH` | captured MR32 beat 0 (`CAL_MRR32_DATA`)         |
| `mrr40_data_o`   | out       | `DFI_DATA_WIDTH` | captured MR40 beat 0 (`CAL_MRR40_DATA`)         |
| `mrr32_valid_o`  | out       | 1                | MR32 capture is fresh                           |
| `mrr40_valid_o`  | out       | 1                | MR40 capture is fresh                           |
| `cal_busy_o`     | out       | 1                | FSM not in IDLE                                 |
| `cal_done_o`     | out       | 1                | sticky — sequence finished (either outcome)     |
| `cal_err_o`      | out       | 1                | sticky — a readout timed out                    |

## Timing / Behavior

The FSM is single-issue and never overlaps the two MRRs — tMRR spacing is a
hard FSM state, not a counter check folded into a shared datapath. Timeout
coverage: `t_readout_i = 0` makes the wait-data states time out on the first
cycle without data, so programming zero buys an immediate error rather than
an infinite wait (worth knowing before bumping the timeout down).

The arbiter's grant contract is what makes the capture safe: no read may be
outstanding when calibration is active, so the aligner sideband cannot
collide with the normal read FIFO push path (see
[ch04/05](../ch04_apb_config/05_training_interface_contracts.md)).

## Verification Notes (cocotb test plan)

Verified by `dv/tests/fub/test_pumice_lp_cal.py`: the one-shot sequence
(start → grant32 → arm → capture → tMRR → grant40 → arm → capture → done),
readout-timeout error path, abort mid-sequence, MRR row packing
(`MA` + OP=0), and DDR2-inert behavior.

## Open Questions / Future Work

- **Timeout default.** `CAL_TRAIN_TIMING.t_readout` resets to 0, so the
  readout-timeout error path fires immediately (a degenerate default that
  software must reprogram); firmware must program a real window
  (covering `RL·tCK + tDQSCK + tDQSQ` at the current frequency) before
  starting a calibration.
- **x16 DQ8 mirror.** The RTL captures the full DFI beat, so the x16
  DQ[8]-mirrored pattern lands in the CSR with everything else; the
  per-lane compare in firmware handles it.
- **Back-to-back sequences.** A second `cal_start` while busy is ignored
  (the FSM only accepts start in IDLE); firmware paces shots through
  `CAL_STATUS.cal_busy`.
