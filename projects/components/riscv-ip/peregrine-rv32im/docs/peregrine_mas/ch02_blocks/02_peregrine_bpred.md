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

# peregrine_bpred

**Module:** `peregrine_bpred.sv`

## Responsibility

A direct-mapped BTB and a BHT of 2-bit saturating counters (COD Fig 4.65), looked up by the fetch PC in IF and written once per resolved instruction as it leaves EX. With `BP_EN=0` it instantiates no storage and always predicts not taken.

## Parameters

<!-- GEN:params:peregrine_bpred -->

| Parameter | Kind | Type | Default | Description |
|----------------|----------|------------|--------------|------------------------------|
| `BP_EN` | parameter | `bit` | `1'b1` | 1: BTB + BHT prediction; 0: predict not taken (merlin's fetch) |
| `BTB_ENTRIES` | parameter | `int` | `32` | BTB entries, a power of two (PRD P5: 32) |
| `BHT_ENTRIES` | parameter | `int` | `256` | BHT counters, a power of two >= BTB_ENTRIES (PRD P5: 256) |

: peregrine_bpred parameters

<!-- /GEN -->

## Ports

<!-- GEN:ports:peregrine_bpred -->

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `clk` | input | `1` | Clock |
| `rst_n` | input | `1` | Reset (BTB valid bits only) |
| `lookup_pc` | input | `[31:0]` | Fetch PC (IF) |
| `pred_taken` | output | `1` | Guess: taken |
| `pred_target` | output | `[31:0]` | Guess: target (meaningful when taken) |
| `upd_valid` | input | `1` | one resolved instruction, this cycle |
| `upd_pc` | input | `[31:0]` | PC of the resolved instruction |
| `upd_cond` | input | `1` | conditional branch |
| `upd_uncond` | input | `1` | JAL or JALR |
| `upd_taken` | input | `1` | Its resolved direction |
| `upd_target` | input | `[31:0]` | Its resolved target |
| `upd_pred_taken` | input | `1` | what the lookup predicted for it |

: peregrine_bpred ports

<!-- /GEN -->

## Storage

| Table | Entries (default) | Entry | Index | Reset |
|-------|-------------------|-------|-------|-------|
| BTB payload | 32 | tag = PC[31:7], target = PC[31:2], `uncond` | PC[6:2] | None (LUTRAM) |
| BTB valid | 32 bits | - | PC[6:2] | Cleared |
| BHT | 256 | 2-bit counter | PC[9:2] | None (LUTRAM) |

: Predictor storage at the PRD P5 sizes

The tag is every PC bit above the index, so a BTB hit is an exact PC match. Targets are stored as PC[31:2]: IALIGN is 32.

## Lookup (Combinational)

- **Hit:** the entry is valid and its tag equals the PC's.
- **Taken:** a hit on an unconditional entry (JAL, JALR), or a hit on a conditional entry whose BHT counter's high bit is set.
- **Target:** the entry's target, `{target, 2'b00}`.
- On a miss the guess is not taken (the next PC is PC + 4).

The BHT is read only on a hit of a conditional entry, and every counter such a lookup can read was written by the update that installed the entry. That is what lets the BHT go without a reset.

## Update (One per Instruction Leaving EX)

| Resolved instruction | BTB | BHT |
|----------------------|-----|-----|
| Taken conditional branch, no conditional hit (an install) | Write entry, set valid | Write `01` (weakly not taken) |
| Taken conditional branch, conditional hit | Write entry | Step toward taken, saturating at `11` |
| Not-taken conditional branch | - | Step toward not taken, saturating at `00` |
| JAL or JALR (always taken) | Write entry with `uncond = 1`, set valid | - |
| Not a branch, but predicted taken (a stale entry) | Clear valid | - |

: Predictor update rule

**Why install at `01`.** The first build stepped the counter from its old value on install, which can be a value nothing wrote (X in a 4-state simulator; whatever an earlier program left on a board). An install now writes a fixed value. Weakly taken (`10`) was tried first and made an alternating branch mispredict every outcome; weakly not taken (`01`) is a zeroed counter after one taken step, the board's power-up behavior, and won on every predictor stream. The owner approved `01` on 2026-11-25.

**Same-entry read and write.** The update reads the BHT through its own port. An update in the same cycle as a lookup of the same entry is seen by the next lookup.

The write rule in the core (once per instruction, not under `mem_wait`, not during an M hold, not for an instruction a MEM redirect kills) is in "Branch Prediction and Recovery".

---

**Last Updated:** 2026-11-25
