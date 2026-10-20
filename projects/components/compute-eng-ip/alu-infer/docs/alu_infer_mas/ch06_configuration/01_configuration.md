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

# Parameters, Encodings, and Open Items

## Parameters

See Table 2.1: `LINE_W = 32`, `N_LANES = LINE_W/16`, `ACC_W = 32`,
`PIPE_DEPTH` (tag-FIFO entries, default 8 — the stall-tolerance knob),
`ADDER_LATENCY` (the add/sub row's own pipe depth, default 3), and
`TAG_W` (8, per the owner ruling). The only behavior-switch
surface is the opcode table itself — the element model is bf16-only and
rounding is the library's RNE throughout (a dynamic rounding mode is
out of scope by the garuda RNE precedent; any request would raise the
error path, per Chapter 2.4).

## `func_sel` Encoding

| Bits | Field | Encoding |
|------|-------|----------|
| [4:0] | opcode | 0 copy, 1 add, 2 sub, 3 mul, 4 mac, 5 min/max, 6 compare/threshold, 7 relu; 8–31 growth |
| [6:5] | sub_op | row-internal (min/max select; compare operand select); row docs of Chapter 2 |
| [8:7] | reserved | element-width legacy field — reserved under the bf16 model (M6) |

: Table 6.1: `func_sel` fields

## `acc_ctrl` Encoding

| Value | Name | Action |
|-------|------|--------|
| 2'b00 | HOLD | acc unchanged |
| 2'b01 | ACCUMULATE | per-lane `acc <= fma(a, b, acc)` |
| 2'b10 | CLEAR | acc ← +0.0 per lane |
| 2'b11 | DRAIN | present acc (fp32→bf16 RNE) without accumulating |

: Table 6.2: `acc_ctrl` encoding (accepted 2026-10-17 — "works for
now"; revisit at FPGA bring-up if the mac row is reworked)

## Filelists

The RTL lives in the alu-infer component (`alu-infer/rtl/...`,
organized like the other component areas — flat RTL, per-block
filelists, and a `<area>_all.f` master for lint). The block has
its own unit filelist,
`alu-infer/rtl/filelists/alu_infer_top.f` — the four ALU sources plus the
`rtl/math` filelists of the instantiated library blocks — which is what
the unit testbench (`alu-infer/dv/tests/test_alu_infer.py`) compiles.
`alu-infer/rtl/filelists/alu_infer_all.f` is the lint master. The
cell-level filelists (`cell_top.f`, `cell_all.f`) include the block's
filelist for integration, since slice 3+ instantiates `alu_infer_top`
inside the cell.

## Open Items Register

Carried from PRD §8, with the MAS additions M7; these are the only
decisions this specification does not make.

| ID | Item | Blocking |
|----|------|----------|
| M1 | NaN/inf semantics in min/max and activations (IEEE `minNum` propagation vs inference "ignore NaN") | golden model for rows 5, 7 |
| M2 | Whether library IEEE exception outputs forward into `result_flags` | observability only |
| M3 | Denormal/FTZ policy cell-wide vs per-block `SUBNORMAL_SUPPORT` defaults | special-value grid |
| M4 | `threshold_imm` encoding (raw bf16 pattern vs converted small int) | opcode-6 tests |
| M5 — **closed 2026-10-17 (owner ruling)** | `result_flags` format: one mask bit per lane, packed low in a `LINE_W` line; port width `LINE_W` | closed |
| M6 | `FUNC_SEL` reserved-field disposition (retire vs keep for fp8/integer growth) | register map freeze |
| M7 — **accepted 2026-10-17** | mac presents the post-update fp32 accumulator rounded to bf16 per invocation; `DRAIN` presents without accumulating — accepted as drafted ("works for now"); revisit if FPGA latency work rewrites the mac row | accepted |
| M8 | Per-row natural-latency table and `PIPE_DEPTH`/`ADDER_LATENCY` values — **deferred to FPGA bring-up** (owner direction 2026-10-17): tuned against hardware, with possible aggressive per-function latency minimization; the tag-join contract absorbs faster or deeper rows without interface change (each row carries its tag through its own pipeline and joins by compare) | FPGA bring-up |

: Table 6.3: open items M1–M8

M1, M3 and M4 resolve from the `rtl/math` library blocks' existing
semantics wherever those semantics are already fixed — the work is
recording the choice, not inventing it. M2 and M6 are cell-level and
ride the cell PRD's next edit. **M5 is closed** (owner ruling
2026-10-17): one mask bit per lane, packed low in a `LINE_W` line. M7
is this MAS's one novel decision and is the first candidate for owner
review of this document.

---

**Last Updated:** 2026-10-17
