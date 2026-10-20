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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Design Philosophy and Scope

## What This Block Is

The **cell** is the tile's compute unit: sixteen of them make a tile.
Each cell contains exactly one `delta_mesh_cell` node, instantiated
inside `cell_top`, with its local port (port index 8, `P_LOCAL`) facing
the cell's internal datapath and its eight mesh-facing ports passing
through to the cell boundary. That containment is the entire
cell↔delta relationship: the node is governed by delta's own HAS/MAS,
and everything else in the cell is the cell's own design, speaking the
tile-level contracts of `TILE_SPEC` §11.

The cell's job is to turn delta-delivered operand lines into
result lines that leave back through the delta mesh toward RAPIDS:

1. **Program.** `cfg` packets write the §7 registers — `FUNC_SEL`,
   `OP_SRC`, batching knobs, and the persistent operands `A`–`D`, `T`.
2. **Fill.** `mem` packets write operand lines into the input memory,
   each line tagged with the packet's source coordinate.
3. **Consume.** The execution FSM pops `OP_LINES` input lines per
   invocation, issues them to the ALU, and pushes result lines into the
   result memory.
4. **Credit return.** As each input line is consumed, the credit logic
   returns credits to the recorded source.
5. **Emit.** The packetizer batches result flits into packets and sends
   them toward the gatling-programmed drain destination, spending the
   cell's `TILE_LAND_FLITS` strap counter.

Everything — data, config, and programming — arrives in-band on delta
(PRD §3; TILE_SPEC §11.13; alu-infer PRD §5).

## Scope and Deferrals

In scope for this MAS:

- The slice-1 RTL as built: `cell_top`, `cell_rx`, `cell_cfg_regs`,
  `cell_mem_in`, `cell_mem_out`
- The slice-2/3 modules specified here: `cell_credit`,
  `cell_packetizer`, `cell_exec_fsm`
- The ALU↔FSM seam (the ALU itself is specified in the alu-infer MAS)
- The credit-loop and result-packetization behavior
- The verification plan for the credit-loop and ALU-run tests

Out of scope or deferred (PRD §10–11):

- Tetrad/root node internals and the tetrad control core
- RAPIDS internals and the CXS migration sequencing
- Fabric-level Z stacking
- Cell-destined result sending (`DEST` override) pending the tile-spec
  cell→cell grant extension
- Loading `A`–`D` from the input memory
- Wider-than-32-bit lines and element widths other than bf16

## MAS Decisions at a Glance

This book closes the PRD §12 open questions with the following
implementation decisions, each marked "MAS decision" with rationale in
the chapter where it lives:

| Decision | Value | Rationale |
|---|---|---|
| Input memory depth (`IN_DEPTH`) | 32 lines | Matches result memory depth; gives a 32-flit advertisement today; simple power-of-two addressing |
| Result memory depth (`OUT_DEPTH`) | 32 lines | Sized to absorb one full input run's results at the default `OP_LINES`=1; deeper than the default `TILE_LAND_FLITS` strap so the memory is not the emit bottleneck |
| Line width (`LINE_W`) | 32 bits (2×bf16) | bf16 element model per alu-infer PRD §2; slice-3 may pack two lines per 64-bit flit |
| Boot advertisement | 32 flits | One 32-bit line per 64-bit payload flit today; the value is `IN_DEPTH` expressed in flits |
| Credit batch size (`CREDIT_BATCH_N`) | Default 1 | Exact per-line behavior; configurable for lower fabric traffic |
| Partial-batch credit timeout | 64 cycles | Bounded drain latency without adding credit traffic at N=1 |
| Result batch size (`EMIT_BATCH_X`) | Configurable, default 4 | Amortizes header overhead while respecting the 16-flit strap |
| Packetizer flush conditions | Batch-full OR `CTRL.flush-and-send` | Simple, deterministic; idle-timeout and end-of-job flush are deferred |
| Strap counter default | 16 flits | Mirrors the Hive default `TILE_LAND_FLITS`; restored by RAPIDS `credit`/`add` returns |
| Local-port data width (slice 2/3) | Delta `DATA_WIDTH` (64b today) | Beat-chained header rule (owner ruling 2026-10-18): the 128-bit tile header spans the first `ceil(128/DW)` payload beats, LSB-first; no widening, no width conversion. Supersedes the 0.10 draft's 128-bit local port |

: Table 1.1: Summary of MAS decisions

## Relationship to the ALU

The cell owns the memories, the FSM, the packetizer, and the credit
logic. The ALU block — `alu-infer` — is the cell's compute engine and is
governed by its own PRD and MAS. The cell MAS cites the alu-infer
contracts at the FSM seam and does not restate the ALU internals.

---

**Last Updated:** 2026-10-18
