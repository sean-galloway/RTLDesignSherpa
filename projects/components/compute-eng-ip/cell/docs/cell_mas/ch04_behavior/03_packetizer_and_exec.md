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

# Packetizer and Execution FSM

## Packetizer

### MAS Decision: Batching and Flush Conditions

**MAS decision:** The packetizer batches result flits up to
`EMIT_BATCH_X` and flushes on either of two conditions:

1. The batch accumulator holds `EMIT_BATCH_X` flits.
2. `CTRL.flush-and-send` is written (bit 2 of `CTRL`).

An idle-timeout flush and an end-of-job marker flush are documented as
deferred (PRD §12; PRD §11). This keeps slice-2 behavior deterministic
and testable: a testbench can either fill a batch or force a flush.

### MAS Decision: Strap Counter Initialization

**MAS decision:** The packetizer maintains a strap counter initialized
from a cell parameter `TILE_LAND_FLITS` with a default of 16 flits. The
counter is spent per flit sent (header included) and is restored by
RAPIDS `credit`/`add` returns.

Rationale: The default 16 matches the Hive-set `TILE_LAND_FLITS`
default in TILE_SPEC §11.9. The counter is private to this cell and
never goes negative; a packet is presented only while the counter covers
the entire packet, header included.

### Header Build

The packetizer builds write-format packets (`ptype=mem`, `op=0`) with
the `TILE_SPEC` §11.5 tile header as the first payload beat(s). The
header fields are:

| Field | Value |
|---|---|
| Destination coordinate | Gatling-programmed drain destination (see below) |
| Source coordinate | This cell's external ID `{ext=1, level=0, X, Y, Z}` |
| `ptype` | `mem` (2) |
| `op` | 0 (write) |
| Length | Payload bytes that follow |
| Target address | Programmed by the drain command (memory address in the sink channel) |
| Tag | Programmed sink channel |

: Table 4.2: Result-packet header fields

**MAS decision on transport:** The packetizer uses the `TILE_SPEC`
§11.6 two-header model with the beat-chained header rule (owner ruling
2026-10-18 — every link keeps its own width):

- The delta route header is placed in `TUSER` of the head beat.
- The 128-bit tile header is placed in the first `ceil(128/DW)` payload
  beats, LSB-first — on the 64-bit local port: beat 0 = `header[63:0]`,
  beat 1 = `header[127:64]`.
- Payload beats follow.

The local port does not widen. This supersedes slice-1's provisional
64-bit TUSER packing and the 0.10 draft's 128-bit local-port widening.

### Destination and Tag Programming

The cell does not choose the result destination. Gatling (the tetrad
engine) commands the drain and tells the cell where to send it
(TILE_SPEC §11.14; PRD §6.3).

**Precedence:** The operational drain destination is held in
`FLUSH_DEST` (offset `0x54`) and the sink-channel tag in `FLUSH_TAG`
(offset `0x58`). These are programmed by gatling (via `cfg` write or an
extended `CTRL` flush command) and are what the packetizer uses when
`CTRL.flush-and-send` is written. The legacy `DEST` register (offset
`0x38`) is **reserved** for the deferred cell→cell result path; it is
not used for rapids-bound drains. `DEST` becomes operational only after
the tile-spec cell→cell credit/grant extension lands (TILE_SPEC §10);
until then, result traffic is RAPIDS-bound and `FLUSH_DEST`/`FLUSH_TAG`
take precedence.

Rationale: This gives gatling a concrete mechanism to command a flush
without requiring a new packet type or a sideband interface, while
keeping the `DEST` register available for the future peer-cell path.

### Strap Accounting

Each packet costs one header flit plus one flit per payload line today.
The packetizer checks:

```text
strap_counter >= 1 + payload_flits
```

before presenting `tvalid`. It decrements the counter by one per flit
sent. RAPIDS returns credits as it drains the cell's landing space; the
returns are `credit`/`add` packets that increment the strap counter.

## Execution FSM

### Pop → Issue → Push Loop

`cell_exec_fsm` runs the compute loop:

1. **Pop.** When enabled and not busy, pop `OP_LINES` input lines from
   `cell_mem_in`, advancing `IP` by one per line. Capture the source
   coordinate of the first line (all lines of one invocation are
   expected to come from the same source; if they differ, the first
   line's source is used for credit return).
2. **Issue.** Present the operand lines to the ALU and assert the issue
   `valid`. Wait for `ready`; hold operands and `func_sel` stable while
   `ready` is low.
3. **Push.** When the ALU asserts `result_valid` and the FSM asserts
   `result_ready`, push the result line into `cell_mem_out`, advancing
   `OP` by one.

The loop is pipelined: while one invocation computes, the FSM can pop
and issue the next, as long as the ALU's elastic pipeline accepts it
(II=1 while draining).

### MAS Decision: Operand-Source Mux

**MAS decision:** The operand-source mux is configured by `OP_SRC`:

| `OP_SRC` value | `op_line_a` source | `op_line_b` source |
|---|---|---|
| 0 | input-memory pop | input-memory pop |
| 1 | `A` | `A` |
| 2 | `B` | `B` |
| 3 | `C` | `C` |
| 4 | `D` | `D` |

: Table 4.3: `OP_SRC` encoding

The two sides are controlled by independent 3-bit fields in `OP_SRC`:
`sel_a[2:0]` and `sel_b[2:0]`. Reset value is 0 (both operands from
memory). The `T` register supplies `threshold_imm` for opcode 6
(compare/threshold).

### IP/OP Pointer Behavior

`IP` and `OP` are 32-bit registers that auto-increment on pop and push
respectively. They wrap at `IN_DEPTH` and `OUT_DEPTH`:

```text
IP_next = (IP + 1) mod IN_DEPTH
OP_next = (OP + 1) mod OUT_DEPTH
```

`CTRL.soft_reset` clears both pointers to 0 and clears `IRQ_STATUS`.
Software may also seed them through AXIL or `cfg` writes.

### Gatling as the Cell ALU Sequencer (owner ruling 2026-10-19)

**MAS decision:** The slice-3 `cell_exec_fsm` remains the standalone
bring-up driver for the cell, preserving the same POP → issue → PUSH
client contract. In the tetrad-integrated tile, **gatling** (the
tetrad barrel-core engine) sequences the cell's alu-infer ALU directly:

- `POP` reads operand line(s) from the cell's input memory and presents
them to the ALU issue handshake.
- `PUSH` retires result line(s) from the ALU and writes them into the
cell's result memory.
- `FLUSH` programs `FLUSH_DEST`/`FLUSH_TAG` and triggers the packetizer
drain.
- `CFG`/`ECTX`/`KICK`/`WAIT` carry tetrad-level context and control.

Gatling never originates config traffic that belongs in the cell's
`cfg` stream; cell programming remains in-band per the standing owner
ruling 2026-10-17. The gatling PRD v0.2 owns the `Xcell` instruction
encodings (`CFG`, `POP`, `PUSH`, `ECTX`, `FLUSH`, `KICK`, `WAIT`).

### ALU Hookup

The FSM drives the ALU's elastic valid/ready interface per the
alu-infer MAS:

| Signal | Direction | Purpose |
|---|---|---|
| `alu_valid` | FSM → ALU | Issue valid |
| `alu_ready` | ALU → FSM | Issue ready |
| `op_line_a` | FSM → ALU | Operand A line |
| `op_line_b` | FSM → ALU | Operand B line |
| `threshold_imm` | FSM → ALU | bf16 threshold immediate (from `T`) |
| `func_sel` | FSM → ALU | {opcode, sub-op, reserved} |
| `acc_ctrl` | FSM → ALU | CLEAR / ACCUMULATE / DRAIN for MAC |
| `result_line` | ALU → FSM | Result line |
| `result_valid` | ALU → FSM | Result valid |
| `result_ready` | FSM → ALU | Result ready |

: Table 4.4: ALU↔FSM seam signals

The function/opcode table is defined in alu-infer PRD §3 and
implemented per the alu-infer MAS. The cell MAS does not restate it.

### Issue Tag and Same-Tag Alignment (ratified spec — RTL pending)

**MAS decision:** When the scheduler loads a new function into the ALU
pipeline, an **8-bit tag** is assigned, common to every op of that
invocation group that must complete together. A **tag FIFO** tracks the
in-flight groups. Each op's `result_valid` asserts only when *every*
`result_valid` of ops carrying the same tag has asserted — so ops that
were scheduled together finish together, and the elastic pipeline's
per-op readiness is gated to the group boundary.

Rationale (owner ruling): if two ops are scheduled in the same clock
they should finish at the same time, and the scheduler programs the
valid/ready behavior it wants (including feedback cases) through this
tag grouping rather than through pipeline-depth matching. This takes
care of the elastic alignment naturally: the group is atomic at the
result boundary even though individual ops may have different internal
latencies.

Status: ratified with the alu-infer work at rev 0.50; **not yet in the
alu-infer RTL or the alu-infer MAS** — the tag assign/FIFO/align gate of
Figure 2.3 is the specified target, not the current implementation.

### MAC Accumulation

MAC behavior is inherited from the alu-infer contract: the FMA computes
the bf16 product exactly in fp32, accumulates per-lane in fp32, and
rounds to bf16 once per result-line presentation. The FSM sequences
`acc_ctrl` (CLEAR at layer boundaries, ACCUMULATE for steps, DRAIN for
the final values) without changing the ALU interface.

### Soft Reset

`CTRL.soft_reset` (bit 1) pulses `o_soft_rst` for one cycle. The FSM
responds by clearing `IP` and `OP` and dropping any in-flight issue
request. The ALU's reset behavior is defined in the alu-infer MAS.

---

**Last Updated:** 2026-10-19
