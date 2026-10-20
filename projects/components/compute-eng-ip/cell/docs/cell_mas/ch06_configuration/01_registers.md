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

# Register Map and MAS Decisions

## Register Map

The v1 register map is identical to PRD §7, with two MAS-added
operational registers for the gatling-programmed drain command.

| Offset | Register | Notes |
|---|---|---|
| 0x00 | `CTRL` | enable, soft reset, flush-and-send |
| 0x04 | `STATUS` | busy, input-empty, result-nonempty, strap-nonzero (RTL alias `status_grant_nonzero`) |
| 0x08 | `FUNC_SEL` | opcode (5b) + sub-op (2b) + reserved (2b) |
| 0x0C | `OP_LINES` | input lines per function invocation |
| 0x10 | `EMIT_BATCH_X` | flits per result packet |
| 0x14 | `CREDIT_BATCH_N` | consumed lines per credit packet per source |
| 0x18 | `IRQ_EN` | done, error, strap-starved (RTL alias `IRQ_GRANT_STARVED_BIT`), credit-timeout enables |
| 0x1C | `IRQ_STATUS` | write-1-clear status |
| 0x20 | `A` | persistent operand A |
| 0x24 | `B` | persistent operand B |
| 0x28 | `C` | persistent operand C |
| 0x2C | `D` | persistent operand D |
| 0x30 | `T` | bf16 threshold immediate |
| 0x34 | `OP_SRC` | operand-source mux: `sel_a[2:0]`, `sel_b[2:0]` |
| 0x38 | `DEST` | deferred cell-destined destination |
| 0x3C | `IP` | input-memory read pointer |
| 0x40 | `OP` | result-memory write pointer |
| 0x44 | `CNT_LINES_IN` | lines received |
| 0x48 | `CNT_LINES_OUT` | results produced |
| 0x4C | `CNT_CREDITS` | credit packets returned |
| 0x50 | `CNT_PKTS` | result packets sent |
| 0x54 | `FLUSH_DEST` | **MAS-added:** gatling-programmed drain destination coordinate |
| 0x58 | `FLUSH_TAG` | **MAS-added:** gatling-programmed sink-channel tag |

: Table 6.1: Cell register map

## Bit Fields

### `CTRL` (0x00)

| Bit | Name | Purpose |
|---|---|---|
| 0 | `EN` | Enable execution FSM |
| 1 | `SOFT_RST` | Soft reset: clears `IP`, `OP`, `IRQ_STATUS`; pulse lasts one cycle |
| 2 | `FLUSH` | Packetizer flush-and-send: emit whatever is buffered now |

: Table 6.2: `CTRL` bit fields

### `STATUS` (0x04) — read-only

| Bit | Name | Purpose |
|---|---|---|
| 0 | `BUSY` | FSM busy (slice 3) |
| 1 | `INPUT_EMPTY` | Input memory empty |
| 2 | `RESULT_NONEMPTY` | Result memory not empty |
| 3 | `STRAP_NONZERO` | Strap counter > 0. Slice-1 RTL still names this bit `STATUS_GRANT_NONZERO_BIT` / `status_grant_nonzero`; the doc term is canonical. |

: Table 6.3: `STATUS` bit fields

### `FUNC_SEL` (0x08)

| Bits | Field | Purpose |
|---|---|---|
| 4:0 | `opcode` | ALU opcode (alu-infer PRD §3) |
| 6:5 | `sub_op` | Sub-opcode, e.g. min vs max, compare vs threshold |
| 8:7 | `reserved` | Reserved under the bf16-only model |

: Table 6.4: `FUNC_SEL` fields

### `OP_SRC` (0x34)

| Bits | Field | Encoding |
|---|---|---|
| 2:0 | `sel_a` | 0=memory pop, 1=A, 2=B, 3=C, 4=D |
| 5:3 | `sel_b` | 0=memory pop, 1=A, 2=B, 3=C, 4=D |
| 31:6 | reserved | 0 |

: Table 6.5: `OP_SRC` fields

### `IRQ_STATUS` / `IRQ_EN`

| Bit | Name | Purpose |
|---|---|---|
| 0 | `DONE` | Computation/drain complete |
| 1 | `ERROR` | Dropped packet or fatal protocol error |
| 2 | `STRAP_STARVED` | Packetizer has data but no strap. Slice-1 RTL still names this bit `IRQ_GRANT_STARVED_BIT`; the doc term is canonical. |
| 3 | `CREDIT_TIMEOUT` | Partial-batch credit timer fired (informational) |

: Table 6.6: IRQ fields

## MAS Decisions Revisited

| Decision | Where in this book | Register / parameter |
|---|---|---|
| Input/result memory depth = 32 lines | Chapter 4.2 | `IN_DEPTH`, `OUT_DEPTH` parameters |
| Boot advertisement = 32 flits | Chapter 4.2 | Derived from `IN_DEPTH` |
| Credit batch default = 1 | Chapter 4.2 | `CREDIT_BATCH_N` register |
| Partial-batch timeout = 64 cycles | Chapter 4.2 | Hard-coded in `cell_credit` |
| Result batch flush conditions | Chapter 4.3 | `EMIT_BATCH_X`, `CTRL.FLUSH` |
| Strap default = 16 flits | Chapter 4.3 | `TILE_LAND_FLITS` parameter |
| Local-port width stays at delta `DATA_WIDTH` (64 bits today) | Chapter 3, Chapter 4.3 | `DATA_WIDTH` parameter |
| Gatling-programmed drain | Chapter 4.3 | `FLUSH_DEST`, `FLUSH_TAG` registers |

: Table 6.7: MAS decisions and their hardware homes

## RTL Naming Divergence (slice 1)

Slice-1 RTL (`cell_pkg.sv`, `cell_cfg_regs.sv`) predates the 2026-10-18
ruling that renamed result-path grants to straps. The canonical MAS/PRD
terms are **strap counter**, `STRAP_NONZERO`, and `STRAP_STARVED`; the
slice-1 RTL identifiers remain:

- `STATUS_GRANT_NONZERO_BIT` / `status_grant_nonzero` for `STATUS` bit 3
- `IRQ_GRANT_STARVED_BIT` for `IRQ_STATUS`/`IRQ_EN` bit 2

A future RTL pass (slice 2/3) should rename these to the strap terms.
Until then, the register map above states the canonical names and notes
the RTL aliases.

---

**Last Updated:** 2026-10-19
