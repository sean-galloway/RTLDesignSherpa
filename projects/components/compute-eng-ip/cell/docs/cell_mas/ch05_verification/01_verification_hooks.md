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

# Verification Plan

## House Test Grid

The cell testbench follows the house gate / func / full grid:

| Level | Scope | Typical seeds | Runtime target |
|---|---|---|---|
| gate | Smoke: elaboration, reset, register reset values, basic fill | 1 seed | < 1 min |
| func | Directed feature tests across seeds | 8 seeds | ~5 min |
| full | Longer randomized runs, corner cases, coverage closure | 32+ seeds | ~30 min |

: Table 5.1: House test grid

## Existing Tests

`cell/dv/tests/test_cell.py` already covers slice-1 behavior:

1. Elaboration + reset + register reset values over AXIL
2. AXIL and cfg-stream register access
3. Input-memory fill from a `ptype=mem` packet
4. Bad-packet drop behavior

The delta node inside `cell_top` is treated as a black box; slice-1
simulation drives the local rx port through the `test_mode` injection
hook (`dut.test_rx_*`) so the testbench can supply cell traffic without
fighting the node's continuous driver.

## Planned Slice-2 Credit-Loop Test

The slice-2 test verifies the credit return path independently of the
datapath:

1. Drive `mem` packets into the cell from multiple recorded sources
   (using the test-mode injection hook or a BFM on the local port).
2. Force the execution FSM to consume lines without running the ALU
   (or run a passthrough opcode).
3. Check that `cell_credit` emits `credit`/`add` packets whose
   destination equals the recorded source coordinate and whose length
   matches the configured batching (`CREDIT_BATCH_N` or residual).
4. Verify the 64-cycle partial-batch timeout by sending a partial
   batch and waiting for the automatic drain.
5. Verify the boot `credit`/`set` advertisement to `level=3` carrying
   `IN_DEPTH` flits.

The test forces straps so that result emission does not gate credit
returns.

## Planned Slice-3 ALU-Run Test

The slice-3 test verifies the pop→issue→push loop end to end:

1. Program `FUNC_SEL`, `OP_SRC`, `OP_LINES`, and persistent operands
   `A`–`D`, `T` via `cfg` or AXIL.
2. Fill the input memory with known operand lines.
3. Enable the FSM and run until `STATUS.busy` clears or an IRQ fires.
4. Read the result memory (via the packetizer drain or AXIL window).
5. Check results against the alu-infer golden model per opcode.

Coverage: opcode (8) × special-value classes × lane position ×
accumulator clear/hold/drain corners.

## Verification Hooks

| Hook | Use |
|---|---|
| `test_rx_*` / `test_mode` | Inject cell traffic without instantiating the delta mesh |
| `inc_lines_in/out`, `inc_credits`, `inc_pkts` | Count events independently of datapath |
| `o_todo_credit_drop_cnt` / `o_todo_cfg_read_drop_cnt` | Confirm slice-1 stubs are replaced in slice 2 |
| `STATUS` / `IRQ_STATUS` | Observe empty/full, error, and strap-starved states |

: Table 5.2: Verification hooks

## Assertions and Checks

- Credit return must match lines consumed, per source, within the batch
  timeout.
- Strap counter must never go negative; packetizer `tvalid` implies
  sufficient strap for the whole packet.
- ALU results retire in issue order.
- `IP` and `OP` wrap correctly at their respective depths.

---

**Last Updated:** 2026-10-19
