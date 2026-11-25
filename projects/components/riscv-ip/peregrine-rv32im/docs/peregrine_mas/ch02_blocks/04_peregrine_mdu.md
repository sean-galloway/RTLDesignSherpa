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

# peregrine_mdu

**Module:** `peregrine_mdu.sv`

## Responsibility

One iterative multiply/divide unit, started from EX, for all eight M operations (PRD §4.4, P3, P8). The instruction that starts it holds in EX until `done`; the core owns that hold ("The M Unit and Hold-in-EX").

## Parameters

<!-- GEN:params:peregrine_mdu -->

| Parameter | Kind | Type | Default | Description |
|----------------|----------|------------|--------------|------------------------------|
| `MUL_DSP` | parameter | `bit` | `1'b0` | 0: multiply iteratively, 32 steps; 1: one registered 32x32 product |

: peregrine_mdu parameters

<!-- /GEN -->

## Ports

<!-- GEN:ports:peregrine_mdu -->

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `clk` | input | `1` | Clock |
| `rst_n` | input | `1` | Reset (busy, done, count) |
| `start` | input | `1` | capture: unit idle and an M instruction in EX |
| `cancel` | input | `1` | the M instruction in EX was killed |
| `consume` | input | `1` | EX advanced: the done result was taken |
| `funct3` | input | `[2:0]` | M-extension operation |
| `a` | input | `[31:0]` | rs1 (forwarded) |
| `b` | input | `[31:0]` | rs2 (forwarded) |
| `idle` | output | `1` | Neither busy nor done |
| `done` | output | `1` | Result valid, held until consumed |
| `result` | output | `[31:0]` | Result word, valid under done |

: peregrine_mdu ports

<!-- /GEN -->

## Control: Three Registers, No State Encoding

| Register | Reset | Meaning |
|----------|-------|---------|
| `r_busy` | 0 | Stepping |
| `r_done` | 0 | Result valid, held until `consume` |
| `r_count` | 0 | Step number, 0 to 31 |

: peregrine_mdu control registers

- **Start** (`start` while idle, no `cancel`): capture the operand magnitudes, the result sign and the high/low word select. A divide by zero or the signed overflow -2^31 / -1 writes its specification result directly and goes straight to `done` (the early-out); otherwise `busy`.
- **Busy:** one radix-2 step per cycle; after step 31 (or after one cycle for a `MUL_DSP` multiply) go to `done`.
- **Done:** `result` is valid; cleared when `consume` is high (the core passes `~mem_wait`, so the result survives a hold).
- **Cancel** (a MEM redirect kills the M instruction) wins over everything and returns the unit to idle.

Latency in stall cycles with the M instruction in EX: 33 iterative (start + 32 steps), 1 early-out, 2 for a `MUL_DSP` multiply.

## Datapath

| Operation | `r_opnd` | `r_acc` at start | Step |
|-----------|----------|------------------|------|
| Multiply (iterative) | \|rs1\| | `{32'd0, \|rs2\|}` | Add `r_opnd` to the high word if the low bit is set, shift right: `{hi, multiplier}` |
| Multiply (`MUL_DSP=1`) | \|rs1\| | `{32'd0, \|rs2\|}` | One registered 32x32 product |
| Divide (restoring) | \|rs2\| | `{32'd0, \|rs1\|}` | Shift the next dividend bit into the remainder, subtract the divisor if it fits: `{remainder, quotient}` |

: peregrine_mdu datapath per operation

Operand signedness: `mulh` and `mulhsu` take rs1 signed; `mulh` takes rs2 signed; `div` and `rem` take both signed. `mul` (the low word) is the same for signed and unsigned operands, so it takes the unsigned path and never negates.

**Result.** The word is the high half for `mulh`, `mulhsu`, `mulhu`, `rem`, `remu`, and the low half otherwise. The sign is applied to the registered value: the product and quotient are negative when the operand signs differ, the remainder takes the dividend's sign. Negating a 64-bit product and keeping the high word is `~hi + (lo == 0)`: the low word's +1 carries in only when the low word is zero.

**Payload.** The operation, sign, select, operand and accumulator have no reset and load on every idle cycle, not only on start: the start condition waits for `mem_wait` and is late, while an idle unit's payload is never read (TASK-001 stage 7).

**Formal build.** Under `RISCV_FORMAL_ALTOPS` (defined only by `formal/peregrine/riscv-formal`) `result` is riscv-formal's stand-in, `(rs1 +/- rs2) ^ constant` per operation, latched on the same idle cycles; the control and timing are unchanged.

---

**Last Updated:** 2026-11-25
