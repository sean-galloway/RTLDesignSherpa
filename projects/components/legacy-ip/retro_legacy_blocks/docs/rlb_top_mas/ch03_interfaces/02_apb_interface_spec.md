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

# RLB Top - APB4 Protocol at the Subsystem Boundary

## Overview

This page is the protocol contract on the single APB slave port `s_apb_*`
— the boundary a SoC fabric must honour to talk to the subsystem. The
signal list and the address decode table live in
[Top-Level Interface](01_top_level.md); this page owns the *rules*:
phases, wait states, strobes, protection attributes, and the two ways a
transaction can complete with an error.

The boundary is the master side of the generated crossbar
([Chapter 2.1](../ch02_blocks/01_apbx_xbar.md)). Everything below is a
property of that generated fabric plus the blocks behind it, not of any
hand-written glue in `rlb_top`.

## Protocol Feature Support

| Feature | Support |
| --- | --- |
| `PSEL` / `PENABLE` / `PWRITE` | Yes — standard two-phase APB |
| `PADDR` | 32-bit, **full system address** (not a window offset) |
| `PWDATA` / `PRDATA` | 32-bit |
| `PREADY` | Yes — wait states come from the addressed block (see below) |
| `PSLVERR` | Yes — two error sources (see below) |
| `PSTRB` | Yes — carried through to the selected block |
| `PPROT` | Yes — carried through to the selected block; checking is a per-block decision |

The interface is APB4. A master that speaks only APB3 can still use it:
tie `PSTRB` to all-ones on writes and all-zero on reads (the APB4 rule —
`PSTRB` must be zero during a read), and tie `PPROT` to zero.

## Transfer Phases

A transaction is the standard APB pair:

1. **Setup.** The master asserts `PSEL`, presents the full system address
   on `PADDR`, the direction on `PWRITE`, and (for writes) `PWDATA`,
   `PSTRB`, `PPROT`.
2. **Access.** The master asserts `PENABLE`. The transfer completes on
   the rising edge where the slave's `PREADY` is high; read data is
   sampled on `PRDATA` in the same cycle.

The minimum transaction length is therefore two `pclk` cycles. There is
no back-to-back packing and no burst concept — APB4 is single-transfer,
and the crossbar does not add one.

## Wait States

`PREADY` returned to the master is the selected block's own `PREADY`.
The fabric between the boundary and the block is combinational: it adds
no wait states of its own, so the wait-state profile of a transaction is
entirely the addressed block's, as documented in that block's book.
Software that polls a slow register (a UART line-status register after
a transmit, for example) sees that block's documented latency, unchanged
by the subsystem layer.

A consequence worth knowing for debug: while `PREADY` is low, the
address and control must be held stable per the APB spec — the crossbar
holds the *decode* stable with them, so a stalled transaction cannot
migrate to a different window mid-wait.

## Write Strobes and Protection

`PSTRB` and `PPROT` are forwarded to the selected block on every
transaction. What the block does with them is the block's own
documented behaviour:

- `PSTRB` — byte lane enables for writes. Blocks that implement
  byte-granular register writes honour it; blocks with word-only
  registers document that in their own book. Masters should not assume
  more than the target block promises.
- `PPROT` — protection attributes. The RLB blocks accept and ignore it
  (no protection checking at this level), as each per-block book states.
  It exists on the boundary because APB4 requires the signals to be
  carried; a system-level protection scheme would be enforced above
  `rlb_top`.

## Error Responses

A transaction completes with `PSLVERR` asserted for exactly two reasons:

1. **Decode miss.** The address matches no window. The generated
   crossbar's decode-miss path completes the transaction with `PSLVERR`
   rather than holding `PREADY` low — an unmapped access can never hang
   the bus. Read data on a miss is undefined; software must treat the
   transaction as failed. This path is a property of the generator and
   is the reason the crossbar is regenerated rather than hand-edited.
2. **Block error.** The addressed block asserts its own `PSLVERR` (for
   example, an access to a register offset that block does not
   implement). The block's book owns the specifics; the boundary simply
   returns whatever the block raises.

The two are distinguishable in hardware only by address: if the address
is inside a decoded window, the error came from the block; if it is
outside all ten windows, it came from the decode miss. The `func` suite
proves the decode-miss case completes instead of hanging.

## Rules an Integrator Must Honour

- Drive the **full system address**; the subsystem decodes
  `PADDR[15:12]` against `BASE_ADDR` internally and blocks see only
  `PADDR[11:0]`.
- Never issue a new transaction to a different window while `PREADY` is
  low on the current one — standard APB, restated here because the
  crossbar's decode follows the held address.
- Tie `PSTRB`/`PPROT` per the APB4 rules if your master does not drive
  them.
- Expect errors to be *fast*, never *absent*: both failure modes complete
  with `PSLVERR` in bounded time.

## Related Documents

- [Top-Level Interface](01_top_level.md) - the port list and the decode table this protocol serves
- [The APB Crossbar Block](../ch02_blocks/01_apbx_xbar.md) - the generated fabric that implements this boundary
- [Window Map](../ch05_registers/01_register_map.md) - the ten windows the decode resolves to
