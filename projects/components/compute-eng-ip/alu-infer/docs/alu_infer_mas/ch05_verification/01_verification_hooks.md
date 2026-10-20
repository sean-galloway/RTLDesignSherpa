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

# Verification Hooks and Observability

The ALU's verifiability is a consequence of its structure, and this
chapter names the hooks the design exposes on purpose. The tests live
in the cell's `dv/` tree (the RTL does), on the repo's cocotb + rds-dv
BFM stack; the cell PRD's credit-loop tests already prove lines-in →
credits-out independently of the datapath, so these hooks assume a
datapath-only test space.

## The Golden Model

One scalar bf16 numerics model, applied per lane: compute the expected
result in fp32, round to bf16 RNE. This is the same discipline the math
library's own dv uses, which means the ALU's golden model and the
library's golden model are the same arithmetic — and lane independence
(PRD §4 invariant 1) makes a per-lane scalar comparison a *strong*
check, not a sampling one. For mac, the golden model keeps a fp32
accumulator per lane and only rounds at presentation, matching decision
M7.

## Built-in Cross-check

Every row instantiates an `rtl/math` block with its own passing dv. The
unit testbench therefore double-checks for free: drive the same
operands to the ALU and to the library block directly (or to its
reference model); any divergence is a bug in exactly one of them. This
is the strongest hook in the design — it turns "the ALU works" into
"the ALU is wired the way the library block expects," which is where
integration bugs actually live.

## Coverage Matrix

| Axis | Values |
|------|--------|
| Opcode | 0–7 (all v1 rows) |
| Special-value class | NaN payload, +inf, −inf, +0, −0, normal, denormal/FTZ (per block `SUBNORMAL_SUPPORT`, M3) |
| Lane position | 0 and 1 (both populated, either populated) |
| Accumulator | long chains (>100 ACC steps), CLEAR/ACC/DRAIN corners, clear-then-accumulate, drain-without-accumulate |

: Table 5.1: unit coverage matrix

Special values are mandatory corners, not extras — the bf16_testing
base classes (`bf16_special_value_product`, per the math area's
TASK-006 grid discipline) generate the Cartesian product; the matrix
above says where it must be applied.

## Observability

- **No internal monitor taps by default.** Observability is the Ocelus
  MonBus plane's job at tile scope; the ALU contributes nothing to it.
- **The accumulator bank is read-back-able** through normal mac DRAIN
  invocations, so no debug port is needed for the state that matters.
- **Open item M2** (flag observability) is the one place this chapter
  deliberately leaves a hook decision open: whether the library blocks'
  IEEE exception outputs forward into `result_flags`, and if so in what
  layout alongside the mask bits (the mask format itself is closed —
  one bit per lane, packed low; M5).

## Test Levels

House gate/func/full grid, per the cell PRD §9: gate smoke on copy +
add; func per-row truth tables against the golden model; full as the
coverage matrix above plus the cell's integration tests (in-band `cfg`
programming, credit loop, packetizer) that consume this block.

---

**Last Updated:** 2026-10-17
