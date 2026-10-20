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
chapter names the hooks the design exposes on purpose. The tests live in
`alu-infer/dv/` — `tbclasses/alu_infer_tb.py` holds the testbench (an
`AluInferTB` class on the repo's `TBBase`), and `tests/test_alu_infer.py`
is a thin TEST_TYPE-dispatching runner, the repository standard pattern
(the stream area's). Both valid/ready interfaces are owned by RDS-DV GAXI
BFMs: a `GAXIMaster` drives the issue interface (`valid`/`ready` +
operand/func fields), a `GAXISlave` receives the result interface
(`result_valid`/`result_ready` + line/flags), and passive `GAXIMonitor`s
record completed transfers on both sides. Timing checks anchor on the
BFMs' packet timestamps (the master stamps the accepting edge, the slave
the retiring cycle), and the mixed soak additionally runs under the
standard randomized GAXI delay profiles (`GAXI_TIMING_PROFILE`, from the
shared `GAXI_RANDOMIZER_CONFIGS` table in
`bin/TBClasses/amba/amba_random_configs.py`): func sweeps `fast`,
`slow_producer`, `slow_consumer`, `gaxi_realistic`, `gaxi_backpressure`;
full adds `constrained`, `burst_pause`, `high_throughput`, `gaxi_stress`
(the per-type default is `backtoback`). The scenario-to-coverage map
lives in `dv/testplans/alu_infer_top_testplan.yaml` — its `covers_lines`
are generated from the per-scenario merged coverage data, and
`bin/cov_utils/verify_testplan_coverage.py --strict` re-checks every
scenario against a fresh `COVERAGE=1` run. The cell PRD's
credit-loop tests already prove lines-in → credits-out independently of
the datapath, so these hooks assume a datapath-only test space.

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

## Elastic and Tag-Join Behavior

The alignment mechanism has its own directed tests — the as-built
TEST_TYPEs `copy_timing`, `backpressure`, and `tag_join`: natural per-row
latency (combinational rows offered the cycle after issue, add/sub
`ADDER_LATENCY` cycles after, measured from BFM packet timestamps),
II=1 streaming proven from consecutive retirement deltas under
`send_burst`, the elastic hold-and-resume (the slave's
`set_ready_policy('stall'/'always')` drives the consumer side), the
tag-FIFO fill (`ready` falls only at `PIPE_DEPTH` in flight, never
earlier), and the join itself — an add issued ahead of a relu and a
copy must present first, with the fast rows waiting at the FIFO head.
These are the tests that pin the owner ruling of 2026-10-18.

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

**Last Updated:** 2026-10-20
