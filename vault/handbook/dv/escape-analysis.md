---
title: Escape analysis
summary: The RTL defects that got past a green test suite, and the specific test-gap that let each one through.
---

# Escape analysis

Every bug below existed in `rtl/` while its own test suite was green. The point
of this note is not the bugs - they are fixed - it is the **shape of the gap**
that let each one through, because those shapes recur.

All of these were surfaced by *documentation* review ([[kimi-review-rounds]]),
not by testing. That is itself the headline: a reviewer forced to reconcile the
doc against the RTL line by line found what the testbench could not.

## The defects, and what let each one through

### 1. `arbiter_round_robin_simple` - rotated the wrong way, starved half its clients

Rotating the request vector LEFT by `last+1` maps rotated bit j to agent
`(j - s) mod N`. That is a **reflection**, not a rotation - and a reflection
composed with itself is the identity, so the pointer oscillated between two
positions. N=4, all four requesting: grants went `0,3,0,3,...` forever. Two of
four agents were never served. Measured before/after under Verilator:
`10/0/0/10` -> `5/5/5/5`.

**Four independent escapes, any one of which would have caught it:**

- **The threshold was set so loose it passed the bug.** `min_fairness_threshold
  = 0.3` on a 4-client arbiter. Jain's index for k of n clients served equally
  is k/n, so 0.3 passes with **two clients completely starved** (index 0.5).
  The test printed `fairness: 0.500` and PASSED. A threshold that cannot fail
  the defect it names is decoration.
- **The stimulus never reached the stressing corner.** No `ArbiterMaster`
  profile asserts all clients continuously - even `fast` leaves a 1-3 cycle
  gap. The arbiter was therefore never forced to walk its rotation, and the
  *request pattern* decided who got served rather than the arbiter. See
  [[randomization]]: randomized traffic does not prove fairness.
- **The checker whose name promised this exact catch is a stub.**
  `ArbiterCompliance.analyze_round_robin_compliance()` returns a hardcoded
  `rr_efficiency: 1.0` regardless of the observed grant sequence. A clean report
  from it is not evidence of anything.
- **No downstream pressure.** The module has zero instantiators in the repo, so
  no integration test would trip over it. It is a library module someone could
  have picked up - which is exactly how it survived.

### 2. `clock_pulse.sv` - counter as wide as the period

`r_counter` was declared `[WIDTH-1:0]`, but WIDTH is the pulse PERIOD. The
doc's own 1 Hz heartbeat example (`WIDTH=100_000_000`) would infer ~100 million
flip-flops and not synthesize.

**Escape:** *functionally correct in simulation.* An over-wide counter counts
perfectly well. Only synthesis or an area/resource check catches this class, and
the flow gates on behaviour, not on inferred resources. Nothing in the test path
has an opinion about flop count.

### 3. `clock_gate_ctrl.sv` - port list forward-references a body localparam

The ANSI port list used `[N-1:0]` where `N` is a localparam declared *after* the
port list. Strict-LRM tools reject it.

**Escape:** *one simulator's tolerance became the spec.* Verilator accepted it,
and Verilator is what the repo runs. Nothing checks LRM strictness, so
"compiles here" silently stood in for "is legal SystemVerilog".

### 4. `pwm.sv` - emitted N+1 periods for `repeat_count = N`

`w_all_repeats_done` compared `r_repeat_value` against `local_repeat` while that
register increments on the same period-boundary cycle. `repeat=1` ("single
pulse") produced two.

**Escape:** recorded plainly at fix time - *the test waits for `done` but never
counts periods.* It asserted that the thing **finished**, not that it did the
**right amount**. This is the most repeatable gap on the list.

### 5. Four RTL header comments that described a different module

- `sort.sv` claimed ascending / smallest at LSB; the compare-swap sorts
  DESCENDING with the largest at the LSB.
- `sync_pulse.sv` advertised a toggle-synchronized-back-to-source ready path
  with **no port and no logic**, plus two inconsistent min-spacing figures.
- `fifo_sync.sv` / `fifo_async.sv` advertised sim-only overflow/underflow
  `$display` checks the bodies never contained.

**Escape:** *comments do not execute.* Nothing in any flow reads them, so they
drift from the code the moment either changes, and only a human (or a reviewer
model) reading RTL and doc side by side will notice.

### 6. `gaxi_drop_fifo_sync` - mux mode never presented the head entry

The read address was the NEXT pointer in mux mode:

```systemverilog
assign r_rd_addr = (REGISTERED == 0) ? w_rd_ptr_selected[AW-1:0] : r_rd_ptr_bin[AW-1:0];
```

`counter_bin_load` drives `counter_bin_next = curr + 1` whenever its enable
(`w_read = rd_valid && rd_ready`) is high, so asserting `rd_ready`
combinationally re-pointed the memory at the entry AFTER the one being
accepted. The head was never presented during its own handshake, and `rd_data`
moved while the consumer was sampling it. Written `A1 B2 C3 D4`, a consumer
holding `rd_ready` read back `C3 D4 00`. `gaxi_fifo_sync` has always used the
current pointer unconditionally; the drop FIFO was the outlier. Every RTL
instantiation in the repo uses `REGISTERED(0)`, so the broken mode was the only
one anything ships.

**Escape: the testbench returned its own model as the DUT's answer.**
`read_entry()` ended with

```python
rd_data = self.fifo_model.pop(0)  # This is what was read
...
return True, rd_data
```

so the caller's `assert data == expected` compared the stimulus list against
itself. It could not fail. `dut.rd_data` was never read anywhere in the
testbench; the read monitor's packet was popped and discarded as mere evidence
that *a* read had happened. Five cocotb tests, both modes, GATE through FULL,
green throughout - against a FIFO that was handing back the wrong entry.

This is the [[arbiter-compliance-model]] failure one layer down. There, a model
nobody read its verdict from was wrong indefinitely. Here, a model that WAS
read had been substituted for the DUT, so reading it proved nothing. **Ask of
any data check: which side of the comparison came off a pin?**

The count-only checks (`drop_by_count`, `drop_all`) stayed green under the
mutation too - they assert on occupancy and never look at data, so a FIFO can
lose, duplicate, or fabricate every entry and still satisfy them.

## The recurring shapes

Worth checking any new test against directly:

| Shape | Ask |
|---|---|
| Asserts completion, not quantity | Does it count, or just wait for `done`? |
| Threshold looser than the defect | Can this threshold fail the bug it names? Compute the metric for the broken case. |
| Stimulus never reaches the corner | Does any profile actually saturate / back-pressure / fill? |
| The checker is a stub | Has anyone read the checker's body, or just its name? |
| Both sides are the model | Which side of this comparison came off a DUT pin? |
| Counts checked, data not | Would this notice if every payload were wrong? |
| Simulation-only signoff | What classes (area, LRM strictness, CDC) does simulation structurally not see? |
| No instantiators | Who would notice if this library module were wrong? |
| Comments | Nothing executes them. |
| The monitor "misbehaves" | When a protocol monitor never closes a packet, first ask whether the DUT ever produced the closing condition. smbus #58: the wire monitor returned stale packets and the tests read `wire data=[]`; the cause was the PHY releasing SDA and SCL on the same edge, so no STOP condition ever existed on the bus. An hour went into the monitor before a reviewer's bit-level slave counted zero STOPs. |
| The helper consumed the evidence | A polling helper that reads a read-clear register clears the very flags the test is about. uart_16550 #60: `is_rx_data_ready()` reads LSR, whose error bits clear on read per the datasheet, so `wait_for_rx_data()` ate FE/BI/PE/OE before the assertion could see them and three tests were unsatisfiable by any correct RTL. Ask what each poll costs, and capture status from the value the poll already returned. |
| Tests pass on a register, not the wire | `SMBUS_PEC` read back right while the STOP was missing; a register-level pass says nothing about the bus. Every transaction-type test asserts the wire conditions (START, Sr, ACK/NAK per byte, STOP) from a monitor, not only the status bits. |
| The parameter's OFF state is never asserted | A feature parameter defaulting to 0 gets tested ON and assumed OFF. But OFF is a claim too -- "these bits read zero whatever the input was" -- and it holds vacuously if the test never drives the input. Drive the feature's stimulus in BOTH builds and assert the tie-off; then mutate the RTL to ignore the parameter. wb4 `USE_BURST_HINTS` (TASK-088): that mutation is the only one the hints-OFF configurations catch, and without it a default of 0 that silently leaked the hint would have shipped green. |
| The test passes on its own precondition failing | A guard that returns PASS when the thing the test needs is unavailable converts an infrastructure breakage into a green run. RLB-006 found `test_gh58_r4_10_tx_fifo_pstrb` importing the framework's `APBPacket` behind a `try/except ImportError` that returned `True`: a rename in the framework would have turned the test green while it drove nothing. A missing precondition is a FAILURE, or a skip loud enough to be counted -- never a pass. Ask of every early `return True`: what state of the world does this reward? |
| A checker with false positives is a checker nobody reads | Not a test shape but the one above it. The RLB-006 input-driven sweep first reported `hpet_clk` and `rtc_clk` as undriven because it recognised `.value =` but not `Clock(self.dut.x)`. Two false positives out of nine blocks is enough for a reader to dismiss the other seven results. Fix the checker before believing its output -- `check_test_levels.py`'s own header records three regex generations that each cried wolf differently. |
| An undriven input is a configuration | Under Verilator an input the test never assigns reads 0, not X, so it silently selects a mode. pumice's `test_pumice_dfi_layer` left `gear_i` undriven, so a two-phase build ran at gear 0 with half its DFI enables masked. A model that only asked "is any enable set?" passed, and the requirements doc cited that test as the gear=MAX evidence. Diff the DUT's inputs against what the test assigns, then make the check reject the wrong mode: a gear-0 mutant must go red. |
| The report adds a constant nobody recomputes | A summary line that prints `measured + <literal>` is a hand-sum, and it rots the first time a loop count changes. All four apbx-xbar crossbar tests did it: 1to1 reported `+60` where its loops ran 82 fixed transactions, 2to1 `+70` against 144, 1to4 `+160` against 296, 2to4 `+250` against 364 -- every one already wrong, and all four would have gone further wrong the moment the counts became level-scaled. Derive the number from the same knobs that drive the loops, or do not print it. |
| A new port escapes the area you are testing | Adding a required port breaks every instantiation that does not connect it -- and under the flags cocotb passes, PINMISSING is an ERROR, so it fails the BUILD, not the test: the test never runs and reports nothing. STREAM hit this in 2026-07 (`descriptor_ext_packet` -> `datapath_rd_test`/`datapath_wr_test`); rapids hit the identical thing in 2026-09 (`scheduler_beats` -> `src`/`snk_data_path_axis_test_beats`), and a green top_beats gate said nothing because those consumers live in macro_beats. Sweep EVERY instantiation repo-wide, not just the area under test and not just DV wrappers -- RTL test-path modules instantiate DUTs too. Tie an unused INPUT to a value, not `.port()`, which leaves it undriven. The pre-commit port-consumer check is what catches this; do not reach for `--no-verify` when it fires. |
| The count check only bounds one side | `len(got) < expected` catches SHORT delivery and is structurally blind to OVER-delivery. rapids' kick refactor: a doubled launch moved 8 beats for a 4-beat descriptor, `8 < 4` is false, and the payload comparison ran on `got[:4]`, which a re-run of the same descriptor reproduces byte-for-byte -- so the test passed. Worse, it silently invalidated a MUTATION PROOF: removing the load-bearing rising-edge detect came back green, and the RTL was only cleared once the checker settled to idle and demanded an EXACT count (then the mutant went red at 8/4). Before trusting any mutation's verdict, confirm the observer can see the failure you are mutating in -- a green mutation against a one-sided checker is not evidence of anything. |
| The BFM's answer is a constant | A sibling of "the checker is a stub", on the model side. The AXI5 slave BFM answered `BTAGMATCH = 1` for ANY non-zero tag operation and stored no tag at all, so a fabric test asserting "tagged write reports a match" would have passed with every tag zeroed in transit. Before asserting on a value the model produces, read how the model produces it; if it cannot say no, the assertion cannot fail. BRIDGE-018 gave the slave BFMs a real tag store, a Match that compares, and a Transfer read that returns what was stored -- then the test could write cpu tags 0..7 and dma tags 8..15 through two masters at once and read the store back per 16-byte granule. |
| The model skips what it cannot handle | A TB that models a consumer and gates on `if beats > 0:` cannot detect a ZERO-beat request -- and the illegal case is exactly the one the real engine turns into a defect, sizing its burst as (beats - 1) and underflowing to AxLEN=0xFF. rapids EXT: a 16-case fub matrix stayed green over a run-boundary defect that the top-level test caught under only one seed in three. An out-of-contract input must be RECORDED, never skipped. |
| A comment outliving its guard | Sharper than "Comments: nothing executes them". rapids' write side carried STREAM's note about the awlen=0xFF transfer-size underflow while the port had dropped the `!w_wr_need_base` term that prevented it, so the file documented a hazard it no longer defended against -- and the surviving comment read as evidence the guard was there. When porting a feature between sibling modules, diff the source module's EXPRESSION term by term, not the feature. |

## What is still unexamined

The common area is integrated. Across the un-integrated units there remain
**38 CONFIRMED findings that cite `rtl/*.sv`** and are therefore candidate RTL
defects, not doc drift:

| Unit | CONFIRMED citing RTL |
|---|---|
| shared_part_02 | 7 |
| monitor_part_01 (round_3) | 8 |
| apb | 6 |
| math_part_01/02/03 | 4 / 5 / 4 |
| axi4_part_01/02 | 4 / 2 |
| cdc_part_01 | 3 |
| axis4 | 1 |

Tracked as DOCREV-001. Triage doc-fix vs RTL-fix per finding - the headline
lies in both directions.

Related: [[kimi-review-rounds]], [[randomization]], [[running-regressions]],
[[coverage]].
