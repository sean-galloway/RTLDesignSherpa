# TASK-022: the byte-granular RAPIDS has no formal proofs of its own

**Priority:** P2 -- the product tree is unproven while the stepping stone is
proven. Not urgent (the byte tree is board-characterized and its suites are
green), but it is the largest coverage gap the rapids TASK-019 closure exposed.
**Status:** ACTIVE 2026-10-02. Scope DECIDED 2026-10-02 -- see "Decide first".
**Owner:** TBD

## The gap

`formal/rapids/` holds 11 proof directories. **Nine are `*_beats`**; the only
un-suffixed ones are `ctrlrd_engine` and `ctrlwr_engine`, which both trees
share. So every proof that is specific to a design proves the beat-granular
stepping stone -- the tree rapids TASK-019 explicitly described as "kept
runnable and green, not maintained forward".

Nothing proves `scheduler.sv`, `axi_read_engine.sv`, `axi_write_engine.sv`,
`snk_data_path_axis.sv`, `src_data_path_axis.sv`, `alloc_ctrl`, `drain_ctrl`,
`descriptor_engine` or the byte SRAM controllers.

**Census of all 23 byte modules against `formal/rapids` (measured by the
RLB-cleanup session, 2026-10-01), which widens this gap beyond how it was
first filed:**

| Group | Count |
|---|---:|
| proven, and only because `ctrlrd`/`ctrlwr` are shared | 2 |
| the `_beats` twin is proven, the byte one is not | 9 |
| **UNPROVEN IN BOTH TREES** | **12** |

The twelve are `scheduler_group`, `scheduler_group_array`, `rapids_core`,
`rapids_snk`, `rapids_src`, `snk`/`src_data_path`, `snk`/`src_data_path_axis`,
the two `_axis_test` wrappers, and `monbus_axil_group_2in` (no beats twin at
all; shared, like ctrlrd/ctrlwr). **The macro level has never been proven in
either granularity.** So the beats suite covers 9 of the 21 non-shared modules,
and this is not "the byte tree is unproven while the stepping stone is proven"
-- more than half the tree is unproven at any granularity. That also settles
"Decide first" on arithmetic: porting the nine cannot reach even half the gap,
and the twelve have nothing to port from.

Also missing from the original list: the byte `latency_bridge` (`rtl/fub/`) is
unproven while `latency_bridge_beats` has a proof. Deprioritise it, though --
NEITHER latency_bridge is instantiated in any design. `latency_bridge` appears
only in `dv/tb/latency_bridge_tb_top.sv` and `latency_bridge_beats` only in its
own TB plus its formal wrapper; the beats top closure is 69 sources with no
latency_bridge in it, and STREAM has its own `stream_latency_bridge`.

## Why it matters more than a straight port would suggest

The byte tree is not the beats tree with wider counters. It added logic that
has no beats equivalent, and it is exactly the kind of logic formal is good at:

- the ingress barrel shifter and its spill/hold across memory beats, plus the
  mirror shifter on egress -- a byte-placement invariant, and the kind of thing
  a directed test samples rather than proves;
- the packet-record queue and its ready contract (`s_axis_tready` held low
  until a channel's record exists), which is a liveness property;
- WSTRB generation from offset and remaining length, and the first/last-beat
  masking -- a sizing invariant over the 4 KB boundary split;
- per-channel reset reaching every latching stage (the rapids TASK-019
  channel-reset work), where "a channel recovers without aresetn" is a property,
  not a test case.

## Decide first

- [x] scope: DECIDED 2026-10-02 (Sean) -- the smaller set aimed at the
      byte-specific logic above, not a port of the nine. The arithmetic in
      the census settles it: porting cannot reach half the gap, and the
      twelve have nothing to port from.
- [ ] does the beats formal suite stay once the byte proofs exist? DEFERRED
      2026-10-02 -- decide when the byte proofs exist; the answer should
      match how long the beats tree itself stays.
- [x] proof mechanism: DECIDED 2026-10-02 (Sean) -- PORT-LEVEL HARNESS ONLY.
      No new in-RTL properties of any kind; internal invariants are restated
      at module boundaries or the signal is exposed. This matches the only
      mechanism that has ever worked in this tree (see the finding below).
- [x] the 64 existing in-RTL concurrent assertions: DECIDED 2026-10-02 (Sean)
      -- DELETE all 64 (32 per tree, 14 files). Dead text whose maintenance
      cost was already paid (the arbiter-request comment); nothing compiles
      them and nothing may start to.

## Notes

- Flat-file discipline applies from day one: a committed sv2v snapshot that is
  not regenerated leaves a proof green against RTL that no longer exists. That
  has already happened in this area -- rapids BUG-011.
- `vault/handbook` has the formal method (sv2v flatten, in-RTL ifdef FORMAL
  properties, mutation-checking every new assertion, harness vacuity traps);
  this task does not restate it.

## Finding 2026-10-01: the 64 in-RTL properties have never been compiled

Measured by the RLB-cleanup session while scoping this task, in both trees;
the three structural checks independently reproduced here.

**`ctrlrd_engine` is the whole finding in one line:** it has a PASSING formal
proof, its source carries 8 `assert property` statements, and its flat contains
**zero**. Its Makefile passes no `--define=FORMAL`, so the `ifdef FORMAL` block
is never compiled. The proof is its harness's properties and nothing else.

That generalises:

- **64 concurrent `assert property` statements across 14 files**, 32 per tree,
  symmetric. fub/: axi_read_engine 4, axi_write_engine 5, ctrlrd_engine 8,
  ctrlwr_engine 8, descriptor_engine 6, scheduler 3; macro/: scheduler_group 4,
  scheduler_group_array 2 -- and the identical counts in every `_beats` twin.
- **0 of 11 rapids proof Makefiles pass `--define=FORMAL`.** Not one outlier --
  none of them.
- **No committed `*_flat.v` anywhere under `formal/` contains `assert
  property`.** Repo-wide the figure is 103 across 27 files; rapids is 64 of them.

### It is not a forgotten flag

Both sv2v settings were tried and neither carries these properties:

- **WITH `--exclude=Assert`**: sv2v passes the SVA through verbatim and yosys
  rejects it -- `syntax error, unexpected '@'` at the first assertion. Adding
  `-sv` to `read_verilog` does not help; `disable iff` and `|->` are beyond the
  frontend.
- **WITHOUT it**: sv2v deletes them silently. The flat goes from 4 assertions to
  0, and the proof then passes while checking nothing.

The second is the dangerous half, because it looks like success.

**Immediate vs concurrent is the dividing line** (verified here): 22 committed
`*_flat.v` files DO contain an immediate `assert(...)`, and 0 contain `assert
property`. So immediate assertions survive sv2v into the flats and concurrent
SVA does not -- which is why a rule that says "in-RTL properties are compiled
and checked" is half true and misleading.

### The cost is real and already paid

`axi_read_engine`'s block carries a comment explaining that the arbiter now sees
`r_arb_request` rather than the live `w_arb_request` "after the request pipeline
added for 8-channel 100 MHz timing closure". Someone reasoned about a property's
correctness through a timing change that could never have been checked. That is
maintenance spent with no coverage returned.

### Consequence for this task's scope

The byte-specific invariants this task exists for -- the ingress barrel shifter's
hold/spill, the packet-record ready contract, WSTRB generation across the 4 KB
split -- are all internal, and the only mechanism that has ever worked in this
tree is the port-level `formal_<block>.sv` harness. So an internal property needs
either the signal exposed on the boundary or the property restated at it. That
constraint should be settled before any proof is written, not discovered during.

It is also the route Sean's 2026-09-03 decision requires. **Two questions are
with Sean:** whether NEW internal properties are permitted at all, and what
becomes of the 64 existing ones -- delete, convert to harness properties, or keep
as documentation. The second is new information for that decision: in this tree
RTL assertions break no tool, because nothing compiles them.

### Method note

Count `assert property` with comment lines excluded --
`grep -E "assert property" FILE | grep -vE "^\s*(//|\*|/\*)"` -- and require the
file to contain an `ifdef FORMAL` block. A plain grep counts prose: `drain_ctrl`
and `drain_ctrl_beats` each contain the string once, inside a comment saying the
author deliberately used a procedural check instead. (This caught me: I "corrected"
64 to 66 off an unfiltered grep, and the two extra hits were that comment.)

Handbook: `vault/handbook/dv/formal.md` (985bc3b4b) now carries the general rule.
