---
title: BFM usage
summary: Use RDS-DV framework BFMs; never hand-roll. Map + trap list.
---

# Use the framework BFMs - never re-roll

The CocoTBFramework (RTLDesignSherpa-DV repo, editable-installed) plus the
bin/TBClasses wrappers cover every protocol here. Hand-rolled drivers miss
timing corners; hand-rolled decoders desync from packet formats. Missing
BFM = add it to RDS-DV, never inline.

| Interface | Use |
|---|---|
| custom valid/ready | GAXIMaster/GAXISlave (components.gaxi) |
| AXI4 | axi4 factories + AXI4Sequence (never hand-poke s_axi_*) |
| AXI4-Lite / APB / AXIS | axil4 / apb / axis4+axis5 factories |
| Wishbone B4 (pipelined) | wb4 factories (components.wb4): WB4Master / WB4Slave / WB4Monitor; STALL, CYC and in-order termination are why it is not a GAXI composition |
| MonBus receive | TBClasses.monbus.MonbusSlave |
| MonBus decode | TBClasses.monbus.parse() ONLY |
| MonBus groups | MonbusGroupHarness (scoreboards.monbus_group) |
| MonBus drive WITH timestamp | The family group TBs drive `monbus_packet` through a GAXI master and only sniff `monbus_timestamp`, so no group test checked that the source timestamp lands. To drive both on one handshake, give the GAXI master a two-field `FieldConfig` (`packet` 128, `timestamp` 64) with `multi_sig=True` and a `signal_map` naming both pins; the 1wr bench (`bin/TBClasses/amba/monbus_group_1wr/`) does this and checks the timestamp beat through `parse_stream()` (2026-10-23) |
| MonBus groups, beat addresses | `trace_beats` stamps EVERY W beat with its burst's AW address; per-beat addresses come from `trace_bursts` (`addr + 8*i`, in B order). A check written against `trace_beats` passes at `MAX_BURST_BEATS=1` and fails on the first real burst (monbus_group_core_1wr test, 2026-10-23) |
| Registers | [[registers-by-name]] |

| Arbiters | ArbiterMaster + RoundRobinArbiterMonitor (components.shared) |

Decision line: standard protocol -> factory; custom valid/ready -> GAXI;
<50-line test-local helper may stay embedded; anything reusable -> RDS-DV.

Factory entry points, per family (count = callables in that file):
`gaxi_factories` 8, `axi4_factories` 17, `axil4_factories` 18,
`apb_factories` 7, `axis_factories` 11, `fifo_factories` 14, `wb4_factories` 3. DFI, UART and
SMBus have no factory module - construct their components directly
(`dfi_master_mc.py`, `uart_components.py`, `smbus_components.py`).

This note covers the BFM axis ONLY. What traffic to send (sequences) and what
timing shape to send it at (randomization) are INDEPENDENT choices - see
[[rds-dv-axes]] for the three-axis framing, and [[randomization]] for the
profile catalogue. Using the right BFM says nothing about whether the test
stresses anything.

Authoritative per-family API docs live in RDS-DV itself
(`docs/components/<family>/`, published at
sean-galloway.github.io/RTLDesignSherpa-DV) - read those rather than
reverse-engineering from source.

Traps (each cost real debug time):
- cocotb Monitor.__len__ = queue depth: empty-queue BFM is FALSY, so
  `x.get_stats() if x else {}` silently returns {}. Use `is not None`.
- signal_map requires ALL of {valid, ready, data}.
- Default ready profile delays reach 30 cycles; drain/quiet windows must
  exceed max-delay+refill (~40) AND check bus idle ([[seeds-and-determinism]]
  has the companion rule).
- Don't spawn private _monitor_recv on self-registering components.
- TB classes live in the PROJECT area (projects/**/dv/tbclasses), never in
  the shared framework.

## `MemoryModel` addresses BYTES; `bytes_per_line` is a dump convenience (2026-10-01)

`MemoryModel.read(address, length)` / `.write(address, data, strobe)` take a
**byte address** -- they slice `self.mem[address:address+length]` directly. The
`bytes_per_line` constructor argument shapes the dump and the access maps; it is
NOT an index unit, and nothing converts for you.

So a test that thinks in device words (a DRAM column, a cache line) must scale
to bytes itself. If the DUT's own model writes through a translation -- on the
DFI slave, `DFISlavePHY._byte_addr(flat) = flat * device_bytes` over
`AddressMapping.tuple_to_flat(rank, bank, row, col)` -- then a test that peeks
the backing store has to use **that same translation**, not a formula of its
own. Ask the framework for the address; do not re-derive it.

*Case: scoria's first top-tier test divided the AXI byte address by the device
size and handed the result to `read()` as if it were a line index. The tell was
specific and worth recognising: a 16-byte read of a just-written beat came back
as four overlapping copies of the data, each shifted ONE byte --
`4aebe859 ebe859c9 e859c9b3 59c9b3dd` against a written
`4aebe859 c9b3dd38 3e29e986 1868ab75`. That is a stride-1 walk over 4-byte
reads, i.e. an index being used as an address. Round-trip cases passed
throughout, because a write and a read through the same wrong scale cancel --
only the case that checked an ABSOLUTE address saw it, which is the reason that
case exists. The framework's own `_byte_addr` carries a comment making the same
point about the same mistake.*

## Out of range means one thing (2026-09-09)

Every memory-backed slave BFM -- AXI4, AXI5, AXIL4, AXIL5 `Slave{Read,Write}`,
`APB`/`APB5 Slave` and `WB4Slave` -- answers an access beyond its `MemoryModel` the
same way: **SLVERR** (`PSLVERR` on APB, `ERR` on Wishbone), **nothing written** (an AXI write
burst is checked whole before any beat lands), **read data 0xDEADDEAD**
replicated to the beat width, **one WARNING** naming the slave, the address
and the model size. It is one code path, `MemoryModel.in_range` /
`oor_warning` / `oor_read_data` in RDS-DV `shared/memory_model.py`, and a
structural unit test there asserts every family calls it.

*Case: before this, the four families disagreed -- AXI4/AXI5 answered OKAY,
dropped the write and returned the ADDRESS as read data; AXIL answered
SLVERR; APB grew its memory. The bridge's boundary probe reached the right
slave past its 4 KB model, got OKAY from an AXI4 slave and SLVERR from an
AXIL one, and the TB comment that called the silent OKAY "the framework
behaviour" was true of one slave type. The tests were first "fixed" by
widening the model (bridge BUG-006, was BRIDGE-008); the disagreement stayed until this.*

*Case 2 (2026-09-11): `WB4Slave` was written after the contract and did not
follow it -- a bounds miss raised inside its sampling loop and the whole BFM
died, and it addressed memory with the raw `ADR`, so it could not sit at a
fabric address at all. Both surfaced the day a bridge put a Wishbone
completer at 0x5000_0000 (bridge TASK-008, was BRIDGE-019). A new slave family is not done until
it has `base_addr` and the OOR path; the structural unit test in RDS-DV is
the place to add the new class.*

Two consequences for a TB:

- `single_write` / `write_transaction` do **not** raise on an error response;
  they report it in the returned dict. A helper that awaits the write and
  drops the dict passes a SLVERR write silently -- the bridge's generated
  `master_write` did exactly that. Check `result['success']` (or raise).
- The model's limit is not the design's. An address the RTL does not decode
  at all is the design's own error path (the bridge's subtractive slave
  answers DECERR); a probe past the model is answered by the slave the
  address decodes to, and that SLVERR coming back from the right port is
  routing evidence, not a failure.

`APBSlave(error_overflow=False)` keeps the old grow-the-memory behaviour for
a slave meant to accept any address; the default is now the error.

## An ID in flight is a resource (2026-09-10)

The AXI5 BFMs key their response queues on transaction ID: every R or B
beat lands in a per-ID deque and the coroutine that issued that ID pops it.
Two transactions in flight with one ID therefore share one queue, and the
first coroutine to wake takes whichever beat arrived, regardless of whose
it was. AXI itself only permits same-ID reuse for ordinary reads and
writes; an atomic must not share its ID with ANY outstanding transaction
from the same Manager, because a read-return atomic answers on R under its
AW ID and that is the only thing that tells its beat from a read's.

Measured on the bridge A5-3b sign-off test at full depth: a concurrency
phase rotated 14 IDs over 32 in-flight transactions, so word seven reused
word zero's four IDs while word zero was still outstanding. A read then
starved for 5000 cycles waiting on a queue another coroutine had drained,
and it looked exactly like a routing bug in the fabric. The fabric was
fine. The fix is structural, not a bigger timeout: batch the traffic so
that everything in flight at once holds a distinct ID (with a 4-bit ID and
four transactions per word, three words per batch), and await the batch
before reusing one. `AXI5ComplianceChecker` now records ATOMIC_ID_IN_USE
when an atomic is issued under an ID a read or write still holds, and
R_WITHOUT_REQUEST for an R beat nobody asked for; the first would have
named this in the compliance report had the test reached it.

For read-return atomics themselves: `AXI5MasterWrite.atomic_operation`
takes `read_channel=` (the port's `AXI5MasterRead`) and returns
`read_data` / `read_resp` alongside the B result; the paired
`AXI5SlaveWrite` performs the operation on its memory model and hands the
original data to `AXI5SlaveRead.send_read_return`. The generated bridge TB
pairs the two slave BFMs for every AXI5 rw slave.


## Deterministic backpressure is ready_policy, not ready_delay (2026-09-16)

To hold a consumer's ready low ON PURPOSE -- proving a producer parks its
payload, or stalling a DUT long enough to trip a timeout -- set
`slave.ready_policy = 'stall'` at runtime and set it back to `'valid_first'` to
release. A large randomized `ready_delay` looks equivalent and is not: phase 2
latches one delay per transaction and nothing can shorten it once taken, so a
test that must stall AND THEN RECOVER cannot get its recovery half back.
`GAXISlave`'s own constructor comment says so -- randomized `ready_delay`
"cannot do that: it is not controllable."

The three policies: `'valid_first'` (default; the wait for valid is clocked, so
ready lands one cycle AFTER valid even at `ready_delay=0`), `'always'` (ready
asserted up front, so valid and ready coincide -- the honest model of a
consumer with permanent space), `'stall'` (held low).

Where it bit: the directed `src_timeout` test for `cdc_4_phase_handshake`. It
stalls the destination past `TIMEOUT_CYCLES`, then must lift the stall and see
the transfer complete and the flag clear. Built on a parked `ready_delay` the
second half is unreachable, and the test would have quietly checked only that
the timeout fires -- never that it clears.

## Extract a BFM, or keep it embedded (2026-09-20)

Two questions get conflated. **Is it a standard protocol?** decides whether you
write anything at all: AXI4, AXIL, APB, AXIS or a plain valid/ready handshake
are already in the framework, and the answer is to use it -- at any size. Only
genuinely custom behaviour gets written, and then size decides where it lives:

| | Extract to a BFM | Keep it in the testbench |
|---|---|---|
| Size | >100 lines | <50 lines |
| Reuse | several tests | one test |
| Logic | real protocol state | simple stimulus/response |

RAPIDS has one of each.
`projects/components/dma-ip/rapids/dv/components/data_mover_bfm.py` (150+ lines, custom
data-mover protocol, shared across scheduler tests) was extracted; the ~50-line
AXI read responder inside `descriptor_engine_tb.py` stays embedded, because the
framework covers AXI4 properly and the responder is only a test-local stub.

What this prevents is the 200-line hand-written "AXI4 read responder BFM" -- a
reimplementation of something the framework ships, which diverges from the
protocol at the first corner case.

## A hand-rolled driver has a write-timing hazard a BFM does not (2026-09-26)

`val/amba/test_mon_cg_gating.py` drives the monitored wrappers by hand -- a
deliberate choice, since it tests the clock gate, not the protocol. Its response
driver set `rvalid` right after a `RisingEdge`, waited for `valid && ready` at a
falling edge, then held one more edge "to let the rising edge consummate it".
Under cocotb + Verilator a write made in a rising-edge timestep is applied
before that edge's `always_ff` sampling, so the beat was consummated at the
write's own edge, and the hold delivered it a second time. Probed: two
downstream and two upstream response handshakes per transaction, on every
wrapper, for as long as the test has existed.

Twenty-four green cells hid it. The full monitor does not emit read-data
orphans, so the second beat changed nothing it reported. `axi_monitor_lite`
does: the first run of the `_monlite_cg` wrappers failed phase 6 on all 32
cells with an extra `AXI_ERR_DATA_ORPHAN` packet behind the completion. The
test was wrong and the new DUT was the first strict enough to say so -- the
[[escape-analysis]] shape where a stricter checker exposes a stimulus defect
the lenient one absorbed.

The first fix was a patched hand driver (`respond_once()`, writing at falling
edges). Sean's answer to that was "Never hand roll BFMs!!!!!!!!", and he is
right: the patch fixed the one hazard it had found and kept the surface that
grows them. The test is now driven entirely by the framework BFMs the
family's own monitor TB class already builds -- the master BFM issues the
transaction, the slave BFM's memory model answers it, and every stall the
six phases need is a `set_ready_policy('stall' | 'always')` on the upstream
response receiver, the downstream request receivers or the MonbusSlave. The
test reads pins to observe handshakes and gating; it drives only config pins.
Sixteen wrappers per family pass unchanged, because the BFMs never delivered
the beat twice in the first place.

The BFMs' timing is not typed into the test either. Every valid_delay and
ready_delay comes from the repo's shared profile table,
`bin/TBClasses/amba/amba_random_configs.py` (`AXI_RANDOMIZER_CONFIGS`,
`GAXI_RANDOMIZER_CONFIGS`: fixed, constrained, fast, backtoback, burst_pause,
slow_producer, slow_consumer, high_throughput and the gaxi_* patterns), and the
profile is a test axis -- the gating test runs 'backtoback' for the deterministic
zero-gap case and 'constrained' so the gate/ungate boundaries land at varied
points of a transaction. A monitor TB class that keeps its own private delay
table (the AXI4/AXI5 base TBs do) is the older pattern; new tests take the
shared one.

The rule this file already states covers it, with no exception for
"structural" tests: a framework BFM drives at the falling edge and never has
this hazard, and a test that needs a stall asks the BFM for one
(`ready_policy`) rather than driving the pin. There is no "must hand-drive"
case; if the BFM lacks a control the test needs, the fix is in the BFM.


## A BFM walks every top-level handle when it binds (2026-09-27)

`SignalResolver` (every GAXI-derived BFM: AXIS, GAXI, the AXI4 channels) calls
`get_top_level_ports(dut)` before it resolves anything, and that helper reads
`.value` on EVERY child of the DUT handle to decide whether it is a signal.
Under Verilator, cocotb's `.value` on a 2-D unpacked array raises
`IndexError: unknown(GPI_ARRAY) contains no object at index -1`, which the
helper does not catch -- so a top-level module that declares
`logic [15:0] x [NUM_PORTS][NUM_CHANNELS]` cannot have an AXIS master bound to
it at all, whatever the pin names. `axis4_intf_observer` hit it on its first
build; `axi4_intf_master_observer` declares the same shape and never did,
because its TB binds only `APBMaster`, which does not walk.

The fix is in the RTL, and it is the right shape anyway: pack what a TB may
need to read (`logic [NUM_PORTS-1:0][NUM_CHANNELS-1:0][15:0] x`) and keep
1-D unpacked arrays for what a shared submodule insists on, bridged inside a
generate block where the walk does not look. The companion trap in the same
build: a test compile has no `-Wno-fatal`, so a parameter-degenerate shape a
lint run merely reports (`monbus_arbiter` at `CLIENTS=1` sizes its grant id
`[-1:0]`, ASCRANGE) stops the build. Pad the degenerate case
(`ARB_CLIENTS = max(2, NUM_PORTS)`) rather than waive the warning.

One more line on the rule above ("there is no must-hand-drive case"): a
PROTOCOL VIOLATION is the one stimulus a compliant BFM cannot emit. The AXIS
observer's `AXIS_ERR_VALID_TIMING` (TVALID withdrawn before the handshake) is
driven on the pins in one helper that says so, with the BFM idle around it.
The proper home for that is an injection control on `AXISMaster` in RDS-DV;
until it exists, keep such a helper to one place, name the violation in it,
and never let it touch a pin the BFM is mid-transaction on.

## A protocol checker armed in the constructor judges the reset window (2026-10-16)

`AXI4ComplianceChecker` and `AXI5ComplianceChecker` start sampling in their
constructors. A TB that builds them in `__init__` therefore checks from sim
time 0, inside reset and before the first clock edge has applied any async
reset. A simulator does not see an async reset that is already low at time 0
as an edge, so every flop holds its initial value (0 under Verilator) until
the first clock. Most VALIDs are flops and read 0, but an async FIFO's
VALID is its inverted empty flag, so it reads 1. The first edge then resets
it to 0 with READY low, and the checker records "VALID deasserted before
handshake completed". The bridge's CDC master ports (`axi4_cdc_{wr,rd}`,
GitHub #119 L2) hit this on their first run: B and R on the CDC ports only,
on all three tests. Silicon is unaffected, because an async-reset flop
clears while reset is held.

Build checkers after reset is released (the bridge TB template stores a
factory per port and builds it in `setup_clocks_and_reset`), and make
`assert_compliance` fail if a declared checker was never built. An empty
set of checkers passes vacuously (see [[test-review]]). Calling
`setup_monitors()` on a checker that its constructor already armed starts
every loop twice.

## Same-ID calls in flight can swap responses (2026-10-16)

The AXI4 and AXI5 requester BFMs keep one response queue per ID. Every
`read_transaction` / `write_transaction` waiting on that ID polls the same
queue, and the first call to wake takes the beats, not the oldest request.
`send()` returns before the address handshake, so a later call is often
already waiting. Two calls on one ID from one port can therefore swap
responses even though the DUT returned them in order. The bridge's
`test_bridge_2x2_axi5_wakeup[full]` (SEED=80505) failed this way: a later
write took an earlier one's B, started its read early and took that read's
R. The bridge's port trace showed both returned in order.

**Fixed in cocotb-framework 1.2.3 (RDS-DV #94).** The AXI3, AXI4, AXI5 and
ACE requesters now give each call a ticket when its address is queued, and a
call takes beats only at the head of its ID's line, so concurrent same-ID
calls are served in issue order. The wakeup test dropped its per-ID `Lock`
workaround; with the Lock removed, SEED=80505 fails on 1.2.2 and passes on
1.2.3. Before 1.2.3, keep one transaction per (port, ID) in flight in test
code.

`axi4_sequence.py` still pops `_response_by_id` directly. It orders its own
bursts, but do not mix it with concurrent `*_transaction` calls on one ID.
Before blaming the DUT for swapped same-ID data, trace AR/R or AW/B order at
the port.

## A requester has two timeouts, and the inner one drops the transaction (2026-10-17)

An AXI4 requester BFM (`AXI4MasterRead` / `AXI4MasterWrite`) times out in
two places. `timeout_cycles` on the requester (default 5000) bounds a
call's wait for its response. Each channel driver underneath it --
`aw_channel`, `w_channel`, `ar_channel`, all `GAXIMaster` -- has its OWN
`timeout_cycles` (default 1000) for the READY wait of one beat. Raising the
first does not raise the second. When the inner one fires, the transmit
pipeline logs `Phase2: TIMEOUT waiting for ready`, drops that beat, and
moves on to the next queued one; the call that owned it then waits for a
response to a request the DUT never received.

Where it bit: a bridge bandwidth run of eight 256-beat writes over an 8:1
downsize. The bridge legitimately holds AWREADY low ~2047 cycles while its
converter drains one burst into the narrow slave. The AW driver gave up
after 1000, dropped AWs 6 and 7, and the test hung waiting for their B --
which read as a bridge deadlock for most of a day, and drew one wrong RTL
"fix" before a waveform showed every AW the bridge accepted got its B.
Until RDS-DV 1.2.4 the timeout raised `cocotb.result.TestFailure`, gone in
cocotb 2.x, so the log said "module 'cocotb' has no attribute 'result'"
instead of naming the timeout. **Before suspecting the DUT in a hang, grep
the log for `Phase2: TIMEOUT`**, and when a long legal stall is the point
of the test, raise both timeouts (the bridge perf harness's `pipeline()`
does).

For bandwidth, set `pipelined=True` on the requester (RDS-DV 1.2.4): each
call then queues its address and W beats on the driver instead of waiting
for the pipeline to drain, so back-to-back calls keep VALID high. Without
it the requester itself caps a write stream at 0.89 beats/cycle and the
gap gets blamed on the fabric.

## The AXI4 slave's memory model steps every beat by its size (2026-10-20)

`AXI4SlaveRead` / `AXI4SlaveWrite` with a `memory_model` address beat `i` of
a burst at `AxADDR + i * 2^AxSIZE`, whatever AxBURST says. That is AXI only
for an aligned INCR burst. A FIXED burst should hit one address every beat;
a WRAP burst should wrap at its container; an unaligned INCR start should
realign from the second beat on. Against the model, all three read and write
the wrong bytes, and a DUT that drives them correctly fails its data check.
(Narrow beats are fine: both paths place them on their lanes since RDS-DV
593c279, above.)

Where it showed: the bridge stress model's mem windows
(`val/amba/test_axi_stress_mem.py`, `bs_harness_bridge_bs_xil` in
bridge-stress) put a stress master on the model as a real memory. Both
restrict that window to aligned INCR, and say so; the other burst shapes
against a real memory are covered on the board (MIG, the AXI BRAM
controller). **Give a memory-model slave aligned INCR only, or model the
burst yourself in the test** -- and do not read a FIXED / WRAP failure there
as a DUT bug. Fixing it is an RDS-DV change with ~80 consumers; it needs the
owner's go-ahead first.


## A cycle checker samples AFTER the falling edge (2026-10-25)

A cycle-accurate checker that reads pins has the mirror of the driver hazard
above. `GAXIMaster` drives `valid`/data right after the rising edge
(`RisingEdge` then 200 ps); `GAXISlave` drives `ready` AT the falling edge.
A checker that does `await FallingEdge(clk)` and then reads `rd_ready` races
the slave's write in the same timestep: whichever coroutine the scheduler
resumes first wins, and the model records the read a cycle late. On
`gaxi_age_fifo_sync` that was two `count` mismatches per packet, every
packet, with every age output correct -- it looked like a FIFO bug and was
sampling order.

Sample a fixed step past the edge the BFMs drive on, and put any TB-side
"wrapper mirror" (a process that derives one DUT input from a DUT output the
way the real instantiating RTL would, e.g. `wr_data_age = youngest + 1`)
between the two:

```python
# slave BFM drives ready AT the falling edge
await FallingEdge(clk); await Timer(2, 'ns')   # wrapper mirror drives here
await FallingEdge(clk); await Timer(3, 'ns')   # checker samples here
# outputs = state after every edge so far; inputs = what the next edge latches
```

and advance the model from those inputs in the RTL's own order. Two things
the model must then know about this FIFO family: `count` from `fifo_control`
with `REGISTERED=0` is COMBINATIONAL off the next pointers, so it already
includes the handshakes in flight this cycle while `wr_ready`/`rd_valid` are
registered and do not; and a reader "parked" by poking `rd_ready = 0` is
overwritten by the slave BFM at the next falling edge -- park it with a
profile whose `ready_delay` is fixed far out (`'parked': ready_delay 400`),
the same rule as `ready_policy` above: ask the BFM, never drive its pin.
