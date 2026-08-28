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

# The Monitor System

**What it is:** on-chip observability that emits a fixed 128-bit packet whenever
something worth knowing about happens -- an error, a timeout, a completion, a
performance sample, a debug trace point -- and a set of transports that get
those packets off the chip.

**What it is not:** protocol-specific. The packet format, the transports, the
filtering and the capture back ends know nothing about AXI. A protocol wrapper
supplies detection; everything downstream is shared. That is why an arbiter --
which is not a bus protocol at all -- rides the same infrastructure as AXI4.

**Scope of this document.** The architecture and what it can do. Per-module
detail lives in the module pages; the packet field map and event-code
assignments live in [monitor_package_spec](../includes/monitor_package_spec.md).

---

## The one thing to understand first

Everything is a `monitor_packet_t`: 128 bits, laid out identically no matter who
produced it.

| Bits | Field | Width | Meaning |
|---|---|---|---|
| `[127:124]` | `packet_type` | 4 | error, timeout, completion, perf, debug, ... |
| `[123:109]` | reserved | 15 | forward-compat slack |
| `[108:105]` | `protocol` | 4 | AXI / AXIS / APB / ARB / CORE |
| `[104:97]` | `event_code` | 8 | which error, which event, which metric |
| `[96:88]` | `channel_id` | 9 | channel, or AXI transaction ID |
| `[87:72]` | `agent_id` | 16 | which instance |
| `[71:64]` | `unit_id` | 8 | which subsystem |
| `[63:0]` | `event_data` | 64 | payload -- a full 64-bit address fits |

A 64-bit timestamp travels beside the packet as side-band, not inside it. The
pair `(packet, timestamp)` is carried atomically from the point of emission all
the way to the capture back end -- `monbus_arbiter` moves both through a
192-bit skid precisely so a consumer can never observe a packet against the
wrong timestamp.

The consequence worth internalising: **`{protocol, packet_type, event_code}` is
a message identity.** Filtering keys on it. The coverage histogram bins on it.
The compressor templates on it. Adding a new event to a new kind of block means
choosing a `protocol` and allocating `event_code` values -- and the rest of the
system already handles it.

---

## Two coordinate systems and a topology

This is the property that makes one 128-bit word serve a whole SoC, and none of
it is obvious from the field list.

**Read the first two as coordinate systems, not as a tree with a fixed root.**
The packet carries a classification (*what happened*) and an identity (*who it
happened to*), and the two are orthogonal. Neither is the base. It is entirely
reasonable to organise by `protocol` and treat identity as an attribute of the
event -- and equally reasonable to organise by `unit_id` and treat the
classification as an attribute of the block. The packet is indifferent.

That choice is not cosmetic. Putting `unit_id` first scopes `protocol` inside it
and turns a hard 16-protocol ceiling into an effectively unbounded space --
see [Precedence decides how many protocols exist](#precedence-decides-how-many-protocols-exist)
below, which is the most consequential decision on this page.

Today's *hardware* consumers happen to be classification-major: the filter masks
are per-protocol then per-type (`cfg_axi_pkt_mask`, `cfg_axis_error_mask`, ...),
and `monbus_pkt_tally` addresses its histogram with
`{protocol, pkt_type, event_code}` directly. That is an implementation choice of
those two blocks, not a property of the format -- **nothing in the monitor
hardware filters or indexes on `unit_id` or `agent_id` at all.** A unit-major
consumer ("show me everything subsystem 9 did, whatever protocol") is just as
legitimate, needs no change to the packet, and is what a software decoder
typically wants; `get_unit_id()` and `get_agent_id()` exist for exactly that.

If a future block wants to filter or bin by identity, the packet already carries
what it needs. Only the consumer is missing.

### Precedence decides how many protocols exist

This is not a reporting preference. **Precedence determines whether `protocol`
is a global namespace or a per-unit one, and that changes the ceiling by a
factor of 256** -- 16 protocol identities against 256 x 16 = 4096, with the
full message space scaling by the same 256x (see the table below).

`protocol` is 4 bits. Read protocol-major -- `protocol / packet_type / unit` --
and those 4 bits are a **global** namespace: 16 protocols for the entire SoC,
for all time, 5 already spent. Every new one must be centrally allocated and
must never collide with anything, anywhere. It is a scarce, coordinated resource
and it runs out.

Read unit-major -- `unit / protocol / type` -- and `protocol` is **scoped by
`unit_id`**. Unit 9's protocol 3 and unit 12's protocol 3 are unrelated. Nothing
central allocates them; each unit owns its own 16.

| | protocol-major | unit-major |
|---|---|---|
| `protocol` namespace | global | per `unit_id` |
| distinct protocol identities | **16** | 256 x 16 = **4096** |
| full message space | 16 x 16 x 256 = 65,536 | 256 x 16 x 16 x 256 = **16,777,216** |
| allocating a new protocol | central registry, collides SoC-wide | local to the unit, collides with nobody |

For any practical purpose the unit-major space is unbounded -- you exhaust
`unit_id` long before you exhaust protocols, and `unit_id` is the field you were
going to assign per-block anyway.

**This is the same mechanism as `event_code`, applied one level up.** `event_code`
is already scoped per `{protocol, packet_type}` rather than globally, which is
why adding events never competes with existing assignments. Scoping `protocol`
under `unit_id` extends that property to protocols themselves. The packet
already works this way one level down; the only question is how far up you take
it.

**What it costs.** A protocol-major packet is self-describing: any decoder can
read `protocol` and know what it is holding, with no context. A unit-major
packet is not -- `protocol = 3` means nothing until you know the unit, so every
consumer needs the unit-to-protocol map, and that map becomes a real artifact
the project must maintain and version. You also give up the free global query:
"every AXI error in the SoC" is one mask protocol-major, and a map lookup per
unit otherwise.

So it is a genuine trade: **a hard 16-protocol ceiling with zero bookkeeping,
against an effectively unbounded space that requires a maintained map.** Small
or single-protocol projects should take the ceiling. Large multi-team SoCs,
where blocks arrive with their own event vocabularies and no one wants a central
protocol registry, should take the map.

### Fix the choice per project

Whichever you pick, **pick once and hold it for the life of the project.** A
different project may reasonably pick the other; two consumers inside the same
project may not -- with unit-major especially, since a consumer that assumes
global `protocol` will silently mis-decode every packet from a unit that reused
a value.

Precedence also leaks into everything downstream: decoder grouping, coverage
report row order, the register map a filter is programmed through, dashboards,
and the shorthand people use in bug reports. Half a project sorting one way and
half the other makes all of those incomparable.

Nothing in the RTL enforces either choice -- the packet is a flat tuple and no
hardware indexes on identity -- so this is a convention, and conventions need a
home. Record it where the project records its other integration decisions,
alongside the `UNIT_ID` and `AGENT_ID` assignments, since those are the same
conversation. If the project is unit-major, the unit-to-protocol map lives there
too.

### Coordinate A -- classification: what happened

```
protocol  (4b, 16 slots)   AXI / AXIS / APB / ARB / CORE
  └─ packet_type (4b)      error / timeout / completion / threshold / perf / debug / ...
       └─ event_code (8b)  ARB_ERR_STARVATION, AXI_PERFWIN_BP_CYCLES, ...
```

Each level narrows the one above, and **each level is independently useful**. A
consumer that only understands `packet_type` can still sort errors from
performance samples in a stream containing protocols it has never heard of. One
that understands `protocol` too can route AXI traffic to an AXI decoder and pass
the rest through untouched. Only the innermost level requires knowing the block.

This is what lets the filter be three-level (drop a whole type, then individual
codes within a type you are keeping) and what lets the histogram bin on the
whole tuple without knowing what any of it means.

### Healthy classes vs fault classes

The packet types split into two groups, and the split changes how you cover them.

**Healthy classes -- `completion`, `addr_match`, `perf`/`perfwin`/`perfhist`.**
These arise from *correct* operation. Every transaction completes; every access
matches a configured watch range; every window closes with utilization buckets.
Drive normal traffic and they appear. A capture that tallies them is measuring a
working system.

**Fault classes -- `error`, `timeout`, `threshold`.** These arise only from a
*misbehaving* slave or an *illegal* access, and in a correct system they **never
occur** -- the fault tally reads **zero**, and that zero is the pass condition,
the "nothing went wrong" signal. You cannot exercise them with healthy traffic;
you must **explicitly inject the fault**:

| Fault packet | Inject by |
|---|---|
| `timeout`   | a slave that does not respond (hold R/B past the timeout window) |
| `threshold` | a slave that is slow (latency past `LATENCY_THRESH`, under the timeout) |
| `error`     | a slave that returns `SLVERR`/`DECERR`, or an access outside an enabled address-range allowlist (see [axi_monitor_addr_check](axi_monitor_addr_check.md)) |

**An error, by definition, hangs the system.** A transaction that errors or is
never answered does not retire, so injecting an error *wedges* the traffic that
provoked it -- that stall is the fault, not a test artifact to engineer around.
The monitor's job, and its whole value, is to **emit the fault packet as the hang
happens** so a downstream capture records what stalled and why, instead of the
system simply going dark. Consequently, fault coverage belongs in a dedicated
fault-injection test that deliberately misbehaves the slaves -- kept separate
from the healthy-traffic capture, whose job is to assert the fault tally stays
zero.

### Coordinate B -- identity: who it happened to

```
unit_id    (8b)   which subsystem
  └─ agent_id  (16b)   which instance within it
       └─ channel_id (9b)   which channel, or which AXI transaction ID
```

Note this nests the same way the classification does, and to the same depth --
three levels, each narrowing the one above. That symmetry is why either can
serve as the major key without the other becoming awkward.

`UNIT_ID` and `AGENT_ID` are elaboration parameters on the monitor, so identity
is assigned structurally at integration time, not discovered at runtime. Two
instances of the same wrapper differ only by parameter. A consumer can aggregate
at any level -- all errors in a subsystem, or one channel of one instance --
without the producers knowing which grouping anyone intends.

### Topology -- how packets reach the capture point

`monbus_arbiter` takes `CLIENTS` monbus inputs and produces **one monbus
output of exactly the same shape**. That is the whole trick: an arbiter's output
is a valid arbiter input, so aggregation nests to any depth without a special
"root" or "leaf" module.

STREAM builds a real three-level tree this way -- one arbiter per level, each
merging the level below:

| Level | Module | `CLIENTS` |
|---|---|---|
| leaf | `scheduler_group` | 2 |
| middle | `scheduler_group_array` | `NUM_CHANNELS + 1` |
| root | `stream_core` | 3 |

Each level collapses its children onto one stream, and the packet is unchanged
by the trip -- `agent_id` still says which leaf produced it. Only the root
attaches to a `monbus_*_group` and off-chip transport. Adding a channel changes
one `CLIENTS` parameter; it does not change the packet, the transport, or any
consumer.

Note that the timestamp rides beside the packet through every level, and
`monbus_arbiter` carries the 192-bit `(packet, timestamp)` pair atomically at
each hop -- so depth in the tree does not risk pairing a packet with the wrong
time.

**The shape of the tree is arbitrary, and it is expected to change.** Nothing in
the packet, the transport or any consumer encodes how many levels there are,
which leaf hangs off which branch, or how wide each merge is. It is an
integration choice: re-parent a block, add a level, collapse two levels into one
wider `CLIENTS`, and every downstream stage behaves identically. That freedom is
the point of the input/output symmetry -- the tree can be re-drawn to match
floorplan or timing without touching a line of monitor logic.

Two consequences follow, and both are contracts rather than advice:

- **Arrival order across producers means nothing.** Each level merges with
  `arbiter_round_robin` in ACK mode, so the interleaving you observe is a
  product of arbitration phase, backpressure and tree shape -- all three of
  which can change. **Order packets by their timestamp, never by the order they
  came out of the pipe.** A consumer that infers causality from arrival order is
  reading an artifact of the topology it was captured on, and will silently
  disagree with itself when the tree is re-drawn.
- **Per-producer order IS preserved.** A single producer's packets stay in the
  order it emitted them, at every level, because arbitration reorders *between*
  clients and never *within* one. So "this agent's events, in sequence" is
  reliable; "these two agents' events, interleaved" is not.

What the tree does guarantee is fairness and no loss: round-robin prevents a
chatty leaf from starving a quiet one, and the grant-hold contract (the grant
retires only on `grant && valid && ready`) means backpressure delays packets
rather than dropping them. Depth costs latency, never data.

---

## Adaptability: what is deliberately left open

The format is locked, which is what makes bit-exact tooling possible. It is not,
however, full:

| Space | Used | Free |
|---|---|---|
| `protocol` | 5 (AXI, AXIS, APB, ARB, CORE) | 11 slots |
| `packet_type` | 13 | `0xA`, `0xB`, `0xC` reserved |
| `event_code` | per `{protocol, packet_type}` | 8 bits *per pair* |
| reserved bits | none | `[123:109]`, 15 bits of forward-compat slack |
| `event_data` | payload | 64 bits, fits a full address |

The `event_code` row is the important one. Because the code is scoped by the
`{protocol, packet_type}` pair rather than global, a new protocol gets a fresh
256-value space for each packet type it uses. Extension does not compete with
existing assignments, so nobody has to coordinate a global registry.

`PROTOCOL_CORE` exists as the general-purpose slot for blocks that are not a bus
protocol -- reach for it before spending one of the 11 free `protocol` values.
Spend a protocol slot only when the block is a *family* worth separating in
filters and coverage reports.

The 15 reserved bits are genuine slack, not padding to a round number: they sit
between `packet_type` and `protocol`, so a future field can be added without
moving either the type tag at the top or the 64-bit payload at the bottom, and
without changing the width. Existing decoders that mask on the documented fields
keep working.

---

## Architecture

```
   DETECT                  SHAPE                    TRANSPORT           CAPTURE
   ------                  -----                    ---------           -------

 protocol wrapper      axi_monitor_base           monbus_arbiter    monbus_*_group
 axi4_master_rd_mon      trans_mgr (CAM)            (N:1 merge,       ├─ error FIFO
 axi5_slave_wr_mon       timer / timeout            packet+ts         │   -> AXI read
 axil4_*_mon             reporter_error            atomic)           │      (IRQ)
 apb4_monitor             reporter_timeout               │            └─ write FIFO
 apb5_monitor            reporter_compl                 │                -> AXI write
                         reporter_threshold             │                (bulk trace)
 custom producer         reporter_perf                  │                   │
 arbiter_rr_pwm_monbus   reporter_debug                 │            monbus_compressor
 arbiter_wrr_pwm_monbus       │                         │            (optional, in-line)
 your block                   │                         │
       │                      ▼                         │            monbus_pkt_tally
       └──────────────> axi_monitor_filtered ───────────┘            (counting only)
                        (3-level drop filter)
```

Four stages, and you can stop after any of them.

### 1. Detect

A **protocol wrapper** pairs one protocol block with the shared monitor core.
`axi4_master_rd_mon` instantiates `axi4_master_rd` and `axi_monitor_filtered`;
the wrapper's whole job is to present protocol signals to a core that does not
know what AXI is. These live with their protocols (`rtl/amba/axi4/`, `axi5/`,
`axil4/`, `apb/`, `apb5/`), not in `rtl/amba/monitor/`.

For AXI-shaped traffic the core tracks outstanding transactions in
`monitor_trans_cam`, a multi-port ID CAM with payload storage, managed by
`axi_monitor_trans_mgr`. That table is what makes completion, timeout and
latency reporting possible: an event is attributed to the transaction that
caused it.

**A custom block skips all of this.** See "Instrumenting something that is not a
bus protocol" below.

### 2. Shape

`axi_monitor_base` decides what is worth reporting, through six reporters that
each own one packet type:

| Reporter | Emits | Answers |
|---|---|---|
| `axi_monitor_reporter_error` | `PktTypeError` | a protocol or response error occurred |
| `axi_monitor_reporter_timeout` | `PktTypeTimeout` | a transaction outlived its budget |
| `axi_monitor_reporter_compl` | `PktTypeCompletion` | a transaction finished (and how long it took) |
| `axi_monitor_reporter_threshold` | `PktTypeThreshold` | a watermark was crossed |
| `axi_monitor_reporter_perf` | `PktTypePerf` only | lifetime completion/error count rollups. **Not** PerfWin/PerfHist -- nothing packetizes the window buckets onto the MonBus yet (see Performance Monitoring below); they are readable as counters only |
| `axi_monitor_reporter_debug` | `PktTypeDebug` | trace points |

Each has an `ENABLE_*_LOGIC` parameter that removes its detection cone at
elaboration. This matters: an unused reporter is not gated at runtime, it is
**not built**. `ENABLE_TIMEOUT_LOGIC=0` also drops the `axi_monitor_timeout`
instance outright. Size the monitor to what you will actually read.

### 3. Filter

`axi_monitor_filtered` applies a three-level drop filter *at the source*, before
a packet ever consumes transport bandwidth:

1. **`cfg_axi_pkt_mask`** -- drop whole packet types (16 bits, one per type).
2. **per-type event masks** -- `cfg_axi_error_mask`, `cfg_axi_timeout_mask`,
   `cfg_axi_compl_mask`, `cfg_axi_thresh_mask`, `cfg_axi_perf_mask`,
   `cfg_axi_addr_mask`, `cfg_axi_debug_mask`. Drop individual event codes
   within a type you are otherwise keeping.
3. **address-range selection** -- `axi_monitor_addr_check` (and
   `apb_monitor_addr_check` for APB) restrict reporting to address windows.

Filtering at the source rather than at the consumer is deliberate. The monitor
bus is a shared resource and the failure mode is congestion: enable everything
at once and the interesting packets queue behind the boring ones.

### 4. Transport and capture

`monbus_arbiter` merges N producer streams into one, carrying packet and
timestamp atomically. The `monbus_group` family then provides two independent
drains from one `monbus_group_core`:

- **Error / interrupt path** -- a FIFO drained over an AXI4-shaped *slave read*
  interface, 192 bits per record. An IRQ handler walks records as 3 x 64-bit
  beats; `arlen` may fetch several records per burst. This is the "wake the CPU,
  something is wrong" path.
- **Master-write path** -- a beat-granular FIFO drained over an AXI4-shaped
  *master write* interface with watermark and timeout flush, bursting as far as
  FIFO contents, `MAX_BURST_BEATS`, the 4 KB boundary and the address-window
  wrap allow. This is the bulk-trace path.

Four wrappers exist for the four combinations of interface width on those two
ports: `monbus_axi4_axi4_group`, `monbus_axi4_axil_group`,
`monbus_axil_axi4_group`, `monbus_axil_axil_group`. They are wrappers only --
the logic is in `monbus_group_core`.

---

## Choosing a capture strategy

This is the decision that actually shapes a deployment, and there are three
answers.

| | Bulk trace | Compressed trace | Counting |
|---|---|---|---|
| Module | `monbus_group_core` write path | `+ monbus_compressor` | `monbus_pkt_tally` |
| Off-chip cost | 24 B per record | ~8 B per record on template hits | zero until readback |
| Run length | bounded by log SRAM depth | bounded, but several times longer | **unbounded** |
| Keeps | every packet, exactly | every packet, exactly | counts per message identity |
| Loses | nothing | nothing | ordering, timestamps, payloads |
| Use when | debugging a specific failure | long capture, still need every packet | "did this ever happen?" |

### Bulk trace

Raw mode emits complete 24-byte (3-beat) records. Simple, exact, and the run
length is whatever your log SRAM holds.

### Compressed trace -- `monbus_compressor`

Opt in per wrapper via `USE_COMPRESSION`. It sits in front of the master writer
and turns `(packet, timestamp)` records into 64-bit self-tagged slots:

| Tag | Format | Beats | When |
|---|---|---|---|
| `0x0` | RAW escape | 3 | no template match |
| `0x1` | T1-A | 1 | template hit, small payload |
| `0x2` | T1-B | 1 | template hit, big `delta_ts` |
| `0x3` | T1-C | 1 | template hit, `event_data` delta |

A 32-entry true-LRU CAM (`monbus_cam`) holds the templates, keyed on message
identity. Each entry stores **its own** last timestamp, so `delta_ts` is
measured per template -- interleaved producers do not force each other into the
raw escape. Throughput is one record per cycle on template hits, one per three
cycles on escapes.

The format is a locked spec, and the acceptance criterion is unusually strong:
the hardware slot stream is **bit-exact** to what the Python `Encoder` in
`bin/TBClasses/monbus/monbus_compressor.py` produces from the same record
sequence. Per-tier hit counters (`tier1_a`, `tier1_b`, `tier1_c`,
`tier0_escape`) let you measure the compression you are actually getting rather
than assuming it.

`monbus_halfbeat_packer` sits downstream and packs two 30-bit half-slots into
one 64-bit beat where the format allows.

### Counting -- `monbus_pkt_tally`

The one that changes what is *possible* rather than what is efficient.

It counts accepted packets into an SRAM histogram addressed by
`{protocol, packet_type, event_code}`, fronted by a 32-entry LRU
write-combining cache so back-to-back hits on hot bins never reach the SRAM.
One readback sweep dumps the matrix.

**A counter absorbs any arrival rate.** The trace paths are bounded by log SRAM
depth; the tally is not bounded at all. A coverage run can span millions of
cycles. This is the silicon twin of the simulation-side packet-type coverage
matrix (`bin/monbus_coverage_report`, `TBClasses.monbus.parse`) -- a bin count
greater than zero means *this message was observed on hardware*.

You give up ordering, timestamps and payloads. If the question is "which of
these 200 events ever fired in a week of running", that is the right trade.

---

## Instrumenting something that is not a bus protocol

The system was built for AXI and then generalised, and the arbiters are the
proof that the generalisation is real. `PROTOCOL_ARB` is a first-class protocol
with its own event codes:

| Code | Event |
|---|---|
| `0x0` | `ARB_ERR_STARVATION` -- a client never got service |
| `0x1` | `ARB_ERR_ACK_TIMEOUT` |
| `0x2` | `ARB_ERR_PROTOCOL_VIOLATION` |
| `0x3` | `ARB_ERR_CREDIT_VIOLATION` |
| `0x4` | `ARB_ERR_FAIRNESS_VIOLATION` -- weighted round-robin is not honouring weights |
| `0x5` | `ARB_ERR_WEIGHT_UNDERFLOW` |
| `0x6` | `ARB_ERR_CONCURRENT_GRANTS` |
| `0x7` | `ARB_ERR_INVALID_GRANT_ID` |
| `0x8` | `ARB_ERR_ORPHAN_ACK` |
| `0x9` | `ARB_ERR_GRANT_OVERLAP` |
| `0xA` | `ARB_ERR_MASK_ERROR` |
| `0xB` | `ARB_ERR_STATE_MACHINE` |
| `0xC` | `ARB_ERR_CONFIGURATION` |

None of these mean anything to AXI. They ride the identical packet, the
identical arbiter, the identical filter, and land in the identical histogram
bin. `arbiter_monbus_common` carries the shared production logic;
`arbiter_rr_pwm_monbus` and `arbiter_wrr_pwm_monbus` are the instrumented
round-robin and weighted round-robin arbiters.

**To instrument your own block:**

1. Pick a protocol value. `PROTOCOL_CORE` (`4'h4`) exists for exactly this --
   blocks that are not a bus. Add a new `protocol_type_t` only if your block is
   a family worth separating; there are 16 slots and 5 are used.
2. Allocate `event_code` values in a package next to
   `monitor_arbiter_pkg.sv`, and document them. The code is 8 bits per
   `{protocol, packet_type}` pair, so the space is not tight.
3. Emit a `monitor_packet_t`. Fill `unit_id` / `agent_id` so the packet
   identifies your instance, and use the 64 bits of `event_data` for whatever
   the event needs.
4. Feed `monbus_arbiter`. From that point on you inherit filtering, both
   transports, compression and the coverage histogram without writing any of it.

Step 4 is the payoff. The reason to use this system rather than adding your own
debug registers is that everything after emission already exists.

---

## Performance monitoring

Two distinct perf paths exist, and only one currently reaches the bus:

- **`PktTypePerf` rollup (implemented).** `ENABLE_PERF_LOGIC` (legacy alias
  `ENABLE_PERF_PACKETS`) builds [`axi_monitor_reporter_perf`](axi_monitor_reporter_perf.md),
  which rolls up lifetime completion/error counts and emits `PktTypePerf`
  (`AXI_PERF_COMPLETED_COUNT = 0x7`, `AXI_PERF_ERROR_COUNT = 0x8`). This is the
  perf packet you see on the MonBus today. It advances only while the output is
  idle and loses the reporter mux to completion/threshold, so it surfaces in the
  gaps between traffic rather than under sustained load.
- **`PktTypePerfWin` / `PktTypePerfHist` window+histogram (RFC Stage B/F --
  not yet emitted).** The window state machine below exists (perfmon Stage A in
  [`axi_monitor_base`](axi_monitor_base.md)) and maintains its bucket counters,
  but the code that *packetizes* those counters onto the MonBus is not wired yet.
  **No module currently emits `PktTypePerfWin` or `PktTypePerfHist`** -- the
  buckets are readable only as counters, so a MonBus tally can never bin them.
  The description below is the intended shape once Stage B/F lands.

The window state machine buckets every cycle into one of four states and (once
Stage B/F lands) reports at window close:

| Code | `AXI_PERFWIN_*` | Meaning |
|---|---|---|
| `0x1` | `PROD_CYCLES` | `valid && ready` -- productive |
| `0x2` | `BP_CYCLES` | `valid && !ready` -- backpressured |
| `0x3` | `STARV_CYCLES` | `!valid && ready` -- starved |
| `0x4` | `IDLE_CYCLES` | `!valid && !ready` -- idle |

Those four partition the window, which is what makes them useful: a link at 40%
utilization is a different problem depending on whether the other 60% is
backpressure (the consumer is slow) or starvation (the producer is). Alongside
them: `BEAT_COUNT`, `BYTE_COUNT` (beats x `1<<axsize`, masked by `strb`),
`BURST_COUNT`, window start and end timestamps, and per-channel splits
(`CHAN_PROD`, `CHAN_STARV`, `CHAN_BP`).

`PktTypePerfHist` reports histogram buckets instead of totals:
`event_code[7:4]` selects the histogram, `event_code[3:0]` the bucket
(0..15, log2 cycle thresholds). Use it for latency distributions, where a mean
hides the tail that actually matters.

---

## Configuration cautions

Two that have bitten before:

- **Do not enable every packet type at once.** `cfg_compl_enable` together with
  `cfg_perf_enable` is the documented congestion case -- completion packets are
  frequent and perf packets are bursty, and together they crowd out errors. Use
  separate test configurations.
- **The transaction table has a saturation-recovery contract.** Command-
  originated entries are capped below `MAX_TRANSACTIONS` so a saturated table
  can always drain; `cmd_entry_reserve()` in `monitor_common_pkg` is the single
  source of truth, and both `axi_monitor_trans_mgr` and `axi_monitor_base`
  derive from it. Tables smaller than 16 take reserve 0 and trade the guarantee
  for capacity. This was a comment-encoded invariant once, and that is how a
  saturation wedge shipped.

---

## Where to go next

| For | Read |
|---|---|
| Packet fields, event-code assignments | [monitor_package_spec](../includes/monitor_package_spec.md) |
| The monitor core | [axi_monitor_base](axi_monitor_base.md) |
| Filtering | [axi_monitor_filtered](axi_monitor_filtered.md) |
| Capture back end | [monbus_group_core](monbus_group_core.md) |
| Compression | [monbus_compressor](monbus_compressor.md) |
| Counting | [monbus_pkt_tally](monbus_pkt_tally.md) |
| Arbiter instrumentation | [arbiter_monbus_common](arbiter_monbus_common.md) |
| A protocol wrapper | [axi4_master_rd_mon](../axi4/axi4_master_rd_mon.md) |

---

**[← Back to Monitor Index](../_book_monitor_index.md)**
**[← Back to Main Documentation Index](../../index.md)**
