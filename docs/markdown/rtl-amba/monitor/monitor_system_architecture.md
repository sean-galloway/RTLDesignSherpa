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

## Architecture

```
   DETECT                  SHAPE                    TRANSPORT           CAPTURE
   ------                  -----                    ---------           -------

 protocol wrapper      axi_monitor_base           monbus_arbiter    monbus_*_group
 axi4_master_rd_mon      trans_mgr (CAM)            (N:1 merge,       ├─ error FIFO
 axi5_slave_wr_mon       timer / timeout            packet+ts         │   -> AXI read
 axil4_*_mon             reporter_error            atomic)           │      (IRQ)
 apb_monitor             reporter_timeout               │            └─ write FIFO
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
| `axi_monitor_reporter_perf` | `PktTypePerf`, `PerfWin`, `PerfHist` | throughput and utilization |
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

`ENABLE_PERF_PACKETS` turns on a measurement-window state machine that buckets
every cycle into one of four states and reports at window close:

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
