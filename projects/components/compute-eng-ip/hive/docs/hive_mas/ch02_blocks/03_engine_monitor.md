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

# engine_monitor (Block 2)

One instance. A gatling core (riscv-ip/gatling-rv32i) whose four barrel
contexts monitor the four compute engines, context *n* on engine *n*, plus
one peripheral set per engine: the counters, taps and injection path a core
alone cannot provide. Clock domain: `mon_clk`. This replaces v0.2's sixteen
`serv_monitor` instances, one SERV per tile of a 4x4 mesh (owner,
2026-11-25).

```
engine_monitor
├── gatling_core           # riscv-ip/gatling-rv32i: 4-context barrel RV32I
├── gatling_mem_bram       # riscv-ip/gatling-rv32i: one 4 KB bank + run bit per context, AXIL loader
├── engine_monitor_top.sv  # (to be written) the core, memory, peripheral decode by context
└── per engine (×4):
    ├── traffic_counter.sv # Packet/cycle counters from the router tap
    ├── trigger_logic.sv   # Threshold compare + event detect (independent of core)
    ├── axis_injector.sv   # AXIS TX (PKT_CONFIG / PKT_STATUS) into CDC FIFO
    └── ctrl_net_slave.sv  # Control-network slave + mailbox to the context
```

: Engine monitor module tree

## The core and its memory

**`gatling_core`.** Four contexts take turns, one pipeline step each
(F, D, X, W), so each context retires one instruction every four cycles and
the core one per cycle. RV32I only: every CSR reads 0, `mhartid` is 0 on
every context, there are no interrupts and no trap vector, and a trap halts
only its own context (gatling PRD §3.3, §4.4). The instruction and data
ports carry the issuing context (`imem_ctx`, `dmem_ctx`); every memory
behind them is a registered-read block RAM with one stage of latency, and
the core has no wait input.

**`gatling_mem_bram`.** One private bank per context, `MEM_WORDS` words each
(HIVE uses 1024: 4 KB, the SERV design's 2 KB I + 2 KB D), selected by the
context, never by an address bit, so all four contexts run one image linked
at one base. Its AXI4-Lite port loads a held context's bank and sets the
per-context run bits; HIVE-C drives it through its AXIL master window.

## Peripheral decode by context

The monitor top splits gatling's data port: an access below the peripheral
window goes to `gatling_mem_bram`, and an access inside it goes to the
peripheral set of the engine named by `dmem_ctx`. Every context therefore
sees its own engine's counters, triggers, injector and mailbox at the same
addresses, and the four contexts run one firmware image. This keeps
gatling's rule that contexts are implicit and binaries uniform (gatling PRD
§7 item 2). A peripheral read must return its word in W, one cycle after
the request, like the memory; the counter bank and the mailboxes are
registered reads.

Two registers in the window are the same for every engine's set except
for what they read:

| Register | Access | Contents |
|----------|--------|----------|
| `MON_ID` | RO | [31:24] the engine's Delta tile ID (the injector's `TILE_ID`); [15:8] `GATLING_ID`, a parameter of the monitor top, 0 in HIVE's one-gatling build; [7:0] the context number, `dmem_ctx` |
| `TIME` | RO | The Ocelus time base: the 32-bit count of the local `axi_monitor_timer` now, the global usync value once rtl/amba/monitors TASK-005 lands |

: Identity and time registers in each peripheral set

`MON_ID` (owner, 2026-11-25: a gatling ID along with the hart ID) does not
change gatling's core: `mhartid` still reads 0, and the context number comes
from `dmem_ctx`, which the decode already uses. Nothing in HIVE needs the
register to address an engine: the decode by context routes the accesses,
and the engine's Delta unit has its own unique tile ID, which
`axis_injector` stamps on every packet. Firmware reads `MON_ID` only to
label what it reports. (v0.2's `serv_wrapper` exposed a read-only tile-ID
register at `0xF000_0000`.)

## Observation and time

An Ocelus monitor (`rtl/amba/ocelus/`) watches the engine monitor and
reports on MonBus like the rest of the system (owner, 2026-11-25). Its
`axi_monitor_timer` is the local timer: a frequency-invariant tick from
`counter_freq_invariant`, so an interval set in ticks means the same time at
any clock, and a 32-bit count, which `TIME` reads. When the global usync
timer exists (rtl/amba/monitors TASK-005), every Ocelus monitor stamps from
it and `TIME` reads it too, so an engine's report and a MonBus packet about
the same event carry the same time. HIVE adds no timer of its own; the
periodic report (Chapter 4) is timed on `TIME`.

## Per-engine peripherals

**`traffic_counter`.** The counter bank behind the router tap:
`pkt_rx_count[4]`, `pkt_tx_count[4]`, `pkt_local_inject`,
`pkt_local_consume`, `buffer_overflow_count`, `stall_cycles` — 32-bit
wrapping, saturating-clear on read when `Reset Statistics Counters` is
issued. `buffer_occupancy[4]`, `congestion_flag`, and `error_flags` are
wired combinationally from the tap for low-latency trigger evaluation.

**`trigger_logic`.** Hardware threshold comparator running in parallel with
the core: flags `occupancy > cfg_threshold` (default 75% of buffer depth)
and error conditions immediately, so congestion detection meets the < 10
cycle target whatever the context is executing. The context polls the
flags (gatling has no interrupts) and decides the packet response;
`trigger_logic` never injects packets by itself (firmware owns all packet
content — policy in software, detection in hardware).

**`axis_injector`.** TX FIFO aperture (128-bit × 4 entries) plus the AXIS
master into the per-engine `mon_clk → delta_clk` CDC FIFO. Firmware writes
words, then commits with `TVALID`; the injector appends `tid` (its
`TILE_ID` parameter, the engine's ID), `tuser`, `tdest`, `tlast` per the
commit record.

**`ctrl_net_slave`.** Receives 32-bit control frames addressed to this
engine (HAS Chapter 4 command set), updates threshold/config registers,
holds a mailbox the context polls, and queues uplink status frames for the
control network's round-robin arbiter.

**`local_mem`** (from the SERV design) is not used: it is a 2 KB + 2 KB
memory on SERV's instruction and data buses, and `gatling_mem_bram` takes
its place. It stays in `rtl/engine_monitor/` until the monitor top lands.

## Interfaces

Per engine: router tap in (from the engine's router, `delta_clk` —
synchronized at the tap boundary inside `traffic_counter`; the tap is
observation-only), control-network slave port, AXIS TX into CDC. For the
block: the `gatling_mem_bram` AXI4-Lite loader port (from HIVE-C), the
observation port out.

## Open Items

- Tap synchronization (decided 2026-10-13): **dual-flop synchronizers** per
  direction at the tap boundary inside `traffic_counter`.
- Periodic-report time base (decided 2026-11-25): the Ocelus monitor's
  local timer, then the global usync timer, read through `TIME`.
- Engine identity (decided 2026-11-25): `MON_ID` as above; the Delta tile
  ID is the engine's identity.
- Which buses the Ocelus monitor taps. gatling's instruction and data ports
  are not AMBA; the four AXIS injectors (`axis_monitor_lite`) and the
  `gatling_mem_bram` AXI4-Lite loader (`axi_monitor_lite`) are.
- The peripheral window's base address (v0.2's `0xF000_0000` is a
  candidate) and its fit inside gatling's one-stage data latency.

---

**Last Updated:** 2026-11-25
