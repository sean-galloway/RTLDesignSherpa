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

# AXI Monitor Reporter — Performance Packets

**Module:** `axi_monitor_reporter_perf.sv`
**Location:** `rtl/amba/monitor/`
**Status:** Production Ready

---

## Overview

The `axi_monitor_reporter_perf` module is the performance-packet emitter for the AXI/AXIL monitor family. It is one of the per-packet-type sub-blocks that the top-level `axi_monitor_reporter` dispatches to. It owns two lifetime counters — completed transactions and error transactions — and a small cycle FSM that periodically publishes count-rollup packets of type `PktTypePerf` onto the monitor bus (MonBus).

This block was split out of the original monolithic reporter so integrators who do not need performance counters can drop it (compile it out with `ENABLE_PERF_LOGIC=0` at the reporter level) and reclaim the counter area.

Key features:

- Lifetime completion and error transaction counters (16-bit each)
- Counters driven from mark-reported masks supplied by the top reporter
- 5-state cycle FSM that paces packet publication
- Emits one packet at a time via a simple `pkt_valid` / `pkt_taken` handshake
- Backpressure aware: only advances when the output bus is free (`output_busy` low)
- Emits `AXI_PERF_COMPLETED_COUNT` and `AXI_PERF_ERROR_COUNT` event codes
- Counters exposed as ports for status / debug read-back

Performance analysis of an AXI interface needs a periodic summary of how many transactions have completed and how many ended in error over the life of the monitor. This block accumulates those two counts and, when the output path is idle, walks a fixed FSM that emits a completion-count packet followed by an error-count packet.

**Use cases:**

- Long-run throughput and error-rate characterization of an AXI/AXIL master or slave
- Coarse "health" telemetry streamed to a host over the MonBus
- Regression sanity: confirming the number of completions matches the stimulus
- Cross-checking the window-bucket perfmon path (Stage A/B) against a lifetime rollup

**Key benefit:** real area savings when disabled (the counters and FSM are removed), while providing a lightweight lifetime performance rollup that runs in parallel with the window-bucket perfmon counters in `axi_monitor_base`.

---

## Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| `MAX_TRANSACTIONS` | int | 16 | Number of transaction slots; sets the width of the `error_marked_mask` / `compl_marked_mask` inputs |

---

## Ports

### Clock and Reset

| Port | Direction | Width | Description |
|---|---|---|---|
| `aclk` | Input | 1 | Monitor clock |
| `aresetn` | Input | 1 | Active-low asynchronous reset |

### Control / Status Inputs

| Port | Direction | Width | Description |
|---|---|---|---|
| `cfg_perf_enable` | Input | 1 | Enable performance packet generation (also gates the FSM) |
| `output_busy` | Input | 1 | Output path busy (FIFO has data or `monbus_valid` asserted); FSM stalls while high |
| `pkt_taken` | Input | 1 | Strobed by the top reporter when this block's packet is accepted. **Load-bearing** — it holds the emit FSM; see Design Notes |
| `error_marked_mask` | Input | MAX_TRANSACTIONS | Per-slot bit set the cycle an error event is marked-reported into the FIFO |
| `compl_marked_mask` | Input | MAX_TRANSACTIONS | Per-slot bit set the cycle a completion event is marked-reported into the FIFO |

### Packet Output

| Port | Direction | Width | Description |
|---|---|---|---|
| `pkt_valid` | Output | 1 | A performance packet is available this cycle |
| `pkt_type` | Output | 4 | Packet type — constant `PktTypePerf` (4'h4) |
| `pkt_event_code` | Output | 8 | Event code: `AXI_PERF_COMPLETED_COUNT` (8'h7) or `AXI_PERF_ERROR_COUNT` (8'h8) |
| `pkt_channel` | Output | 9 | Channel field (unused here — driven to 0) |
| `pkt_data` | Output | 64 | Zero-extended count value being reported |

### Lifetime Counters (Status / Debug)

| Port | Direction | Width | Description |
|---|---|---|---|
| `perf_completed_count` | Output | 16 | Running total of completed transactions |
| `perf_error_count` | Output | 16 | Running total of error transactions |

---

## Functional Description

### Lifetime Counters

Two 16-bit registers, `r_completed_count` and `r_error_count`, accumulate over the life of the monitor. On every clock, the block scans the `error_marked_mask` and `compl_marked_mask` inputs across all `MAX_TRANSACTIONS` slots and increments the relevant counter for each asserted bit. Because the counters advance directly from the mark masks (not from `pkt_taken`), they track every event the top reporter accepted into its FIFO regardless of whether a rollup packet is emitted. Entries **auto-retired** because their packet class is disabled do NOT feed the mark masks, so these counters count packets actually emitted, not transactions observed. Timeout packets roll up into `r_error_count` (timeout slots sit in `TRANS_ERROR`).

Both counters are exposed on the port list for status read-back, and — since commit `95c9490a` — are plumbed through `axi_monitor_base` and `axi_monitor_filtered` to drive every `*_mon` wrapper's `error_count` / `transaction_count` status outputs (which read 0 when `ENABLE_PERF_LOGIC=0` or `USE_MONITOR=0`).

### Cycle FSM

A 5-state counter (`r_state`) paces packet publication and matches the original monolithic reporter's behavior one-for-one. The FSM only advances while `cfg_perf_enable` is asserted and `output_busy` is low:

| State | Name | Action |
|---|---|---|
| 3'h0 | ADDR_LATENCY | No packet (placeholder state) |
| 3'h1 | DATA_LATENCY | No packet (placeholder state) |
| 3'h2 | TOTAL_LATENCY | No packet (placeholder state) |
| 3'h3 | COMPLETED_COUNT | Assert `w_gen_completed` if `r_completed_count > 0` |
| 3'h4 | ERROR_COUNT | Assert `w_gen_errors` if `r_error_count > 0`, then wrap to 3'h0 |

The three latency states are placeholders retained for behavioral compatibility; they emit no packet. Only the completed-count and error-count states can produce output.

### Output Multiplexer

The output mux prioritizes the completion-count packet over the error-count packet. When `w_gen_completed` is set, `pkt_valid` asserts with event code `AXI_PERF_COMPLETED_COUNT` and `pkt_data` carrying the zero-extended completed count. Otherwise, when `w_gen_errors` is set, `pkt_valid` asserts with `AXI_PERF_ERROR_COUNT` and the error count. `pkt_type` is always `PktTypePerf` and `pkt_channel` is always 0.

### Handshake

The block presents one packet at a time. The top reporter samples `pkt_valid`, forwards the packet fields onto the MonBus, and strobes `pkt_taken` when the packet is accepted. Publication rate is naturally throttled by the FSM (which only steps when the output is not busy), so the emitter cannot flood the bus.

---

## Timing Characteristics

This module is **purely combinational** -- it contains no `always_ff` and no
latch, so it holds no state and adds no clock cycles. Its outputs settle a
propagation delay after its inputs, and it introduces no latency into a
pipeline that instantiates it.

Timing closure is therefore a question of the surrounding logic's slack, not of
this module's cycle count. No synthesis figures are quoted; none have been
measured.

---

## Usage Examples
This block is not instantiated directly by users; it is instantiated inside `axi_monitor_reporter`. The pattern is:

```systemverilog
axi_monitor_reporter_perf #(
    .MAX_TRANSACTIONS (MAX_TRANSACTIONS)
) u_reporter_perf (
    .aclk                 (aclk),
    .aresetn              (aresetn),

    .cfg_perf_enable      (cfg_perf_enable),
    .output_busy          (w_output_busy),      // FIFO data or monbus_valid
    .pkt_taken            (w_perf_pkt_taken),   // top reporter accepted our packet
    .error_marked_mask    (w_error_marked_mask),
    .compl_marked_mask    (w_compl_marked_mask),

    .pkt_valid            (w_perf_pkt_valid),
    .pkt_type             (w_perf_pkt_type),
    .pkt_event_code       (w_perf_pkt_event_code),
    .pkt_channel          (w_perf_pkt_channel),
    .pkt_data             (w_perf_pkt_data),

    .perf_completed_count (perf_completed_count),
    .perf_error_count     (perf_error_count)
);
```

---

## Design Notes

### Completion + Performance Packets: Bandwidth, and the Two Ways to Suppress

Enabling both completion packets (`cfg_compl_enable`) and performance packets (`cfg_perf_enable`) simultaneously can congest the monitor bus under heavy traffic (the reporter sustains at most one packet per two cycles). The usual split is a functional-debug config (error + completion + timeout) and a performance config (error + perf, completions suppressed). There are two suppression mechanisms with different semantics:

- **Runtime disable** (`cfg_compl_enable = 0` with `ENABLE_COMPL_LOGIC = 1`): the monitor is passive for that class. Since commit `95c9490a` this is **safe** — terminal entries of a disabled class auto-retire (are marked reported without emitting a packet and without bumping this block's counters), so the transaction table never leaks and `block_ready` never wedges. Before that commit this exact configuration leaked every completed entry and stalled the monitored bus after roughly `MAX_TRANSACTIONS` transactions. See the auto-retire section in [axi_monitor_reporter](axi_monitor_reporter.md).
- **Packet-type drop mask** (`cfg_axi_pkt_mask` in [axi_monitor_filtered](axi_monitor_filtered.md)): completions are still detected, marked, and **counted** (this block's `perf_completed_count` keeps advancing, and the wrapper's `transaction_count` output stays live); only the emission is dropped downstream of the reporter. Use this when you want the lifetime counters while suppressing the packet stream.

See `docs/user-guides/AXI_Monitor_Configuration_Guide.md`.

### `pkt_taken` Holds the Emit FSM — Do Not Tie It Off

`pkt_taken` does not gate the *counters* (those update from the mark masks
unconditionally), but it **does** gate the FSM state register:

```systemverilog
// Hold the state whenever we are presenting a packet that was not
// accepted (threshold beats perf in the top reporter's output mux).
// Advancing regardless silently dropped the packet.
if (!(pkt_valid && !pkt_taken)) begin
    r_state <= w_next_state;
end
```

The hold exists because threshold outranks perf in the top reporter's output
mux: without it, a perf packet that lost that arbitration was generated, never
emitted, and the FSM walked past it.

So the port must be driven correctly. Tie it **low** and the FSM deadlocks the
first time it presents a packet — the state holds forever. Tie it **high** and
the silently-dropped-packet bug returns.

(The "retained for a future hook, tied to an `unused` net" pattern this section
used to describe belongs to `axi_monitor_reporter_debug`, a different module,
whose own page documents it correctly.)

### Relationship to the Window-Bucket Perfmon

This block emits the legacy `PktTypePerf` count-rollup packets that summarize completion/error counts over the monitor's lifetime. It runs in parallel with the Stage A/B window-bucket perfmon counters in `axi_monitor_base`. Those buckets are **readable as counters only** — nothing packetizes them onto the MonBus yet, so no `PktTypePerfWin` / `PktTypePerfHist` packets are emitted by any module today. The two mechanisms are complementary, not redundant.

### Counter Wrap

Both counters are 16-bit and wrap on overflow. For very long runs the host should account for wrap or read the counters periodically via the status ports.

---

## Related Modules

**Used by:**

- **axi_monitor_reporter.sv** — instantiates this block as its performance-packet sub-emitter
- **axi_monitor_base.sv** — top-level monitor scaffold that wires the reporter into the MonBus

**Uses:**

- **monitor_common_pkg** — `PktTypePerf` and shared packet definitions
- **monitor_amba4_pkg** — `AXI_PERF_COMPLETED_COUNT` / `AXI_PERF_ERROR_COUNT` event codes
- **reset_defs.svh** — reset macros (`ALWAYS_FF_RST`, `RST_ASSERTED`)

**See also:**

- **axi_monitor_reporter_threshold.sv** — threshold-crossing packet emitter (sibling)
- **axi_monitor_reporter_timeout.sv** — timeout packet emitter (sibling)

---

## Testing

**No dedicated testbench for this module.** It has no
`val/**/test_axi_monitor_reporter_perf.py`. It is exercised indirectly, through the tests of
modules that instantiate it (directly or further up):

- `axi4_master_rd_mon` -- `val/**/test_axi4_master_rd_mon.py`
- `axi4_master_wr_mon` -- `val/**/test_axi4_master_wr_mon.py`
- `axi4_slave_rd_mon` -- `val/**/test_axi4_slave_rd_mon.py`
- `axi4_slave_wr_mon` -- `val/**/test_axi4_slave_wr_mon.py`
- `axi5_master_rd_mon` -- `val/**/test_axi5_master_rd_mon.py`

Indirect coverage exercises this module only in the configurations those
parents elaborate. A parameter or mode no parent uses is untested.

Treat any behaviour described on this page as unverified by simulation.

---

## References

### Source Code
- RTL: `rtl/amba/monitor/axi_monitor_reporter_perf.sv`
- Parent: `rtl/amba/monitor/axi_monitor_reporter.sv`
- Packages: `rtl/amba/includes/monitor_common_pkg.sv`, `rtl/amba/includes/monitor_amba4_pkg.sv`

### Documentation
- Architecture: `docs/markdown/rtl-amba/shared/README.md`
- Monitor Base: `docs/markdown/rtl-amba/monitor/axi_monitor_base.md`
- Configuration: `docs/user-guides/AXI_Monitor_Configuration_Guide.md`
- Packet Format: `docs/markdown/rtl-amba/includes/monitor_package_spec.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- **[Back to Shared Infrastructure Index](../_book_monitor_index.md)**
- **[Back to rtl-amba Index](../index.md)**
