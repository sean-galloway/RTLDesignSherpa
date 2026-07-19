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
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The `axi_monitor_reporter_perf` module is the performance-packet emitter for the AXI/AXIL monitor family. It is one of the per-packet-type sub-blocks that the top-level `axi_monitor_reporter` dispatches to. It owns two lifetime counters — completed transactions and error transactions — and a small cycle FSM that periodically publishes count-rollup packets of type `PktTypePerf` onto the monitor bus (MonBus).

This block was split out of the original monolithic reporter so integrators who do not need performance counters can drop it (compile it out with `ENABLE_PERF_LOGIC=0` at the reporter level) and reclaim the counter area.

### Key Features

- Lifetime completion and error transaction counters (16-bit each)
- Counters driven from mark-reported masks supplied by the top reporter
- 5-state cycle FSM that paces packet publication
- Emits one packet at a time via a simple `pkt_valid` / `pkt_taken` handshake
- Backpressure aware: only advances when the output bus is free (`output_busy` low)
- Emits `AXI_PERF_COMPLETED_COUNT` and `AXI_PERF_ERROR_COUNT` event codes
- Counters exposed as ports for status / debug read-back

---

## Module Purpose

Performance analysis of an AXI interface needs a periodic summary of how many transactions have completed and how many ended in error over the life of the monitor. This block accumulates those two counts and, when the output path is idle, walks a fixed FSM that emits a completion-count packet followed by an error-count packet.

**Use Cases:**
- Long-run throughput and error-rate characterization of an AXI/AXIL master or slave
- Coarse "health" telemetry streamed to a host over the MonBus
- Regression sanity: confirming the number of completions matches the stimulus
- Cross-checking the window-bucket perfmon path (Stage A/B) against a lifetime rollup

**Key Benefit:** Real area savings when disabled (the counters and FSM are removed), while providing a lightweight lifetime performance rollup that runs in parallel with the window-bucket perfmon counters in `axi_monitor_base`.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `MAX_TRANSACTIONS` | int | 16 | Number of transaction slots; sets the width of the `error_marked_mask` / `compl_marked_mask` inputs |

---

## Port Groups

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `aclk` | input | 1 | Monitor clock |
| `aresetn` | input | 1 | Active-low asynchronous reset |

### Control / Status Inputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_perf_enable` | input | 1 | Enable performance packet generation (also gates the FSM) |
| `output_busy` | input | 1 | Output path busy (FIFO has data or `monbus_valid` asserted); FSM stalls while high |
| `pkt_taken` | input | 1 | Strobed by the top reporter when this block's packet is accepted (currently observational — see Design Notes) |
| `error_marked_mask` | input | MAX_TRANSACTIONS | Per-slot bit set the cycle an error event is marked-reported into the FIFO |
| `compl_marked_mask` | input | MAX_TRANSACTIONS | Per-slot bit set the cycle a completion event is marked-reported into the FIFO |

### Packet Output

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `pkt_valid` | output | 1 | A performance packet is available this cycle |
| `pkt_type` | output | 4 | Packet type — constant `PktTypePerf` (4'h4) |
| `pkt_event_code` | output | 8 | Event code: `AXI_PERF_COMPLETED_COUNT` (8'h7) or `AXI_PERF_ERROR_COUNT` (8'h8) |
| `pkt_channel` | output | 9 | Channel field (unused here — driven to 0) |
| `pkt_data` | output | 64 | Zero-extended count value being reported |

### Lifetime Counters (Status / Debug)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `perf_completed_count` | output | 16 | Running total of completed transactions |
| `perf_error_count` | output | 16 | Running total of error transactions |

---

## Functional Description

### Lifetime Counters

Two 16-bit registers, `r_completed_count` and `r_error_count`, accumulate over the life of the monitor. On every clock, the block scans the `error_marked_mask` and `compl_marked_mask` inputs across all `MAX_TRANSACTIONS` slots and increments the relevant counter for each asserted bit. Because the counters advance directly from the mark masks (not from `pkt_taken`), they track every event the top reporter accepted regardless of whether a rollup packet is emitted. Both counters are exposed on the port list for status read-back.

### Cycle FSM

A 5-state counter (`r_state`) paces packet publication and matches the original monolithic reporter's behavior one-for-one. The FSM only advances while `cfg_perf_enable` is asserted and `output_busy` is low:

| State | Name | Action |
|-------|------|--------|
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

## Usage Example

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

### Never Enable Completion + Performance Packets Together

This is the single most important integration caveat for the monitor family. Enabling both completion packets (`cfg_compl_enable`) and performance packets (`cfg_perf_enable`) simultaneously overwhelms the monitor bus and causes packet congestion. Use separate monitor configurations: a functional-debug config (error + completion + timeout) and a performance config (error + perf, with completions disabled). See `docs/AXI_Monitor_Configuration_Guide.md`.

### `pkt_taken` Is Currently Observational

`pkt_taken` is on the port list but does not gate the counters today — they update from the mark masks unconditionally. The port is retained for future hooks such as back-pressure on packet bursts. The RTL ties it to an `unused` net to keep lint clean.

### Relationship to the Window-Bucket Perfmon

This block emits the legacy `PktTypePerf` count-rollup packets that summarize completion/error counts over the monitor's lifetime. It runs in parallel with the Stage A/B window-bucket perfmon counters in `axi_monitor_base`, which emit `PktTypePerfWin` / `PktTypePerfHist` window-aggregate packets. The two mechanisms are complementary, not redundant.

### Counter Wrap

Both counters are 16-bit and wrap on overflow. For very long runs the host should account for wrap or read the counters periodically via the status ports.

---

## Related Modules

### Used By
- **axi_monitor_reporter.sv** — instantiates this block as its performance-packet sub-emitter
- **axi_monitor_base.sv** — top-level monitor scaffold that wires the reporter into the MonBus

### Uses
- **monitor_common_pkg** — `PktTypePerf` and shared packet definitions
- **monitor_amba4_pkg** — `AXI_PERF_COMPLETED_COUNT` / `AXI_PERF_ERROR_COUNT` event codes
- **reset_defs.svh** — reset macros (`ALWAYS_FF_RST`, `RST_ASSERTED`)

### See Also
- **axi_monitor_reporter_threshold.sv** — threshold-crossing packet emitter (sibling)
- **axi_monitor_reporter_timeout.sv** — timeout packet emitter (sibling)

---

## References

### Source Code
- RTL: `rtl/amba/monitor/axi_monitor_reporter_perf.sv`
- Parent: `rtl/amba/monitor/axi_monitor_reporter.sv`
- Packages: `rtl/amba/includes/monitor_common_pkg.sv`, `rtl/amba/includes/monitor_amba4_pkg.sv`

### Documentation
- Architecture: `docs/markdown/RTLAmba/shared/README.md`
- Monitor Base: `docs/markdown/RTLAmba/axi_monitor_base.md`
- Configuration: `docs/AXI_Monitor_Configuration_Guide.md`
- Packet Format: `docs/markdown/RTLAmba/includes/monitor_package_spec.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../index.md)
