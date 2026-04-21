<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> &middot; <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# CDC 2-Phase Handshake

**Module:** `cdc_2_phase_handshake.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready
**Companion:** `cdc_4_phase_handshake.sv` (level-based, classic variant)

---

## Overview

Two-phase (toggle / NRZ) CDC handshake with data transfer. Provides the same valid/ready interface as the 4-phase variant but uses toggle-based signaling to halve the control-path round trip -- two synchronizer crossings per transfer instead of four.

The "event" is a TRANSITION of the request/acknowledge signals rather than a level. The source toggles its request bit on each new transfer; the destination detects the toggle edge and responds by toggling its acknowledge bit.

### Key Features

- Drop-in replacement for `cdc_4_phase_handshake` (same port interface)
- Faster: 2 synchronizer crossings per transfer (vs 4 for level-based)
- Toggle-based request/acknowledge (NRZ encoding)
- Parameterizable synchronizer depth (2-3 stages)
- Optional timeout detection for stall diagnosis
- ASYNC_REG attributes for Xilinx/Intel FPGA flows
- SDC constraint guidance in RTL comments

### 2-Phase vs 4-Phase Comparison

| Aspect | 2-Phase (this module) | 4-Phase |
|--------|----------------------|---------|
| **Crossings per transfer** | 2 (req toggle + ack toggle) | 4 (req + ack + req clear + ack clear) |
| **Latency** | ~5-6 destination clocks | ~7-8 destination clocks |
| **Throughput** | Higher (shorter round-trip) | Lower |
| **Complexity** | Edge detection required | Simpler level-based logic |
| **Reset behavior** | Toggle state preserved across reset recovery | Clean level-based reset |

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| DATA_WIDTH | int | 8 | Width of the data bus (1+) |
| SYNC_STAGES | int | 3 | Synchronizer depth for req/ack (2 or 3) |
| TIMEOUT_CYCLES | int | 0 | 0 = disabled; >0 asserts src_timeout after stall |

---

## Port Groups

### Source Clock Domain Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| clk_src | input | 1 | Source domain clock |
| rst_src_n | input | 1 | Source domain active-low async reset |
| src_valid | input | 1 | Source indicates data valid |
| src_ready | output | 1 | Handshake ready (asserted when idle) |
| src_data | input | DATA_WIDTH | Data from source domain |
| src_timeout | output | 1 | Stall timeout (when TIMEOUT_CYCLES > 0) |

### Destination Clock Domain Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| clk_dst | input | 1 | Destination domain clock |
| rst_dst_n | input | 1 | Destination domain active-low async reset |
| dst_valid | output | 1 | Data valid to receiver |
| dst_ready | input | 1 | Receiver ready |
| dst_data | output | DATA_WIDTH | Data transferred to destination domain |

---

## Theory of Operation

### Source Domain FSM

```
S_IDLE      src_ready=1. On src_valid: latch data, toggle r_req_tog,
            drop src_ready, go to S_WAIT_ACK.

S_WAIT_ACK  Wait for ack edge (w_ack_event). On edge: src_ready=1,
            return to S_IDLE.
```

### Destination Domain FSM

```
D_IDLE       Wait for req edge (w_req_event). On edge: copy data into
             r_dst_data, raise dst_valid, go to D_WAIT_READY.

D_WAIT_READY Hold dst_valid. On dst_ready: drop dst_valid, toggle
             r_ack_tog, return to D_IDLE.
```

### Edge Detection

```systemverilog
event = current_sync_output ^ previous_sync_output
```

The edge detector uses one additional flop per direction to compare the current synchronized toggle value with the previous cycle's value. A difference indicates a new transfer event.

---

## Usage Example

```systemverilog
cdc_2_phase_handshake #(
    .DATA_WIDTH     (64),
    .SYNC_STAGES    (3),
    .TIMEOUT_CYCLES (1000)
) u_packet_cdc (
    // Source: Monitor clock domain
    .clk_src     (mon_clk),
    .rst_src_n   (mon_rst_n),
    .src_valid   (mon_pkt_valid),
    .src_ready   (mon_pkt_ready),
    .src_data    (mon_pkt_data),
    .src_timeout (mon_timeout),

    // Destination: System clock domain
    .clk_dst     (sys_clk),
    .rst_dst_n   (sys_rst_n),
    .dst_valid   (sys_pkt_valid),
    .dst_ready   (sys_pkt_ready),
    .dst_data    (sys_pkt_data)
);
```

### Swapping with 4-Phase

The two handshake modules are drop-in interchangeable:

```systemverilog
// Change only the module name -- ports are identical
cdc_4_phase_handshake #(  // or cdc_2_phase_handshake
    .DATA_WIDTH     (64),
    .SYNC_STAGES    (3),
    .TIMEOUT_CYCLES (0)
) u_cdc ( ... );
```

---

## Required SDC Constraints

```tcl
# 1. Req / Ack single-bit toggle crossings
set_max_delay -datapath_only \
    -from [get_pins u_cdc/r_req_tog_reg/C] \
    -to   [get_pins u_cdc/r_req_sync_reg[0]/D] \
    <dst_period_ns>

set_max_delay -datapath_only \
    -from [get_pins u_cdc/r_ack_tog_reg/C] \
    -to   [get_pins u_cdc/r_ack_sync_reg[0]/D] \
    <src_period_ns>

# 2. Data bus (quasi-static, protected by toggle handshake)
set_max_delay -datapath_only \
    -from [get_pins u_cdc/r_src_data_hold_reg[*]/C] \
    -to   [get_pins u_cdc/r_dst_data_reg[*]/D] \
    <dst_period_ns>
```

Do NOT use `set_false_path` -- the data bus relies on a bounded crossing window for correctness.

---

## Related Modules

| Module | Purpose |
|--------|---------|
| `cdc_4_phase_handshake.sv` | Level-based variant (slower, simpler) |
| `cdc_synchronizer.sv` | Multi-bit sync (no handshake, quasi-static only) |
| `sync_pulse.sv` | Single-cycle pulse crossing (no data) |
| `fifo_async.sv` | Streaming data crossing (Gray-coded pointers) |
| `apb_slave_cdc.sv` | APB protocol CDC (uses either handshake variant) |

---

## Resources

- RTL: `rtl/amba/shared/cdc_2_phase_handshake.sv`
- Tests: `val/amba/test_cdc_2_phase_handshake.py`
- Formal: `formal/amba/cdc_handshake/`

---

**Last Updated:** 2026-04-21

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../index.md)
