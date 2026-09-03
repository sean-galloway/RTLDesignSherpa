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

# 5.2 Debug Guide

## Overview

Start here when a converter misbehaves. Each entry runs symptoms, probe points, then fix — the order you want them in at the bench.

## Testing

### 5.2.1 Common Issues

#### Width Converter Issues

##### Issue: Data Corruption

**Symptoms:**
- Output data doesn't match expected
- Random bits flipped or missing

**Debug Steps:**
1. Check width ratio calculation: `RATIO = WIDE_WIDTH / NARROW_WIDTH`
2. Verify beat counter is correct: `$clog2(RATIO)` bits
3. Check data packing/unpacking slice indices
4. Verify sideband mode matches use case

**Waveform Checkpoints:**
```
r_beat_ptr             - slot/slice pointer, cycles 0 to RATIO-1
r_data_accumulator     - (upsize) each slot fills as narrow beats land
r_data_buffer          - (dnsize) captured wide beat being sliced
narrow_/wide_ data     - compare input/output patterns
```

##### Issue: LAST Signal Incorrect

**Symptoms:**
- Transaction ends early or late
- Master receives wrong beat count

**Debug Steps:**
1. Check TRACK_BURSTS parameter (axi_data_dnsize); there is no USE_LAST
2. Verify burst tracker logic if enabled
3. Check s_last input timing

**Solution:**
```systemverilog
// LAST is the buffered last flag AND the final beat -- from the RTL:
//   upsize:  wide_last   = r_last_buffered && r_wide_valid;
//   dnsize:  narrow_last = r_wide_buffered && r_last_buffered
//                          && w_last_narrow_beat;
// An OR of (final beat, saw-last) asserts LAST at the end of EVERY
// group and truncates any burst spanning more than one wide beat.
```

##### Issue: Throughput Lower Than Expected

**Symptoms:**
- Gaps between output beats
- Single-buffer stalling between wide beats (it should replace during the last narrow beat)

**Debug Steps:**
1. Check downstream ready signal behavior
2. Look for backpressure stalls

#### Protocol Converter Issues

##### Issue: Burst Decomposition Incorrect

**Symptoms:**
- Wrong number of single transactions
- Address increment wrong

**Debug Steps:**
1. Check burst type (FIXED, INCR, WRAP)
2. Verify size calculation
3. Check address increment logic

**Waveform Checkpoints:**
```
r_ar_addr / r_aw_addr - walk by (1 << size) per issued beat
r_ar_beat_count / r_aw_beat_count - count to arlen/awlen
m_axil_arvalid  - asserts for each decomposed beat
```

##### Issue: Response Aggregation Wrong

**Symptoms:**
- Wrong BRESP/RRESP value
- Error not propagated correctly

**Debug Steps:**
1. Check worst-case response tracking
2. Verify response counter
3. Check RLAST generation

**Solution:**
```systemverilog
// Accumulate per beat...
always_ff @(posedge aclk or negedge aresetn) begin
    ...
    else if (m_axil_rvalid && m_axil_rready)
        if (m_axil_rresp > r_r_resp_accum)
            r_r_resp_accum <= m_axil_rresp;
end

// ...and ALWAYS fold the live beat in at emission. The accumulator
// alone is the shipped bug (see 4.3.3): it does not yet contain the
// final beat's own response, so a single-beat error reports OKAY.
assign w_r_resp_worst = (m_axil_rresp > r_r_resp_accum) ? m_axil_rresp
                                                        : r_r_resp_accum;
assign s_axi_rresp = (r_r_beat_count == r_r_len) ? w_r_resp_worst
                                                 : m_axil_rresp;
```

### 5.2.2 Debug Signals

#### Recommended Internal Signals

For width converters:
```systemverilog
// Add debug outputs
output logic [$clog2(RATIO)-1:0] dbg_beat_count,
output logic                     dbg_buffer_valid,
output logic [1:0]               dbg_state
```

For protocol converters:
```systemverilog
// Add debug outputs
output logic [7:0]  dbg_remaining_beats,
output logic [2:0]  dbg_state,
output logic [1:0]  dbg_worst_resp,
output logic        dbg_in_burst
```

#### ILA Configuration

```tcl
# Create ILA for converter debug
create_debug_core u_ila ila

# Add probes
set_property probe_count 10 [get_debug_cores u_ila]
connect_debug_port u_ila/clk [get_nets aclk]

# Key signals
connect_debug_port u_ila/probe0 [get_nets r_beat_ptr]
connect_debug_port u_ila/probe1 [get_nets r_ar_beat_count]
connect_debug_port u_ila/probe2 [get_nets s_axi_arvalid]
connect_debug_port u_ila/probe3 [get_nets m_axil_arvalid]
```

### 5.2.3 Simulation Debug

#### Waveform Analysis

**Key Signal Groups** (real port names — the width primitives are
named by WIDTH, not direction: `narrow_*` is the INPUT of the upsize
but the OUTPUT of the dnsize):

1. **Narrow side:**
   - narrow_valid, narrow_ready, narrow_data, narrow_sideband,
     narrow_last (upsize input / dnsize output)

2. **Wide side:**
   - wide_valid, wide_ready, wide_data, wide_sideband, wide_last
     (upsize output / dnsize input)

3. **Control:**
   - r_beat_ptr, r_slave_beat_count, r_burst_active (tracked mode),
     start_lane, burst_len/burst_start (dnsize tracked mode)

4. **Sideband contents:**
   - WSTRB rides narrow_/wide_sideband on the write path
   - RRESP rides narrow_/wide_sideband on the read path

#### Timing Diagram Template

```
            ___     ___     ___     ___     ___
clk     ___|   |___|   |___|   |___|   |___|   |
            _______________________________
s_valid ___/                               \___
           [D0 ][D1 ][D2 ][D3 ][D4 ][D5 ][D6 ][D7 ]
s_data
        ___________________________________________
s_ready

           ________________________________
m_valid __|                                |___
                                   [WIDE_DATA ]
m_data

Check:
1. s_ready stays high during accumulation
2. m_valid asserts after RATIO beats
3. Data packing is correct
```

### 5.2.4 Common Mistakes

#### Mistake 1: Wrong Width Ratio

```systemverilog
// WRONG: Manual ratio
localparam RATIO = 8;  // May not match actual widths

// CORRECT: Calculated ratio
localparam RATIO = WIDE_WIDTH / NARROW_WIDTH;
```

#### Mistake 2: Missing Sideband Handling

```systemverilog
// WRONG: Forgetting sideband
assign m_data = r_data;
// Missing: assign m_wstrb = ...

// CORRECT: Handle both
assign m_data = r_data;
assign m_wstrb = r_sideband;
```

#### Mistake 3: Incorrect LAST Timing

```systemverilog
// WRONG: LAST on wrong beat
assign narrow_last = (r_beat_ptr == 0);  // First slice!

// CORRECT: LAST on final beat
// AND of final-beat with the buffered last flag (see 5.2.1); the OR
// form truncates multi-wide-beat bursts
assign narrow_last = r_wide_buffered && r_last_buffered && w_last_narrow_beat;
```

#### Mistake 4: Burst Length Calculation Error

```systemverilog
// WRONG: Off-by-one
assign m_awlen = s_awlen / RATIO;  // Wrong!

// CORRECT: Account for LEN encoding
assign m_axi_awlen = ((int_awlen + 8'(WIDTH_RATIO)) / 8'(WIDTH_RATIO)) - 8'd1;  // round UP
```

### 5.2.5 Verification Checklist

Before signoff, verify:

- [ ] All parameter combinations tested
- [ ] Single-beat transactions work
- [ ] Multi-beat bursts work (INCR, WRAP, FIXED)
- [ ] Backpressure handling correct
- [ ] Error propagation correct
- [ ] LAST signal timing correct
- [ ] Sideband signals handled correctly
- [ ] Reset behavior verified
- [ ] Coverage targets met

### 5.2.6 Performance Validation

#### Throughput Measurement

```python
async def measure_throughput(tb, transaction_count=1000):
    start_time = get_sim_time()

    for _ in range(transaction_count):
        await tb.send_transaction()

    end_time = get_sim_time()
    elapsed_cycles = (end_time - start_time) / clock_period

    throughput = transaction_count / elapsed_cycles
    print(f"Throughput: {throughput:.2f} transactions/cycle")

    return throughput
```

#### Expected Throughput

| Module | Mode | Expected |
| --- | --- | --- |
| axi_data_upsize | Single | 1.0 trans/cycle |
| axi_data_dnsize | Single | 0.992 narrow beats/cycle (measured) |
| axi4_to_axil4 | Single-beat | ~1/(2+slave latency) trans/cycle (one-outstanding guard) |
| axi4_to_axil4 | Burst | ~N/(N+2) beats/cycle vs a pipelining slave (N issue cycles + one response latency, see 4.2.4); whole bursts serialize on the one-outstanding guard |

: Table 5.5: Expected Throughput

## Navigation

**End of Micro-Architecture Specification**
