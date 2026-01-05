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

This section provides debugging guidance for converter module issues.

## 5.2.1 Common Issues

### Width Converter Issues

#### Issue: Data Corruption

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
r_count         - Should cycle 0 to RATIO-1
r_data          - Check each slice is populated
s_data/m_data   - Compare input/output patterns
```

#### Issue: LAST Signal Incorrect

**Symptoms:**
- Transaction ends early or late
- Master receives wrong beat count

**Debug Steps:**
1. Check USE_LAST parameter
2. Verify burst tracker logic if enabled
3. Check s_last input timing

**Solution:**
```systemverilog
// Verify LAST generation
assign m_last = (r_count == RATIO - 1) || r_input_last_seen;
```

#### Issue: Throughput Lower Than Expected

**Symptoms:**
- Gaps between output beats
- Single-buffer achieving <80%

**Debug Steps:**
1. Check downstream ready signal behavior
2. Verify DUAL_BUFFER parameter for downsize
3. Look for backpressure stalls

### Protocol Converter Issues

#### Issue: Burst Decomposition Incorrect

**Symptoms:**
- Wrong number of single transactions
- Address increment wrong

**Debug Steps:**
1. Check burst type (FIXED, INCR, WRAP)
2. Verify size calculation
3. Check address increment logic

**Waveform Checkpoints:**
```
r_current_addr  - Should increment by (1 << size)
r_beat_count    - Should count to s_arlen/s_awlen
m_arvalid       - Should assert for each decomposed beat
```

#### Issue: Response Aggregation Wrong

**Symptoms:**
- Wrong BRESP/RRESP value
- Error not propagated correctly

**Debug Steps:**
1. Check worst-case response tracking
2. Verify response counter
3. Check RLAST generation

**Solution:**
```systemverilog
// Proper error aggregation
always_ff @(posedge clk) begin
    if (new_burst)
        r_worst_resp <= 2'b00;
    else if (m_rvalid && m_rready)
        r_worst_resp <= (m_rresp > r_worst_resp) ? m_rresp : r_worst_resp;
end
```

## 5.2.2 Debug Signals

### Recommended Internal Signals

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

### ILA Configuration

```tcl
# Create ILA for converter debug
create_debug_core u_ila ila

# Add probes
set_property probe_count 10 [get_debug_cores u_ila]
connect_debug_port u_ila/clk [get_nets aclk]

# Key signals
connect_debug_port u_ila/probe0 [get_nets r_state]
connect_debug_port u_ila/probe1 [get_nets r_beat_count]
connect_debug_port u_ila/probe2 [get_nets s_arvalid]
connect_debug_port u_ila/probe3 [get_nets m_arvalid]
```

## 5.2.3 Simulation Debug

### Waveform Analysis

**Key Signal Groups:**

1. **Input Channel:**
   - s_valid, s_ready, s_data, s_last

2. **Output Channel:**
   - m_valid, m_ready, m_data, m_last

3. **Control:**
   - r_state, r_count, r_burst_remaining

4. **Sideband:**
   - s_wstrb/m_wstrb (write path)
   - s_rresp/m_rresp (read path)

### Timing Diagram Template

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

## 5.2.4 Common Mistakes

### Mistake 1: Wrong Width Ratio

```systemverilog
// WRONG: Manual ratio
localparam RATIO = 8;  // May not match actual widths

// CORRECT: Calculated ratio
localparam RATIO = WIDE_WIDTH / NARROW_WIDTH;
```

### Mistake 2: Missing Sideband Handling

```systemverilog
// WRONG: Forgetting sideband
assign m_data = r_data;
// Missing: assign m_wstrb = ...

// CORRECT: Handle both
assign m_data = r_data;
assign m_wstrb = r_sideband;
```

### Mistake 3: Incorrect LAST Timing

```systemverilog
// WRONG: LAST on wrong beat
assign m_last = r_count == 0;  // First beat!

// CORRECT: LAST on final beat
assign m_last = (r_count == RATIO - 1) || r_early_last;
```

### Mistake 4: Burst Length Calculation Error

```systemverilog
// WRONG: Off-by-one
assign m_awlen = s_awlen / RATIO;  // Wrong!

// CORRECT: Account for LEN encoding
assign m_awlen = ((s_awlen + 1) >> RATIO_LOG2) - 1;
```

## 5.2.5 Verification Checklist

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

## 5.2.6 Performance Validation

### Throughput Measurement

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

### Expected Throughput

| Module | Mode | Expected |
|--------|------|----------|
| axi_data_upsize | Single | 1.0 trans/cycle |
| axi_data_dnsize | Single | 0.8 trans/cycle |
| axi_data_dnsize | Dual | 1.0 trans/cycle |
| axi4_to_axil4 | Single-beat | 1.0 trans/cycle |
| axi4_to_axil4 | Burst | 0.5 trans/cycle |

: Table 5.5: Expected Throughput

---

**End of Micro-Architecture Specification**
