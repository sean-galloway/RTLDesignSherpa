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

# Debug Guide

## Overview

This guide provides debugging strategies for Bridge verification failures. Common issues and their resolution approaches are documented.

## Debug Signal Access

### Enabling Debug Outputs

```python
# Enable debug signals in test
@cocotb.test()
async def test_with_debug(dut):
    # Access debug signals
    grant_s0 = dut.dbg_aw_grant_s0.value
    outstanding_m0 = dut.dbg_outstanding_m0.value
    state_s0 = dut.dbg_aw_state_s0.value
```

### Debug Signal Categories

| Category | Signals | Purpose |
|----------|---------|---------|
| Arbitration | `dbg_*_grant_s*` | Grant state per slave |
| Outstanding | `dbg_outstanding_m*` | Transaction depth per master |
| State | `dbg_*_state_s*` | FSM states per channel |
| ID Tracking | `dbg_id_table_*` | CAM contents |

: Table 7.3: Debug Signal Categories

## Common Issues

### Issue: Transaction Timeout

**Symptoms:**
- Test hangs waiting for response
- `TimeoutError` after configured timeout

**Debug Steps:**

```python
# 1. Check if request was accepted
await RisingEdge(dut.aclk)
print(f"AWVALID: {dut.m0_axi_awvalid.value}")
print(f"AWREADY: {dut.m0_axi_awready.value}")

# 2. Check arbitration state
print(f"AW Grant S0: {dut.dbg_aw_grant_s0.value}")

# 3. Check outstanding count
print(f"Outstanding M0: {dut.dbg_outstanding_m0.value}")

# 4. Check slave response
print(f"BVALID: {dut.s0_axi_bvalid.value}")
print(f"BREADY: {dut.s0_axi_bready.value}")
```

**Common Causes:**
- Arbiter locked by another master
- Outstanding limit reached
- Slave not responding
- ID table full

### Issue: Wrong Response Routing

**Symptoms:**
- Response arrives at wrong master
- BID mismatch errors

**Debug Steps:**

```python
# Check ID extension
print(f"Outgoing AWID: {dut.xbar_m0_awid.value}")
print(f"Slave received ID: {dut.s0_axi_awid.value}")

# Check response ID
print(f"Slave BID: {dut.s0_axi_bid.value}")
print(f"Routed to master: {dut.dbg_resp_master.value}")
```

**Common Causes:**
- ID extension incorrect
- CAM lookup failure
- ID width mismatch

### Issue: Data Corruption

**Symptoms:**
- Read data doesn't match written data
- WSTRB/data alignment issues

**Debug Steps:**

```python
# Check width conversion
print(f"Master data width: {dut.M0_DATA_WIDTH.value}")
print(f"Slave data width: {dut.S0_DATA_WIDTH.value}")

# Check strobe packing
print(f"Master WSTRB: {dut.m0_axi_wstrb.value}")
print(f"Slave WSTRB: {dut.s0_axi_wstrb.value}")

# Check address alignment
print(f"AWADDR: {dut.m0_axi_awaddr.value}")
print(f"AWSIZE: {dut.m0_axi_awsize.value}")
```

**Common Causes:**
- Width converter byte lane error
- Unaligned access handling
- Burst boundary crossing

## Waveform Analysis

### Generating Waveforms

```bash
# Enable VCD dump
WAVES=1 pytest test_bridge_2x2.py::test_basic -v

# View with GTKWave
gtkwave sim_build/dump.vcd
```

### Key Signals to Observe

```
Waveform Signal Groups:
├── Clock/Reset
│   └── aclk, aresetn
├── Master 0 AW Channel
│   └── m0_axi_awvalid, m0_axi_awready, m0_axi_awaddr, m0_axi_awid
├── Slave 0 AW Channel
│   └── s0_axi_awvalid, s0_axi_awready, s0_axi_awaddr, s0_axi_awid
├── Arbitration
│   └── dbg_aw_grant_s0, dbg_ar_grant_s0
└── Response
    └── s0_axi_bvalid, m0_axi_bvalid, dbg_resp_master
```

### Timing Analysis

```
Expected Transaction Timing:
     ┌───┐   ┌───┐   ┌───┐   ┌───┐   ┌───┐
aclk ┘   └───┘   └───┘   └───┘   └───┘   └───

     ┌───────────────────┐
awv  ┘                   └───────────────────

             ┌───────────┐
awr  ────────┘           └───────────────────

                         ┌───────────────────
wval ────────────────────┘

Time:  0     1     2     3     4     5
```

## Assertion Failures

### Built-in Assertions

```systemverilog
// Protocol assertions in generated RTL
assert property (@(posedge aclk) disable iff (!aresetn)
    s_awvalid && !s_awready |=> s_awvalid
) else $error("AW handshake violation");

assert property (@(posedge aclk) disable iff (!aresetn)
    s_wvalid && s_wlast |-> s_awid == r_current_awid
) else $error("W data ID mismatch");
```

### Handling Assertion Failures

1. **Locate assertion in RTL** - Search for error message
2. **Check signal history** - Review 10-20 cycles before failure
3. **Identify root cause** - Usually protocol or timing issue
4. **Fix test or RTL** - Depending on where bug exists

## Performance Debugging

### Throughput Issues

```python
# Measure transaction throughput
start_time = cocotb.utils.get_sim_time('ns')

for i in range(100):
    await master.write(addr=0x1000 + i*4, data=[i])

end_time = cocotb.utils.get_sim_time('ns')
throughput = 100 / (end_time - start_time) * 1e9  # tx/sec
print(f"Throughput: {throughput:.2f} transactions/sec")
```

### Latency Issues

```python
# Measure single transaction latency
start = cocotb.utils.get_sim_time('ns')
await master.read(addr=0x1000)
latency = cocotb.utils.get_sim_time('ns') - start
print(f"Read latency: {latency} ns")
```

## Related Documentation

- [Test Strategy](01_test_strategy.md) - Overall test approach
- [Arbiter FSMs](../ch03_fsm_design/01_arbiter_fsms.md) - FSM state details
- [ID Tracking](../ch04_id_management/02_id_tracking.md) - ID table operation
