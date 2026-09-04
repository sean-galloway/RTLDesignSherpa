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

When a Bridge test fails, start here. This guide lists the failure modes that actually occur and how to chase each one down.

## Debug Signal Access

### There are no `dbg_*` ports

The generator emits no debug ports. Earlier revisions of this chapter showed
`dbg_aw_grant_s0`, `dbg_outstanding_m0`, `dbg_resp_master` and a
`dbg_id_table_*` CAM view; none of them exist in any generated module, and
every procedure written against them fails immediately with a cocotb
`AttributeError`.

Debug instead by reaching into the real internal signals by hierarchical
name. They are named after the SLAVE (`<slave>_...`) in the xbar and are plain
`logic`, so cocotb can read them directly:

```python
@cocotb.test()
async def test_with_debug(dut):
    xbar = dut.u_xbar                     # instance name in the generated top
    grant   = xbar.ddr_aw_arb_gnt.value   # which master holds the AW grant
    locked  = xbar.ddr_aw_arb_locked.value
    rr      = xbar.ddr_aw_arb_rr.value    # round-robin pointer
    routed  = xbar.ddr_axi_rid_bridge_id.value  # bridge_id the R beat returns to
```

| Category | Real signals | Purpose |
|----------|--------------|---------|
| Arbitration | `<slave>_aw_arb_gnt`, `_locked`, `_rr`, `_req`, `_pick` | Grant, lock and round-robin state, per slave, AW and AR |
| Response routing | `<slave>_axi_bid_bridge_id`, `<slave>_axi_rid_bridge_id` | The `bridge_id` a B/R beat is muxed to. This is the routing decision -- the AXI ID is not used |
| Outstanding tracking | `aw_trk_wptr` / `aw_trk_rptr`, `ar_trk_*` (in the master adapter) | Depth of the in-order tracking FIFO |
| Target gating | `aw_gate_ok` / `ar_gate_ok`, `r_aw_active_target` (adapter) | Why a new AW/AR to a different slave is being held off |

: Table 7.3: Debug Signals That Exist

There is no outstanding-count output and no FSM state vector -- the arbiters
are two-state (`locked` / not) rather than an encoded FSM, so `_locked` plus
`_gnt` is the whole state.

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
print(f"AW grant (ddr): {dut.u_xbar.ddr_aw_arb_gnt.value}")
print(f"AW locked     : {dut.u_xbar.ddr_aw_arb_locked.value}")

# 3. Check the tracking FIFO and the single-outstanding-target gate
print(f"AW trk wptr/rptr: {dut.u_cpu_adapter.aw_trk_wptr.value}"
      f"/{dut.u_cpu_adapter.aw_trk_rptr.value}")
print(f"aw_gate_ok      : {dut.u_cpu_adapter.aw_gate_ok.value}")

# 4. Check slave response
print(f"BVALID: {dut.s0_axi_bvalid.value}")
print(f"BREADY: {dut.s0_axi_bready.value}")
```

**Common Causes:**
- Arbiter locked by another master (`_arb_locked` high for someone else)
- **A different slave is still outstanding.** `aw_gate_ok` low means the
  adapter is holding AWREADY down because every outstanding write must target
  one slave at a time. This is by design, not a fault -- see the
  single-outstanding-target note in the PRD.
- Slave not responding
- Tracking FIFO full (`aw_trk_wptr` has lapped `aw_trk_rptr`)

### Issue: Wrong Response Routing

**Symptoms:**
- Response arrives at wrong master
- BID mismatch errors

**Debug Steps:**

```python
# The AXI ID passes through UNCHANGED -- there is no ID extension.
print(f"Master AWID : {dut.cpu_m_axi_awid.value}")
print(f"Slave  AWID : {dut.ddr_axi_awid.value}")     # same value

# Routing is by the bridge_id sideband, not the ID:
print(f"B routed to bridge_id: {dut.u_xbar.ddr_axi_bid_bridge_id.value}")
print(f"R routed to bridge_id: {dut.u_xbar.ddr_axi_rid_bridge_id.value}")
```

**Common Causes:**
- **The slave returned responses out of order.** Routing pops an in-order
  FIFO, so a reordering slave sends one master's beats to another. Nothing
  detects it. This is the single most likely cause and it is a design
  constraint, not a bug in the bridge -- see FR-2 in the PRD.
- ID width mismatch between master and slave ports
- Two masters using the same AXI ID to one slave: their IDs alias at the
  slave, and only the `bridge_id` sideband keeps the responses apart

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
├── Arbitration (inside u_xbar)
│   └── ddr_aw_arb_gnt, ddr_aw_arb_locked, ddr_ar_arb_gnt, ddr_ar_arb_locked
├── Target gating (inside the master adapter)
│   └── aw_gate_ok, ar_gate_ok, r_aw_active_target
└── Response
    └── s0_axi_bvalid, m0_axi_bvalid, ddr_axi_bid_bridge_id
```

### Timing Analysis

```wavedrom
{ "signal": [
  { "name": "aclk",    "wave": "p....." },
  { "name": "awvalid", "wave": "1..0.." },
  { "name": "awready", "wave": "0.10.." },
  { "name": "wvalid",  "wave": "0..1.." }
],
  "head": { "text": "Expected Transaction Timing" }
}
```

## Assertion Failures

### There are no built-in assertions

The generated RTL contains no `assert` statements of any kind -- not in the
top, the xbar or any adapter. An earlier revision of this section showed two
protocol assertions as though they shipped; they never existed, and the
signals they referenced (`s_awvalid`, `r_current_awid`) match no identifier in
the generated design.

Protocol checking is the testbench's job here. Use the AXI4 BFMs and the
monitor wrappers rather than expecting the DUT to flag a violation itself.

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
