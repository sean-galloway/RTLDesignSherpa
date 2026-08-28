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

# Latency Analysis

## Transaction Latency

### Uncontended Access

When a master has exclusive access to a slave:

| Phase | Cycles | Description |
|-------|--------|-------------|
| Master SETUP | 1 | PSEL high, PENABLE low |
| apb4_slave capture + cmd skid | 2 | command registered out |
| apb4_master IDLE-launch / SETUP / ACCESS | 3 | downstream PSEL then PENABLE |
| Response + rsp skid | 2 | slave PREADY through the return skid |
| apb4_slave BUSY -> PREADY | 1 | master-visible completion |
| **Total** | **9** | PSEL to PREADY (8 of them ACCESS to PREADY) |

: Uncontended Transaction Latency

: Uncontended Transaction Latency

**These are measured numbers, not protocol minimums.** A crossbar
transfer is NOT the 2-cycle APB minimum: the fabric converts APB to an
internal cmd/rsp protocol through `apb4_slave` and back through
`apb4_master`, and both directions cross REGISTERED skid buffers.

**Measurement convention.** Every figure below counts rising `pclk`
edges and names the two edges it spans. State the edges or the number
means nothing -- this page has been wrong twice from not doing so.

| Quantity | Cycles | Spans |
|---|---|---|
| Fabric latency | **8** | first ACCESS edge -> edge where PREADY is high |
| Single-transfer latency | **9** | SETUP edge -> edge where PREADY is high (= 1 + 8) |
| Back-to-back period | **10** | PREADY edge -> next PREADY edge |

: Measured Timing, `apbx_xbar_1to1` With an Always-Ready Slave

**The period is 10, not 9, and the difference is structural.** After
PREADY at cycle N the bus is still in ACCESS for that cycle, so the next
transfer's mandatory SETUP cycle cannot begin before N+1; its ACCESS
follows at N+2 and its PREADY at N+2+8 = N+10. Reaching 9 would require
a SETUP cycle overlapping the previous transfer's ACCESS, which is not a
legal APB waveform. So sustained cadence does **not** equal
single-transfer latency here -- it is exactly one cycle longer.

Earlier revisions of this page claimed 2 cycles (the bare APB minimum
for a directly-attached slave, which does not apply through this
fabric), and later claimed a 9-cycle sustained cadence, which came from
a probe whose turnaround was not legal APB. A qc reviewer flagged the
9-cycle cadence and was told it was a false positive; the reviewer was
right. `dv/tests/test_apbx_xbar_timing.py` now asserts all three numbers
against the RTL so the question is settled by the suite rather than by
argument.

### Contended Access

When multiple masters compete for the same slave:

| Scenario | Additional Latency | Description |
|----------|-------------------|-------------|
| Win arbitration | 1 cycle | grant is REGISTERED in arbiter_round_robin |
| Lose to 1 master | ~10+ cycles | wait one full transaction (see above) |
| Lose to N masters | ~10N+ cycles | wait N transactions |

: Arbitration Latency

## Latency Breakdown

### Forward Path (Master to Slave)

| Component | Latency | Type |
|-----------|---------|------|
| apb4_slave capture | 0-1 cycle | Registered |
| Address decode | 0 cycles | Combinational |
| Arbitration | 0-1 cycle | Combinational + wait |
| apb4_master drive | 0-1 cycle | Registered |
| **Typical Total** | **4 cycles** | master PSEL to downstream slave PSEL |

: Forward Path Latency

### Response Path (Slave to Master)

| Component | Latency | Type |
|-----------|---------|------|
| Slave response | Variable | PREADY timing |
| apb4_master capture | 0-1 cycle | Registered |
| Response routing | 0 cycles | Combinational |
| apb4_slave drive | 0-1 cycle | Registered |
| **Typical Total** | **3 cycles** | downstream PREADY to master PREADY |

: Response Path Latency

## Latency Timing Diagram

### Best Case (No Waits, No Contention)

```
Master PSEL   ___|-----------|___
Master PENABLE___|_____------|___
               ^         ^
Slave PSEL    _____|---------|___
Slave PENABLE _____|___------|___
Slave PREADY  _________|-----|___
                       ^
Master PREADY _________|-----|___
                       ^
              Total: 9 cycles (SETUP edge to PREADY edge)
```

### Worst Case (Contention + Slave Wait States)

```
Master PSEL   ___|--------------------------|___
Master PENABLE___|________________----------|___
               ^  Arbitration    ^
               |  wait           |
Slave PSEL    ____________|---------------|___
Slave PENABLE ____________|______---------|___
Slave PREADY  _____________________|------|___
                                   ^
Master PREADY _____________________|------|___
                                   ^
              Total: 9+ cycles (plus slave wait states and contention)
```

## Latency Optimization

### Design Recommendations

| Goal | Recommendation |
|------|----------------|
| Minimize contention | Use more slaves, spread access |
| Reduce arbitration wait | Lower master count per slave |
| Reduce slave latency | Design slaves with quick PREADY |

: Latency Optimization Recommendations

---

**Next:** [Resource Estimates](03_resources.md)
