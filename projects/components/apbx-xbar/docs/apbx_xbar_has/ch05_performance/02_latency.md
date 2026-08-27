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
| Master APB setup + access | 2 | PSEL, then PENABLE |
| apb4_slave capture -> cmd skid | 2 | command registered out |
| apb4_master IDLE -> SETUP -> ACCESS | 3 | downstream PSEL/PENABLE |
| Slave response -> rsp skid | 2 | response registered back |
| apb4_slave BUSY -> PREADY | 1 | master-visible completion |
| **Total** | **10** | **measured**, zero-wait-state slave |

: Uncontended Transaction Latency

**These are measured numbers, not protocol minimums.** A crossbar
transfer is NOT the 2-cycle APB minimum: the fabric converts APB to an
internal cmd/rsp protocol through `apb4_slave` and back through
`apb4_master`, and both directions cross REGISTERED skid buffers. A
direct probe on `apbx_xbar_1to1` with an always-ready slave measures
**10 pclk cycles** from PSEL to PREADY, and **10 cycles** sustained
back-to-back (the `apb4_slave` FSM is one-command-at-a-time: it cannot
capture the next command until it returns to IDLE). Earlier revisions
of this page claimed 2 cycles, which is the bare APB protocol minimum
for a directly-attached slave -- it does not apply through this
fabric.

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
              Total: 10 cycles (measured through the fabric)
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
              Total: 10+ cycles (plus slave wait states and contention)
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
