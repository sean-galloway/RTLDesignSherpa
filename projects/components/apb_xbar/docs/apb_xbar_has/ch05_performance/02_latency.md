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
| Setup | 1 | PSEL asserted, PENABLE low |
| Access | 1+ | PENABLE high, wait for PREADY |
| **Total** | **2+** | Minimum 2 cycles |

: Uncontended Transaction Latency

### Contended Access

When multiple masters compete for the same slave:

| Scenario | Additional Latency | Description |
|----------|-------------------|-------------|
| Win arbitration | 0 cycles | No delay |
| Lose to 1 master | 2+ cycles | Wait for one transaction |
| Lose to N masters | 2N+ cycles | Wait for N transactions |

: Arbitration Latency

## Latency Breakdown

### Forward Path (Master to Slave)

| Component | Latency | Type |
|-----------|---------|------|
| apb_slave capture | 0-1 cycle | Registered |
| Address decode | 0 cycles | Combinational |
| Arbitration | 0-1 cycle | Combinational + wait |
| apb_master drive | 0-1 cycle | Registered |
| **Typical Total** | **1-2 cycles** | From PSEL to slave PSEL |

: Forward Path Latency

### Response Path (Slave to Master)

| Component | Latency | Type |
|-----------|---------|------|
| Slave response | Variable | PREADY timing |
| apb_master capture | 0-1 cycle | Registered |
| Response routing | 0 cycles | Combinational |
| apb_slave drive | 0-1 cycle | Registered |
| **Typical Total** | **1-2 cycles** | From slave PREADY to master PREADY |

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
              Total: 2 cycles (APB minimum)
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
              Total: 5+ cycles (depends on contention + slave)
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
