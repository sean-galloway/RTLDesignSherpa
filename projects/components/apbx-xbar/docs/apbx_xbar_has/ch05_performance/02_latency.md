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

**The numbers depend on whether the variant has an arbiter, and the
generator only emits one when there is more than one master.** A
single-master variant has no `arbiter_round_robin` at all; a multi-master
variant has one per slave, and its grant is a flop (`grant <= w_next_grant`),
which costs exactly one cycle on every quantity below.

| Quantity | M = 1 | M > 1 | Spans |
|---|---|---|---|
| Fabric latency | **8** | **9** | first ACCESS edge -> edge where PREADY is high |
| Single-transfer latency | **9** | **10** | SETUP edge -> edge where PREADY is high |
| Back-to-back period | **10** | **11** | PREADY edge -> next PREADY edge |

: Measured Timing, Always-Ready Slave

M = 1 is `apbx_xbar_1to1` and `apbx_xbar_1to4` (0 arbiters). M > 1 is
`apbx_xbar_2to1`, `apbx_xbar_2to4` and `apbx_xbar_2to2_mixed` (1, 4 and 2
arbiters). All six columns are measured, not derived -- see
`dv/tests/test_apbx_xbar_timing.py`, which asserts both classes.

Until 2026-08-29 this page published the M = 1 numbers unconditionally,
under the heading "Uncontended Access", having measured only
`apbx_xbar_1to1`. They were one cycle optimistic for every arbitrated
variant -- including the 2x4 that the PRD calls the typical SoC case.

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

| Component | M = 1 | M > 1 | Type |
|-----------|-------|-------|------|
| apb4_slave capture | 1 | 1 | Registered |
| apb4_slave cmd skid out | 1 | 1 | Registered |
| Address decode | 0 | 0 | Combinational |
| Arbitration | **0** | **1** | No arbiter is emitted when M = 1; when one is, its grant is a flop |
| apb4_master cmd skid in | 1 | 1 | Registered |
| apb4_master cmd skid out | 1 | 1 | Registered |
| apb4_master IDLE -> SETUP | 1 | 1 | FSM |
| **Total** | **5** | **6** | master SETUP edge to downstream PSEL edge |

: Forward Path Latency

Both columns measured: 5 on `apbx_xbar_1to1`, 6 on `apbx_xbar_2to1`. The
arbitration row is the whole difference between the two variant classes.
This table carried a single unconditional column with a 1-cycle
arbitration row and a 5-cycle total until 2026-08-29 -- which cannot both
be true, since the 5 was measured on the variant that has no arbiter.

**The three numbers on this page must sum, and now do:**

  M = 1                                M > 1
    5  forward                            6  forward
  + 1  downstream SETUP -> ACCESS       + 1  downstream SETUP -> ACCESS
  + 3  response                         + 3  response
  = 9  SETUP-to-PREADY                  = 10 SETUP-to-PREADY

(With a zero-wait slave the downstream ACCESS and PREADY edges are the
same cycle, which is why the response row can be read from either. A slave
with wait states adds its own cycles between them and shifts the total.)

This table read **4** until 2026-08-29, which could not be reconciled with
the page's own 9-cycle total -- 4 + 3 left two cycles unaccounted for.
Measured on `apbx_xbar_1to1` with an always-ready slave: master SETUP at
cycle 1, downstream PSEL at cycle 6, downstream ACCESS at cycle 7, master
PREADY at cycle 10.

### Response Path (Slave to Master)

| Component | Cycles | Type |
|-----------|--------|------|
| Slave response | Variable | The slave's own PREADY timing, excluded below |
| apb4_master captures into rsp skid | 1 | Registered |
| rsp skid out, through the response mux | 1 | Skid registered; the mux itself is combinational |
| apb4_slave drives PREADY | 1 | Registered |
| **Total** | **3** | downstream PREADY edge to master PREADY edge |

: Response Path Latency

Same on both variant classes -- arbitration is on the command path only.
The rows read "0-1 cycle" each until 2026-08-29, which could not sum to
the stated 3.

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
