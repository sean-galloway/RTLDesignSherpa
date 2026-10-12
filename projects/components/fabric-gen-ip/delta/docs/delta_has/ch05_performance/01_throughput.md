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

# Throughput Characteristics

## Aggregate Throughput

Because each slave has its own arbiter and mux, aggregate throughput scales with the number of slaves. In the best case — every master targets a different slave and every slave is ready — the crossbar can accept one beat per master per cycle.

## Per-Slave Throughput

When multiple masters contend for the same slave, the round-robin arbiter gives each contending master an equal share of the slave's bandwidth. With `K` contending masters, each sees approximately `1/K` of the slave's available bandwidth.

## Head-of-Line Blocking

A master blocked on one slave does not block traffic to other slaves. Each slave arbiter is independent. However, a master that targets a heavily contended slave will wait until its round-robin turn and until the current packet completes.

## Throughput Targets

| Metric | Target | Notes |
|--------|--------|-------|
| Per-slave throughput | Up to 1 transfer/cycle | When one master continuously feeds one ready slave. |
| Aggregate throughput | Up to NUM_MASTERS transfers/cycle | When all masters target different ready slaves. |
| Mixed-traffic throughput | ≥ 0.7 transfers/cycle per active master | Under moderate contention in the performance model. |

: Table 5.1: Throughput Targets

## Factors That Reduce Throughput

- Contention for the same slave.
- Downstream backpressure (`m_axis_tready[s] == 0`).
- Multi-beat packets that lock the slave until `TLAST`.
- Arbitration overhead of one cycle when switching masters after `TLAST`.
