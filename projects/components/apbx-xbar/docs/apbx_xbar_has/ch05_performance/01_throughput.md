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

## Maximum Throughput

### Single Master

With a single master accessing any slave:

Split by arbiter presence -- the generator emits one only when M > 1, and
its registered grant costs a cycle on every figure. See 5.2.

| Metric | M = 1 | M > 1 | Notes |
|--------|-------|-------|-------|
| Cycles per transaction (uncontended) | 9 SETUP->PREADY; 8 fabric | 10 SETUP->PREADY; 9 fabric | measured, zero-wait slave |
| Sustained cycles per transaction | 10 (PREADY->PREADY) | 11 (PREADY->PREADY) | measured back-to-back, one active master |
| Maximum transactions per cycle | ~0.100 | ~0.091 | 1 transaction / 10 or 11 cycles |
| Data throughput (32-bit @ 100MHz) | ~40 MB/s | ~36 MB/s | 4 B per period |
| Data throughput (32-bit @ 250MHz) | ~100 MB/s | ~91 MB/s | 4 B per period |

: Single-Master-Active Throughput, by Variant Class

M = 1: `apbx_xbar_1to1`, `apbx_xbar_1to4`. M > 1: `apbx_xbar_2to1`,
`apbx_xbar_2to4`, `apbx_xbar_2to2_mixed` -- so the 2x4 the PRD calls the
typical SoC case is the slower column. This table published the M = 1
figures unconditionally until 2026-08-29.

### Multi-Master (Uncontended)

When masters access different slaves:
- Each master achieves single-master throughput
- Aggregate throughput = M x single-master throughput
- No arbitration overhead

### Multi-Master (Contended)

When masters compete for the same slave:

| Masters | Effective Throughput | Notes |
|---------|---------------------|-------|
| 2 | 50% per master | Round-robin sharing |
| 3 | 33% per master | Round-robin sharing |
| 4 | 25% per master | Round-robin sharing |

: Contended Access Throughput

## Arbitration Handoff

### Grant Persistence

The crossbar implements grant persistence:
- A master holds the grant for the duration of ONE transaction
- The grant is released at the RESPONSE handshake, not when PSEL drops
  (`grant_ack = grant && rsp_valid && rsp_ready`, arbiter instantiated
  with `WAIT_GNT_ACK(1)`), after which the round-robin mask rotates --
  holding PSEL does not keep the grant if another master is requesting
- A single master with no competitor re-wins immediately, so its
  transactions still stream back-to-back -- at the fabric's own
  cadence, not at APB's 2-cycle minimum

### Back-to-Back Timing

A "zero-bubble" 4-cycle two-transaction diagram appeared here in
earlier revisions. It described a pipeline this RTL does not have: the
`apb4_slave` front end is a one-command-at-a-time FSM
(IDLE -> BUSY -> WAIT), so the next command is not captured until the
previous transaction completes. But sustained cadence is not equal to
single-transfer latency either -- it is one cycle longer. A master
holding PSEL high and dropping PENABLE for exactly one cycle after each
PREADY (the earliest LEGAL turnaround) measures **PREADY-to-PREADY = 10
pclk cycles**, against a 9-cycle SETUP-to-PREADY single transfer. The
extra cycle is the next transfer's mandatory SETUP phase, which cannot
overlap the previous transfer's ACCESS. See 5.2 for the convention and
the cycle-by-cycle breakdown. There is still no overlap between
consecutive transactions to draw.

## Throughput Factors

### Factors That Reduce Throughput

| Factor | Impact | Mitigation |
|--------|--------|------------|
| Slave wait states | Variable | Choose faster peripherals |
| Arbitration conflicts | 1+ cycle | Distribute access across slaves |
| Slave response time | Variable | Design slaves for quick response |

: Throughput Reduction Factors

### Optimal Usage Pattern

For maximum throughput:
1. Distribute master access across different slaves
2. Minimize slave wait states
3. Use burst-like access patterns (same master, same slave)
4. Avoid rapid master switching on same slave

---

**Next:** [Latency Analysis](02_latency.md)
