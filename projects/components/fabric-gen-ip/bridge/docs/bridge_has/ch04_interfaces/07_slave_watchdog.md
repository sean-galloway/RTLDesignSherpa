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

# Slave Watchdog

## Overview

A slave that stops answering hangs every master with a transaction
outstanding at it, and the masters behind those. A slave port declared with
`timeout_cycles = N` (AXI4 slaves; 0, the default, means none) puts
`axi4_slave_watchdog` (`rtl/amba/axi4/`) in front of it. While the slave
answers, the watchdog is a zero-latency pass-through. If the slave is silent
for N cycles with work outstanding, the watchdog cuts it off and completes
everything itself with DECERR (GitHub #119 L3).

## Ports

| Port | Dir | Meaning |
|---|---|---|
| `<slave>_timeout` | out | **sticky**: the watchdog tripped; held until reset |

: Slave watchdog status (one per slave with `timeout_cycles > 0`)

## Functional Description

### When it trips

The timer counts only while there is work outstanding (a transaction the
slave accepted and has not finished, owed W beats, or a request it has not
accepted) and the slave is the blocker: no B or R VALID from it and no
handshake on any channel. Any handshake with the slave restarts the count.
A slow slave that is alive never trips it, and a response held off because
the bridge is not ready does not count against the slave.

### What it does then

- **The slave is cut off.** It sees no VALID from then on (a request it had
  not accepted is withdrawn) and BREADY and RREADY high, so late responses
  drain and are dropped.
- **Everything outstanding is answered DECERR.** Each write gets one B once
  its W burst is complete; owed W beats are accepted and discarded. Each read
  gets its remaining beats, so a burst the slave had half returned is
  finished, not restarted, and RLAST lands on the right beat. Responses go
  out oldest-of-their-ID first, so per-ID order holds.
- **New requests are answered the same way**, as the subtractive slave
  answers an unmapped address: DECERR, and 0xDEADBEEF read data.
- **No response is withdrawn.** The trip is taken only in a cycle with no B
  or R VALID from the slave, so the masters never see a response vanish.

It tracks up to the slave's `max_outstanding` transactions per direction,
and the slave's AWREADY/ARREADY seen by the fabric drop while that is full.
It sits on `aclk`, between the slave adapter's timing wrapper and the port,
or the clock crossing on a `cdc = true` port that one master reaches. A
`cdc = true` port that several masters share is arbitrated on its own clock
and takes no watchdog (HAS 4.5a).

### Measured

`bridge_2x2_rw_wdog` (ddr behind a 64-cycle watchdog), `test_bridge_2x2_rw_wdog_trip`:

- a ddr answering 20 cycles late passes through untouched;
- with ddr hung on a write and a 4-beat read from two masters, both complete
  with DECERR 80 and 81 cycles after issue (64 plus the pipeline), and
  `ddr_timeout` rises;
- a new write and read to ddr are answered at once; sram, beside it, still
  reads back what was written;
- the protocol checkers on every port saw no violation throughout.

## Design Notes

- Assumes W never leads its AW (the crossbar's W steering guarantees it) and
  that the slave returns R bursts contiguously (PRD FR-9).
- Recovery is by reset. A slave that has been cut off is presumed dead; there
  is no path back to it short of reset.
- The AXI rule that VALID holds until READY is broken on the slave side when
  the trip withdraws a request the slave had not accepted. That is the
  slave the watchdog has declared dead.
