# ISSUE-004: sdpram_core serialises bursts, so a master's MAX_OUTSTANDING buys nothing

**Priority:** P2
**Status:** open
**Owner:** TBD

`rtl/amba/shared/sdpram_core.sv` accepts exactly ONE burst at a time on each
direction, so there is a fixed dead-cycle cost at every burst boundary that no
amount of master-side outstanding capacity can hide.

```systemverilog
assign fub_awready = !r_wr_active && !r_b_pending && !w_clearing;
assign fub_wready  =  r_wr_active && !w_clearing;
assign fub_arready = !r_rd_active && !w_clearing;
```

- **Write:** the next AW cannot be accepted until the current burst has
  finished AND its B has been consumed (`!r_wr_active && !r_b_pending`), and W
  data only flows while active. So the last W beat of burst N, the B
  handshake, and the AW of burst N+1 are strictly serial.
- **Read:** the next AR cannot be accepted until the current burst's last beat
  (`!r_rd_active`), so R goes idle between bursts.

A master built with `MAX_OUTSTANDING > 1` expecting overlap gets none against
this slave.

## Measured

On the Nexys A7 RS loop harness (2026-10-01), with bandwidth meters gated to
the engine's own pass so per-burst cost was visible:

| channel | buckets | per burst |
|---|---|---|
| encoder W into the slave | 501 cycles BACKPRESSURE, 11 starvation | ~2.0 cycles |
| decoder R out of the slave | 394 cycles STARVATION, 0 backpressure | ~1.6 cycles |

The direction of the buckets is the evidence: the master was producing fine
and the slave was refusing (write), and the master was always ready and the
slave was not delivering (read). Both costs divided evenly by the BURST COUNT
rather than the beat or block count.

At `burst_len = 16` over a 63-beat codeword that was 4 bursts a block and
~7.9 + ~3.9 cycles a block. Raising the burst length to 64 quartered the
burst count and took the two channels from 88.9% / 94.1% to 97.0% / 98.5%
utilisation -- which confirms the cost is per burst, and is a WORKAROUND, not
a fix.

## Why this is not Reed-Solomon's

Every consumer of `sdpram_slave_axi4_axi4` pays it:

- `projects/fpga-systems/Genesys2/stream/rtl/stream_harness.sv`
- `projects/fpga-systems/Genesys2/rapids/flows-rapids/rtl/rapids_byte_harness.sv`
- `projects/fpga-systems/Genesys2/rapids_beats/flows-rapids-beats/rtl/rapids_char_harness.sv`
- the RS AXI4 harness and its two component TB tops

RS only noticed because its meters were gated to a single stage, which is what
made a per-burst cost separable from everything else in the run.

## What is NOT yet decided

Whether this is a defect or a deliberate simplicity. `sdpram_core` is a test
memory, and one-burst-at-a-time is a reasonable thing for a test memory to be;
the cost is invisible at long bursts and only bites a master issuing many
short ones. That judgement belongs to the area owner, which is why this is an
issue rather than a bug.

Resolves into one of:

- **a bug**, if overlapping bursts are part of this slave's intended contract;
- **a task**, to pipeline AW/B against the active burst and accept AR during
  the final R beat;
- **a recorded no-action**, with the per-burst cost documented so consumers
  size their bursts knowingly -- in which case the module header should say so,
  because today nothing warns a master author that outstanding capacity is
  inert here.

## Not to be confused with

The `USE_WSTRB` default. `USE_WSTRB = 1'b1` costs ~23k LUTs of distributed RAM
by blocking block-RAM inference; every writer that writes whole words should
pass `1'b0`. That is a separate, already-known trap.
