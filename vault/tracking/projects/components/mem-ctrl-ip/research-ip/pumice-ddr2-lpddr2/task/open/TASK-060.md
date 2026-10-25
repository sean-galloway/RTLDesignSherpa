# TASK-060: injectors issue half the DFI burst, addresses alternating bl-hi, bl-lo, bl-hi, bl-lo

> Source: owner, 2026-10-24, while TASK-059 was in progress: "to do: have the
> injectors issue 1/2 the dfi BL and the address are in bl-hi, bl-lo, bl-hi,
> bl-lo". Related: TASK-049 (eight injectors), the char engine's address
> generator (`char_gen_unit`, `program_wr_engine` / `program_rd_engine` with
> `burst_len` / `stride_0`), the burst chopper and the controller's
> legal-AxLEN quantum (`AXI_BEATS_PER_BURST`).

**Priority:** P2
**Status:** open (filed 2026-10-24)
**Owner:** TBD

## What is asked

A traffic family where every injector transaction covers HALF of one DRAM
(DFI) burst, and consecutive transactions alternate between the upper and
the lower half of a burst: bl-hi, bl-lo, bl-hi, bl-lo, ... So two
consecutive requests touch the same DRAM burst from opposite ends, and the
controller sees sub-burst accesses that it must either merge, mask or
serve as two bursts.

## To settle before building

- What "half the DFI BL" is at each geometry. At the board geometry (BL4,
  x16, 32-bit beat on a 64-bit AXI) one DRAM burst is ONE AXI beat, so half a
  burst is a half-beat: a narrow transfer with strobes, not a shorter AxLEN.
  At the sim geometries with a wider beat it is a shorter AxLEN. The engine
  must express both (AxSIZE / WSTRB for the half-beat case).
- Address sequence: hi, lo, hi, lo -- the generator's stride alternates
  (+half, +half, ...) within a burst and the burst base advances every two
  transactions; `stride_0` alone does not express it, so the generator needs
  a second stride or a two-step pattern.
- Both directions, reads and writes, as a family in `pumice_char` with its
  own grid cell (proxy and board), measured against the whole-burst
  incremental family on the same text.

## What landed / Measured / Gates

(not started)
