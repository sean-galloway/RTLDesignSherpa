# ISSUE-001 — build-tetrad answered one UART read with ERR

**Status:** open · **Filed:** 2026-11-26 · **Area:** projects/components/riscv-ip/gatling-rv32i (board: projects/fpga-systems/NexysA7/riscv-ip/gatling/build-tetrad)

## What happened

The first `make host-gatling_tetrad` after the first `make program` of the
build-tetrad bitstream (2026-11-26 ~22:42) read the harness ID correctly,
then got `ERR` for the second command, a read of gatling_mem_bram's BUILD_ID
(`0x2_0004`) through the AXIL split. The host crashed on the `None` it
returned (a host bug, since fixed: see below).

## Why it is an issue, not noise

`uart_axil_bridge` answers `ERR` only when the AXI read or write response is
not OKAY. Nothing on that path produces one: `gatling_mem_bram`,
`gatling_tetrad_harness` and `gatling_tetrad_axil_split` all return OKAY
constants, and the bridge's own masters have no timeout. So either a response
with a non-zero RRESP reached the bridge, or the bridge sent ERR for another
reason; neither is explained.

## What has been tried

- Same two reads, six times each, right after a second `make program`: clean.
- 40 port opens (with the host's autodetect, as the failing run did) x 4
  reads alternating the two slaves: 160 reads, clean.
- Three full host runs (smoke + tetrad at N = 96 twice and N = 384): clean.
- The UART-equivalence sim of the same rig passes every run.

## Next

- Capture `m_rresp` / `s_rresp` at the split with an ILA, triggered on the
  bridge's ERR load, across repeated program-then-run cycles.
- Check the bridge parser's state after configuration (the line idles high
  only once the FPGA drives nothing on it; a framing glitch at power-on could
  leave a partial command).
