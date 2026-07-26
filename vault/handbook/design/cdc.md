---
title: Clock-domain crossing
summary: Sync every crossing; gray-code pointers; handshakes for events.
---

# CDC

- Never sample a foreign-domain signal raw. Multi-bit quasi-static data:
  `glitch_free_n_dff_arn` (3 flops typ). Single-cycle events: `sync_pulse`.
  Req/ack transactions: `cdc_2_phase_handshake` / `cdc_4_phase_handshake`
  (rtl/amba/cdc/). Open-loop rate crossing: `cdc_open_loop`.
- FIFO pointers cross domains gray-coded: `bin2gray` -> sync flops ->
  `gray2bin`. This is why bin2gray/gray2bin live in rtl/common (they serve
  CDC, not math - deliberate decision when rtl/math split out).
- Async FIFO depths are powers of 2 (gray wrap correctness), and EVEN depths
  matter for the ASIC variant - see docs/markdown/rtl-amba/cdc/cdc.md for the
  depth-36 case study.
- In XDC: async clock groups for unrelated clocks. But see
  [[timing-closure]] - a giant negative WNS is usually NOT a missing clock
  group; check clock interaction before touching constraints.
