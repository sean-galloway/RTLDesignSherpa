# TASK-005: one RTL harness -- move the host path down so verify-sim can reach it
> **Was `TASK-084` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Priority:** High -- TASK-081 was a defect the gate could not see. Fixing the
defect without fixing the blindness leaves the next one equally invisible.
**Status:** CLOSED 2026-09-23 -- full re-validation, sim and board.

RAPIDS had THREE levels where STREAM has two, and the host path was stranded at
the wrong one:

```
  before                                  after (the STREAM shape)
  rapids_char_genesys2_top  (MMCM/pins)   rapids_char_genesys2_top  (MMCM/pins)
  rapids_char_top   1129 lines            rapids_char_top    262 lines
      UART->AXIL master                       pins + reset sync + LED/7-seg
      region decode, harness CSRs         rapids_char_harness  (SIM TOPLEVEL)
      apb4_master, both AXIL FSMs             UART->AXIL, CSRs, kick sequencer
      the KICK SEQUENCER                      apb4_master, + the DUT
  rapids_char_harness  (SIM TOPLEVEL)
      just wiring + the DUT
```

`stream_harness` takes `i_uart_rx`/`o_uart_tx` directly and owns `harness_csr`;
`stream_genesys2_top` is pins + MMCM + `u_harness`. RAPIDS now matches. 717 lines
relocated by line range -- working, board-validated RTL was never retyped -- and
the old instantiation port map re-expressed as declarations plus alias assigns
for exactly the 35 connections whose actual differed from the formal.

**Harness: 104 ports -> 7** (`aclk`, `aresetn`, `i_uart_rx`, `o_uart_tx`,
`o_led_status`, `o_result_valid`, `o_pass`). The 55 `cfg_*`/`obs_*`/`gen_*`/
`s_apb_*` ports collapsed inward, which is why the port count fell so far: they
were the CSR interface, and the CSRs are inside now.

**The TB went 738 -> 225 lines** because it reuses `RapidsCharCampaign` -- the
BOARD's own host program -- over `UartSimHarness` + `RapidsCharIO` inside
`cocotb.external`. Sim and board now run the same code rather than two
implementations that must be kept in agreement. They had already drifted apart
once: that drift was TASK-081.

**Validation (all of it, because a refactor of a board-validated design earns
none of the benefit of the doubt):**

| gate | result |
| --- | --- |
| lint, both flists | 0 real errors, 268 warnings -- identical in kind to baseline, 0 citing either rewritten file |
| `rapids_char_top` port list | byte-identical (9 ports, 13 params) -- XDC and the Genesys 2 wrapper untouched |
| harness sim | 2 passed (sink + source), 630.75s |
| kick sim | 2 passed (kick_enable + empty_mask), 596.49s |
| `verify-sim` gate | passed on the new TB, proven non-vacuous (link probe + 4 golden CRCs + `wr prod=32`) |
| bitstream | RC=0, WNS 1.041 / TNS 0.000 / 0 failing of 201142, WHS 0.058 |
| board campaign | **OVERALL PASS**, 8ch x 8 beats |

Behaviour is provably unchanged: all 16 board CRCs are byte-identical to the
pre-refactor campaign (`0x89346A28 / 0x1BD7E214 / 0x942B69BD / 0x06C8E181 /
0xB554DBD2 / 0x27B753EE / 0xA84BD847 / 0x3AA8507B`), `AXI4-wr prod=64` at 91.4%
and `AXI4-rd prod=64` at 80.0% both match exactly. Utilisation went DOWN
slightly (55197 -> 55158 LUTs, 41808 -> 41799 regs, BRAM unchanged) -- expected
once a module boundary dissolves and logic merges. WNS 1.213 -> 1.041 ns: tighter
but positive, and a thin positive WNS is this flow's design point.

**Two things fell out of it:**

- `test_rapids_char_top_kick.py` observes `apb_cmd_*`, which is internal to
  `u_harness` now. Repointed to `dut.u_harness.*` AND given `--public-flat-rw`:
  Verilator inlines plain internal wires, and an inlined signal is not `false` at
  runtime, it is ABSENT -- the recorder would have silently seen nothing and the
  test would have failed claiming the sequencer emitted no writes.
- TASK-082 now REPRODUCES IN SIM. See that task.
