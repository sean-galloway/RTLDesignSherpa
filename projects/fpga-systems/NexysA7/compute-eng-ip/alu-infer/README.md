# alu-infer on Nexys A7-100T

The cell's inference ALU
([`projects/components/compute-eng-ip/alu-infer`](../../../../components/compute-eng-ip/alu-infer/README.md))
in the ALU board harness on the Nexys A7. It is the
[Genesys 2 harness](../../../Genesys2/compute-eng-ip/alu-infer/README.md):
the same `alu_harness`, CSRs and `alu_slot`, built from that area's
filelists. Only the board top differs: the clock and the pins.

The host driver and programs are board-independent and live in the Genesys 2
area's `bin/`; `host_alu.py` here imports them from there. The
UART-equivalence sim runs in that area too.

| Path | What |
|---|---|
| `rtl/alu_nexysa7_top.sv` | board top: 100 MHz -> MMCM -> 4.6875 MHz, UART -> AXI4-Lite, alu_harness, LEDs |
| `build-infer/` | `alu_infer_top` in the slot; `ALU_PROFILE=lean` or `full` |

```sh
make lint ALU_PROFILE=full
make bitstream ALU_PROFILE=full
make program ALU_PROFILE=full
make host-alu                    # smoke, known_answer, stream, backpressure, latency, pwl
```

## Board result (2026-10-20): function proven, clock not

Full profile (every format and row family), on the board:

| Program | Result |
|---|---|
| smoke | PASS (depth 256, pipe depth 8) |
| known_answer | PASS, 23 cases (the one `err` is the deliberate unassigned-opcode case) |
| stream | PASS, 256 invocations in 257 cycles (one per clock) |
| backpressure | PASS, fill and random-ready consumers |
| latency | PASS, comb 0 / adder 3 / mul 0 / acc 0, as configured |
| pwl_sigmoid | PASS, 128 points |

25,854 LUTs (41%), 3,466 flops, no DSPs, no block RAM.

**The clock is a bring-up clock, not a result.** At 50 MHz the full profile
failed post-route by -128 ns: one 148 ns, 222-level path from the command
RAM through the accumulate row's single-cycle fp32 FMA into the result FIFO.
The slot builds the ALU with `MUL_LATENCY = MAC_LATENCY = 0`, and the
accumulate loop is one FMA per clock by design. 4.6875 MHz (VCO 600 / 128)
covers it with +32 ns. Making the ALU close at a real clock is alu-infer
TASK-010 (`vault/tracking/projects/components/compute-eng-ip/alu-infer/`).

LEDs: 0 busy, 1 done, 2 error seen, 3 MMCM locked, 5/6 UART activity,
7 heartbeat.
