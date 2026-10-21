# alu-infer on Genesys 2

Board harness for the cell's inference ALU
([`projects/components/compute-eng-ip/alu-infer`](../../../../components/compute-eng-ip/alu-infer/README.md)).

The UART cannot keep an ALU busy, so the host **loads** up to 256 invocations
into a command RAM, then `START` issues them back to back at the harness clock
(100 MHz). Every result lands in a result RAM with the cycle of its issue and
retire edges, which is how the board measures latency and II=1. The consumer
side can stall: always ready, random ready, or "fill" (hold off until the
ALU's tag FIFO is full, then drain).

The harness knows only the ALU's issue seam. The device under test is the
module `alu_slot`, which each build supplies -- other valid/ready ALUs (and,
later, Gatling as the issuer) reuse the same harness.

| Path | What |
|---|---|
| `rtl/alu_harness.sv`, `rtl/alu_harness_regs.rdl` | harness + CSRs (UART -> AXI4-Lite -> APB -> PeakRDL) |
| `rtl/alu_genesys2_top.sv` | board top: 200 MHz LVDS -> MMCM -> 100 MHz, UART, LEDs |
| `build-infer/` | `alu_infer_top` in the slot; `ALU_PROFILE=lean` (every EN_* off) or `full` |
| `bin/alu_harness.py`, `bin/alu_programs.py` | host driver + programs, the SAME code in sim and on the board |
| `dv/tests/test_alu_harness_uart.py` | UART-equivalence sim: the programs over the real bridge RTL |

```sh
make regmap                                   # after any .rdl change
make sim                                      # the UART-equivalence sim (both profiles)
make lint ALU_PROFILE=lean
make bitstream ALU_PROFILE=lean               # then full
make program ALU_PROFILE=lean
make host-alu                                 # smoke, known_answer, stream, backpressure, latency, pwl
```

Status (2026-10-21): sim green (6 programs x 2 profiles), lint green; not yet
built. It was paused for a kestrel Genesys 2 build, which no longer exists:
kestrel's only board build is now the Nexys A7 (2026-10-21), so the kestrel
work it waited on no longer blocks it.
