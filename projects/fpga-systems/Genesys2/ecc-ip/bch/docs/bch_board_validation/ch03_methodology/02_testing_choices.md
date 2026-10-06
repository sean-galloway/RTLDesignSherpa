# Testing Choices

## Injector modes mapped to failure mechanisms

The shared `error_injector` exposes eight modes, and each one answers a
different physical question:

| Mode | Failure mechanism exercised |
|------|-----------------------------|
| 0 | None: clean run baseline. |
| 1 | Exact count: the e <= t / e > t correction boundary. |
| 2 | Burst: raw bit-error behaviour on a noisy channel. |
| 3 | Rate: continuous random bit-error rate. |
| 4 | Clusters: spatially correlated faults (bad DRAM row, disturbed NAND page). |
| 5 | Localized: windowed half-plane failure. |
| 6 | Badblock: retention tails and worn blocks. |
| 7 | Debug: deterministic walking bring-up pattern. |

: Table 3.2: Injector modes and the physical questions they answer.

## Post-encoder injection

The injector sits after the encoder, not inside the generator. An error in the
generator data would be encoded faithfully and the code would never see it. By
corrupting the codeword, the parity bits are exposed to the same errors as the
data, which is what happens when a real packet is stored, transmitted, or read
back from memory.

## UART and the safety pair

The host link is a plain UART at 115200 baud, driven by `uart_axil_bridge`.
That keeps the harness scriptable from Python without a debug-core licence.
Two pieces of shared tooling guard the board:

- `projects/fpga-systems/bin/board_lock.sh` serializes programming flows by
  JTAG serial.
- `projects/fpga-systems/bin/fpga_board.py` refuses to program until a JTAG
  readback confirms the expected Genesys 2 serial `200300B818A0` is present
  with a device behind it.

## Genesys 2 vs Nexys A7

The harness directory moved from `NexysA7/` to `Genesys2/` on 2026-10-05.
`BCH_TARGET` still accepts `nexys_a7_100t` as a build option, but the Genesys 2
is the primary target. The k325t-2 has the room and timing margin to hold the
full BCH(4224,4120) loop at 100 MHz with both AXIS and AXI4 flavours.

## AXIS vs AXI4

Two bitstreams are built: `bch_loop_genesys2_axis.bit` and
`bch_loop_genesys2_axi4.bit`. The AXIS flavour is a single streaming pipe; the
AXI4 flavour is a memory-to-memory job chain across four AXI4 memories. The
AXI4 flavour refuses runs whose `GEN_BLOCKS` exceed the job-memory capacity
rather than letting regions wrap, so long soaks belong on the AXIS image. The
host reads `TOPOLOGY` to discover which datapath is loaded.

## Deliberately not board-tested

Some things are out of scope. The soak campaign ran to its default time budget
and passed 1,000,000 mixed-mode blocks with zero mis-decodes, but that is a
statistical sample, not every pattern. BCH has no erasure path in this harness:
the injector's `out_erasure` is tied off and `cfg_mark_erasure` is held low.
The board validates only the `BCH(4224,4120) t=8` profile; smaller profiles are
covered in simulation and component DV.
