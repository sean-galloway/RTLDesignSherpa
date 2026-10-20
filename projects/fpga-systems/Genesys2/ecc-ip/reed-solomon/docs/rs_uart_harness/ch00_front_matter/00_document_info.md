# Document Information

## Revision History

| Revision | Date | Author | Description |
|----------|------|--------|-------------|
| 0.1 | 2026-10-06 | RTL Design Sherpa | Initial harness guide for the Reed-Solomon Genesys 2 UART loop. |
| 0.2 | 2026-10-20 | RTL Design Sherpa | Block diagrams redrawn to the repo element key (v3): class fills, double-bordered registered blocks, green return paths and a generated key under each figure. No technical content changed. |

: Table 0.1: Revision history.

## Scope

This book describes the RS(252,236) t=8 UART harness on the Digilent Genesys
2: its contents, connectivity, and the motivations behind the FPGA testing
choices. It is the harness guide that pairs with the Reed-Solomon Board
Validation Report, which carries the run evidence.

## Provenance

The harness description comes from `docs/UART_HARNESS.md`, the living markdown
copy in the harness directory. Build facts come from `stable/MANIFEST.md` and
`stable/reports/`. The board used for the runs is Digilent Genesys 2 serial
`200300B818A0` (Kintex-7 `xc7k325t-2`), programmed and measured with Vivado
2025.1.
