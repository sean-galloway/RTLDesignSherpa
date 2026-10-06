# Document Information

## Revision History

| Revision | Date | Author | Description |
|----------|------|--------|-------------|
| 0.1 | 2026-10-06 | RTL Design Sherpa | Initial harness guide for the BCH Genesys 2 UART loop. |

: Table 0.1: Revision history.

## Scope

This book describes the BCH(4224,4120) t=8 UART harness on the Digilent
Genesys 2: its contents, connectivity, and the motivations behind the FPGA
testing choices. It is the harness guide that pairs with the Binary BCH Board
Validation Report, which carries the run evidence.

## Provenance

The harness description comes from `docs/UART_HARNESS.md`, the living markdown
copy in the harness directory. Build facts come from `stable/MANIFEST.md` and
`stable/reports/`. The board used for the runs is Digilent Genesys 2 serial
`200300B818A0` (Kintex-7 `xc7k325t-2`), programmed and measured with Vivado
2025.1.
