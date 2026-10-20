# Document Information

## Revision History

| Revision | Date | Author | Description |
|----------|------|--------|-------------|
| 0.1 | 2026-10-05 | RTL Design Sherpa | Initial board validation roll-up for the BCH Genesys 2 harness. |
| 0.2 | 2026-10-20 | RTL Design Sherpa | Block diagrams redrawn to the repo element key (v3): class fills, double-bordered registered blocks, green return paths and a generated key under each figure. No technical content changed. |
| 0.3 | 2026-10-20 | RTL Design Sherpa | Section (h2) headings now open a new page, the pipeline default. No technical content changed. |

: Table 0.1: Revision history.

## Scope

This book covers the BCH(4224,4120) t=8 codec as exercised on the Digilent
Genesys 2 board. It describes the harness, the campaign methodology, and the
soak result that produced one million decoded blocks of board evidence.

## Provenance

All timing and campaign results in this book come from `stable/MANIFEST.md` and
`stable/results/2026-10-05_soak/`. The board used for the runs is Digilent
Genesys 2 serial `200300B818A0` (Kintex-7 `xc7k325t-2`), programmed and
measured with Vivado 2025.1.
