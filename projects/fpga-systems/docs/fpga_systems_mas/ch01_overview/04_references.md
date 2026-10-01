# References

## In this repository

| Path | What it is |
| --- | --- |
| `projects/fpga-systems/bin/` | The layer this book specifies |
| `vault/handbook/fpga/cmn-infra/uart-harness.md` | Method: one host program for sim and silicon |
| `vault/handbook/fpga/cmn-infra/boards.md` | Method: board mechanics and gotchas |
| `vault/handbook/fpga/cmn-infra/host-stack.md` | Method: the shared py transport stack |
| `vault/handbook/fpga/cmn-infra/sequences.md` | Method: campaign structure |
| `vault/handbook/fpga/cmn-infra/flow-layout.md` | **Authority** for the directory skeleton and filename conventions |
| `vault/handbook/fpga/cmn-infra/flow-migration.md` | Method: migrating a pre-migration `flows-*` flow |
| `vault/handbook/fpga/cmn-infra/area-structure.md` | Method: where an FPGA project lives |
| `make/fpga_flow.mk` | The make targets discovered from the filename prefixes |
| `vault/handbook/dv/registers-by-name.md` | Method: never address a register by offset |
| `vault/handbook/dv/running-regressions.md` | Method: clean builds, and why a fast pass is fiction |
| `bin/DOC_GENERATION.md` | How this book becomes a PDF |
| `bin/TBClasses/harness/` | The simulation-side transport spine the bridge plugs into |

The handbook is the authority on method. This book is the authority on the
layer. Where they meet, the handbook wins and this book links to it.

## Tracker

| Item | Subject |
| --- | --- |
| tooling TASK-022 | The board lock, the identity readback, and the identity record |
| tooling TASK-024 | This book |

## External

- Xilinx UG908, *Vivado Design Suite User Guide: Programming and Debugging* --
  `hw_server`, `hw_target`, and the JTAG object model the Tcl scripts use.
- FTDI device datasheets (FT2232H, FT232R) -- the USB descriptor fields that
  carry the serial numbers port matching depends on.
- Digilent board reference manuals (Nexys A7-100T, Genesys 2) -- which FTDI part
  is fitted and how its interfaces are wired.

## A note on register documentation

This book does not list any area's registers. Registers are addressed by name
through a generated register map, never by a literal offset, so a register table
copied into this book would be a second source that nothing keeps in step. The
generated map for an area is the authority; see
`vault/handbook/dv/registers-by-name.md` for why this is a rule rather than a
preference.
