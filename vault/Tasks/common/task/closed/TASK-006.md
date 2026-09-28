# TASK-006: Multi-byte CRC support

> Migrated 2026-09-27 from `vault/Tasks/common/closed.md` as **COMMON-008** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-08-09 — premise false; the capability already exists
(spotted by Sean while reviewing the open list)

The task claimed "dataint_crc.sv processes one byte per cycle" and asked for
a 2/4/8/16-byte-per-cycle option. The module's own header refutes it:
**Throughput: CHUNKS bytes per cycle**, CHUNKS = DATA_WIDTH/8. The
architecture is a cascade of per-byte XOR-shift stages with `cascade_sel`
one-hot selecting the tap for a partial final beat — so any instantiation
processes DATA_WIDTH/8 bytes every cycle, and DATA_WIDTH is a free
parameter (default 64 = 8 bytes/cycle; 128/256 give 16/32).
`rtl/amba/shared/axi4_slave_wr_crc_check.sv` already consumes it exactly
this way (32-bit beats, cascade_sel one-hot on the last valid byte).

The task text likely predates the cascaded rewrite and was migrated without
re-verification — same lesson as COMMON-010 and the COMMON-021 cover rows:
re-read a long-lived task's premise against the tree before working it.

One honest residual, recorded not tasked: at very wide DATA_WIDTH the
cascade is a serial combinational chain (one CRC stage per byte), so timing
at 32 bytes/cycle may want an unrolled/parallel formulation. That is a
synthesis-timing question with no consumer today; whoever hits it opens a
fresh task with the failing clock target in hand.

---
