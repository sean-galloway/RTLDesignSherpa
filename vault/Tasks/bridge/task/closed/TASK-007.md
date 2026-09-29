# TASK-007: A native-AXI5 fabric

> Migrated 2026-09-27 from `vault/Tasks/bridge/closed.md` as **BRIDGE-018** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-09-13. The gap was two features, and both now ride
the fabric natively: **Memory Tagging** (`mte`: AWTAGOP/AWTAG, WTAG/
WTAGUPDATE, BTAG/BTAGMATCH, ARTAGOP, RTAG/RTAGMATCH) and **read-data
chunking** (`chunking`: ARCHUNKEN, RCHUNKV/RCHUNKNUM/RCHUNKSTRB). They join
the one sideband table (`bridge_pkg/sideband.py`) with widths that scale
with the data bus (`field_width`, `fit_expr` -- the width-independent
aw/ar/b structs size tag fields for the widest port and adapters/crossbar
zero-extend or slice explicitly). Rules: `mte` is connectivity-gated like
poison (a dropped tag op changes the write's meaning); `chunking` is
droppable (ARCHUNKEN is permission -- an AXI4 slave answers unchunked);
both need >= 128-bit ports. The fabric carries and never interprets them:
tags ride with their beat, BTAGMATCH returns by bridge id, chunked R beats
route by ID and free on RLAST in any order. Fixtures `bridge_2x2_axi5_native`
(128-bit, every feature, two masters contending) and `bridge_1x2_rd_axi5c`
(chunking native to an AXI5 slave, dropped at an AXI4 one); directed tests
`test_bridge_2x2_axi5_native_mte_chunk` (Transfer/Match/Update writes land
and report through the RDS-DV slave BFM's new tag store, Transfer reads
return tags, chunked reads carry RCHUNKV/RCHUNKNUM per beat) and
`test_bridge_1x2_rd_axi5c_chunk`. RDS-DV: `axi5_tag_store`, per-beat
`wtag`/`tagupdate`, Match compare (was a stub returning 1); then (#81,
same day) `chunk_order` on the slave read BFM, real RCHUNKSTRB, master
reassembly by RCHUNKNUM with `wire_index`, and the checker's chunk and
tag-width violations recorded -- so phase 6 of the native test returns
every chunked burst REVERSED on the wire and shows the fabric routes the
beats by ID and frees on RLAST regardless (24 bursts per master at full). Still not
carried, because no library endpoint has them either: AxLOOP, QoS accept,
SMMU untranslated, stash/CMO (rtl-amba AXI5 README). HAS 4.4, MAS 2.10.
**Was:** open 2026-09-11 (split out of BRIDGE-014 when its master-protocol
half closed)
**Priority:** P3. No feature anyone has asked for needs it.

The crossbar is AXI4-shaped inside, with the AXI5 sideband riding alongside
in the channel structs (BRIDGE-002 A5-2). That covers every AMBA5 feature
delivered so far -- interop sideband, native sideband, atomics of every
class, poison, the Lite and APB5 ports on both sides (BRIDGE-014). What it
cannot express is a feature whose semantics change the fabric's own rules:
read-data chunking (per-beat ordering inside a burst), MTE tags with their
own ordering, or anything that needs the crossbar to reason about AXI5
transaction attributes rather than carry them. If one of those becomes a
requirement, this is where it goes: the structs, the crossbar mux, both
adapters' tracking paths and the response mux all change together.

Not owed until a consumer appears. Related: [[BRIDGE-002]], [[BRIDGE-014]]
(both closed).

---

## Pre-migration ledger: projects/components/fabric-gen-ip/bridge/TASKS.md (retired 2026-09-10)

The component's own task file predated the vault and was folded in here, one
line per item with its disposition. It described the generator as of 2025-11;
everything below that was "Planned" either happened under a BRIDGE-0xx task,
is superseded, or moved to [[BRIDGE-017]] / [dropped](../../INDEX.md) (dropped/ in each lane).

| Legacy | Title | Disposition |
|---|---|---|
| TASK-000A | AXI4 interface wrapper integration | Complete 2025-11-04 |
| TASK-000 | Intelligent width-aware routing (4 phases, per-slave arbitration) | Complete 2025-11-04 |
| TASK-000B | slave_select reversion and multi-master routing fixes | Complete 2026-05-13 |
| TASK-001 | APB converter | Done: `axi4_to_apb4_shim` (+ apb5, BRIDGE-002 A5-3c) |
| TASK-002 | Channel-specific master end-to-end testing | Done: `bridge_1x2_{rd,wr}*` fixtures and generated tests |
| TASK-003 | Width converter integration testing | Done: mixed-width fixtures, `bridge_1x2_rd_axi5w`, converters suite |
| TASK-004 | CSV generator documentation | Done: bridge HAS/MAS (generated, house pipeline) |
| TASK-005 | Performance characterization | Not done -> [[BRIDGE-017]] |
| TASK-006 | Address decode documentation | Done: MAS ch02 address decode |
| TASK-007 | Error handling / response routing documentation | Done: MAS ch02 response routing, BRIDGE-009/010/011 |
| TASK-008 | WaveDrom timing diagrams | Done: MAS/HAS diagrams (mermaid); wavedrom generators in handbook |
| TASK-009 | PlantUML architecture diagrams | Superseded by the mermaid set in the HAS |
| TASK-010 | Synthesis and implementation guide | Not done -> [[BRIDGE-017]] |
| TASK-011 | Generator id_width + prefix handling (bugs A/B/C) | Closed 2026-04-30 |
| TASK-011b | Replace hand-coded arbiters with standard components | Done: BRIDGE-005 request arbiter |
| TASK-012 | AXI burst optimization | Dropped (no defined target) -> dropped.md |
| TASK-013a | Outstanding transaction support | Done: AW/AR tracking FIFOs, BRIDGE-011 not-full gating |
| TASK-013b | Timeout detection | Done: `_mon` variants' AXI monitors report timeouts |
| TASK-014 | APB3 to APB4 bridge | Dropped (no consumer) -> dropped.md |
| TASK-015 | AXI4 <-> AXI4-Lite converter | Done: `axi4_to_axil4_{rd,wr}` (+ axil5) |
| TASK-016 | Async clock domain crossing | Not done -> [[BRIDGE-017]] |
| TASK-017 | QoS with aging counters | Not done -> [[BRIDGE-017]] |
| TASK-018 | CAM-based response routing (optional) | Done: `enable_ooo` slaves use `bridge_cam`; repaired under BRIDGE-015 |
| TASK-019 | Pipeline FIFOs for high-performance crossbars | Not done -> [[BRIDGE-017]] |
| TASK-021 | Testbench and test file automation | Done: `--generate-tests` emits TB class + tests per fixture |

<!-- Moved from vault/Tasks/amba/ 2026-09-14: a bridge task, filed under amba -->
