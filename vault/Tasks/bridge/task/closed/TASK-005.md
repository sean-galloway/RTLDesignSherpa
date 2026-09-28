# TASK-005: Master-unique transaction IDs: prepend the master index

> Migrated 2026-09-27 from `vault/Tasks/bridge/closed.md` as **BRIDGE-016** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-09-10, same day. Every fabric ID is {master index,
master id}; the reorder test proves it at the slave ports and its mutation went
RED; full bridge regression 264/264. Originally: open 2026-09-10 (Sean: "there
is supposed to be a unique id for every master, that gets prepended").
**Priority:** P1.

Inside the fabric every transaction ID becomes `{master index, master id}`:
the widest master's id_width plus `$clog2(NUM_MASTERS)` bits, zero for a
single master. Eight-bit masters behind a 16-master bridge give 12-bit IDs
at the slaves. The master adapter forms the prefixed ID on every fabric arm
(direct, width converter, Lite aligner); responses return with the prefix
and the adapter's existing low-bit select strips it. The package exports
`MASTER_ID_WIDTH` / `ID_PREFIX_WIDTH` / `XBAR_ID_WIDTH`; every other site
sizes from `width_utils.xbar_id_width`. The validator requires each AXI
slave's declared `id_width` to be at least the widened width and names the
number. The `bridge_id` routing sideband stays; the prefix is what makes
per-ID tracking sound across masters, which BRIDGE-015 needs.

*Consequence for tracking mode.* The in-order FIFO tracker requires the
slave to complete in AW/AR order across ALL IDs, which a compliant AXI slave
need not do. While every master presented the same IDs that contract held by
accident; the moment IDs became unique per master, a slave that serialises
per ID (the in-order BFM does) completed across masters out of request
order, and mix_b / mix_d tripped BRIDGE-010 in every cell. So with more than
one master, every real AXI slave now tracks by ID in `bridge_cam`
(`SlaveAdapterGenerator.use_cam`), regardless of `enable_ooo`; single-master
bridges, shim slaves and the subtractive slave keep the FIFO. Thirteen
multi-master variants, 22 adapters, switched. The BRIDGE-010 sim check
stays on the FIFO path, and its `$error` finally prints the IDs rather than
the ASCII of its own next sentence (the message was five string arguments).
The BRIDGE-011 overflow test now reads occupancy from the CAM's count.

**Downstream, done 2026-09-11.** The four FPGA-system bridges with more than
one master were regenerated with widened slave IDs, and everything their
slave ports touch is now sized from the bridge package rather than by hand:

- `bridge_ddr2_char_{rd,wr}` (two 8-bit generators -> 9 bits at pumice):
  `char_engine_block` gained `M_AXI_ID_WIDTH = bridge_ddr2_char_wr_pkg::
  XBAR_ID_WIDTH` for its pumice-facing ports, nets and latency histograms;
  `ddr2_char_macro` sizes its pumice nets and `pumice_top_geared.AXI_ID_WIDTH`
  from the same constant. The generators' own IDs stay 8 bits.
- `bridge_stream_{char,mon}_axil` (three and four 8-bit masters -> 10 bits at
  `desc_ram`): `stream_harness` sizes the desc-RAM nets and
  `sdpram_slave_axi4_axi4.AXI_ID_WIDTH` from `bridge_stream_mon_axil_pkg::
  XBAR_ID_WIDTH`. All three Genesys2 builds (perf, mon, obs) lint clean and
  the bridges' local tests pass at the new width. Their Makefile still pointed
  at the area's pre-move path and the local TB classes at the old slave
  width; both fixed.
- **LiteDRAM comparison flow: source-consistent, not rebuildable here.**
  `litedram_char_top` carries the 9-bit IDs and `litedram_hp.yml` asks for
  `id_width: 9`, but `build_board/gateware/litedram_core.v` is a generated
  core still at 8 bits and this machine has no LiteX environment to
  regenerate it. The harness lints clean without the core; the board build
  will stop on the 8-vs-9 port mismatch until the core is regenerated from
  the yml, which is the loud failure we want rather than a truncated index.

The pumice (ddr2-char) and Genesys2 stream builds were respun on the widened
bridges and came up fine (Sean, 2026-09-11). Only the LiteDRAM comparison
build is still pending its core regeneration.
