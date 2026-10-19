# TASK-032: Genesys 2 harness for RAPIDS as the tile I/O (rapids_tile)

**Priority:** P2
**Status:** open -- 2026-10-19; injectors 1 (cell sender) and 2 (credit intake) built and unit-tested
**Owner:** sean galloway

## Why

The byte harness (`projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids`,
rapids TASK-019/020/023) drives `rapids_top`, the AXIS plane, with no tile
header. Everything rapids TASK-026/027/031 built (tile header, end-to-end
credits, straps, credit returns, desc intake, resync, stall checks) has only
been run in cocotb against `rapids_cxs_top` with Python cells. On a board
there are no cells: the harness has to BE the cells and cores, in RTL, on
the one CXS link per direction. That is most of the work (owner 2026-10-19:
"the injectors will need a fair amount of work").

## Shape

New flow `projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids-tile/`,
harness `rapids_tile_harness`, DUT `rapids_cxs_top` with `TILE_HDR` = 1,
`TILE_CREDITS` = 1 and the straps at their defaults (16 / 2, rapids
TASK-031). Kept from the byte harness unchanged: the UART/AXIL host path and
APB region, descriptor and control RAMs, `axi4_slave_rd_injector` (source
memory), `axi4_slave_wr_crc_check` (sink memory, per-channel CRC),
`char_run_timer`, MonBus capture. Replaced: the AXIS injector/checker pair,
by a tile fabric model on the two CXS links.

## The injectors (the bulk)

All harness-local RTL (they model tile endpoints, not AMBA), built from the
shared parts where they fit: `axis4_master_injector`'s LFSR/CRC engine,
`axis_to_cxs` / `cxs_master`, `cxs_slave` / `cxs_to_axis`,
`rapids_pkg::tile_hdr_pack`.

1. **Cell sender** (sink ingress): up to 16 cells (external slots 0-15),
   each with a strap counter starting at `TILE_LAND_FLITS`. A packet is a
   header beat (dst = RAPIDS, src = the cell, ptype mem, length, tag = sink
   channel) then at most `TILE_LAND_FLITS` - 1 LFSR beats; it starts only
   when the strap covers every flit. The header must not advance the LFSR,
   so the per-channel CRC still matches `axi4_slave_wr_crc_check`. CSRs:
   cell mask, cell -> channel map, beats per packet, packet count.
2. **Credit intake** (`m_tile_credit_*`): parse each return (dst -> slot,
   class, add / set, count) into the strap counters. Checks: return to an
   unknown slot, a counter above its strap, a `set` outside a resync, and
   at the end every strap whole again (sent == returned). Sticky errors and
   per-cell sent / returned counts in CSRs.
3. **Core sender**: up to 4 control cores (slots 16-19), each with a
   `TILE_DESC_PER_CORE` strap, sending `desc` packets (tag = source channel,
   one 256-bit descriptor from a host-written table); class-1 returns refill
   it.
4. **Cell receiver** (source egress): `cxs_slave` -> header check (dst = the
   cell mapped to that channel, ptype, length) -> strip the header -> the
   per-channel payload CRC (`axis4_slave_pattern_check`'s). Each
   destination cell models a buffer: it advertises (`set`) at boot inside
   `SRC.TILE_ADV_WINDOW` and returns `add` as it drains, at a CSR-set rate,
   so a slow cell exercises the window hold.
5. **Ingress arbiter**: packet-atomic merge of credit packets (priority:
   a return never waits behind data), core `desc` and cell data onto the one
   sink-ingress AXIS -> CXS link.
6. **Tile controls**: `tile_quiescent` from a CSR (and an auto mode: high
   when every injector is idle and every strap whole), so the host can run
   `SRC.TILE_RESYNC` and channel resets on the board.

## Then

7. Harness CSR map (generated regmap, by name), `BUILD` ID word distinct
   from `RAPB`, `BUILD.TILE_STRAPS` cross-checked against the DUT's
   `TILE_STRAPS`.
8. cocotb self-check of the harness in sim (the board program in cosim):
   sink, source, both at once, cores, resync, a stalled sink.
9. Host flow (UART, `rapids_byte_io`-style), Makefile, xdc, bitstream,
   timing closure, board run.

## Order

Injectors 1+2 with a cocotb unit test each, then 5, then 4, then 3, then the
harness top and 6-8; the board last.

## Done when

- The harness self-check passes in sim: tile sink and source CRCs, every
  strap whole at the end, zero injector errors, a resync and a stall on the
  board program.
- The bitstream meets timing on the Genesys 2 and the same campaign passes
  on silicon.

## Progress 2026-10-19

`flows-rapids-tile/rtl/tile_cell_tx.sv` (one cell: one-channel
`axis4_master_injector` seeded seed ^ channel, a header beat per packet that
takes no LFSR step, strap counter charged at the header, `err_over_return`,
`err_pkt_too_big`) and `tile_credit_rx.sv` (decodes `m_tile_credit_*`, routes
by external slot, flags wrong ptype / source / slot / class, `cfg_hold`).
Filelist `filelists/tile_injectors.f`. Unit tests `dv/test_tile_injectors.py`
on `dv/tb_tile_cell_loop.sv` (two cells + intake, cocotb plays RAPIDS with
AXIS slave and GAXI master BFMs): stream, strap_gate, bad_returns, too_big at
LAND 16 and 8, 8/8. Mutations: header steps the LFSR (stream), no charge
(strap_gate), no class check (bad_returns), all caught.
