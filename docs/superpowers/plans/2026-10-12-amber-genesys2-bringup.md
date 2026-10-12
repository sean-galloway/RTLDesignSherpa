# amber pair-rig Genesys2 bring-up — plan (2026-10-12)

Owner directive 2026-10-12: val-clean gate passed (grid v2: 5/6 legs; the
two FULL-soak corners are filed as amber-mesi-l1 BUG-001/002 and are
pre-existing) — proceed to the Genesys2 board with the pair rig. Readout
via `monbus_tally_axil` over the standard UART→AXIL host bridge, following
the pumice/kestrel/stream board-wrapper pattern.

## System (mirrors dv/tb/amber_pair_rig_tb.sv, BFMs replaced by RTL)

```
uart (host) → uart_axil_bridge → bridge_amber_axil (generated decoder)
   ├─ harness_csr     (ctrl/status: per-gen run/kick, done/busy, cycle ctr)
   ├─ traffic_gen0 cfg/status   (per-core stimulus engine)
   ├─ traffic_gen1 cfg/status
   ├─ tally cnt_*     (monbus_tally_axil count readback)
   └─ tally cfgr_*    (tally config/status)

traffic_gen0/1 → cpu_req GAXI (packed {addr,we,be,wdata}) →
   u_amber0/u_amber1 (amber_top = l1_core + axi4_master_rd/wr + monbus_arb)
   → amber_pair_fabric (c0/c1 masters, coh sidebands, peer_state)
   → mem_* AXI4 → u_mem (sdpram_slave_axi4_axi4, BRAM)

amber0/1 monbus → rig merge arbiter → monbus_axil4_axil4_group
   → monbus_tally_axil rec_* ingest
```

- Geometry: s128w4l64b64 (the pair-rig FULL geometry).
- Memory: 512 KB sdpram (MEM_DEPTH param); working set region configured
  via the traffic-gen address mask.
- Clock: 90 MHz (MMCM pattern from stream_genesys2_top); board 200 MHz
  differential oscillator via IBUFDS.
- Reset: board pushbutton → two-flop sync (stream pattern).

## Files to create (new area: projects/fpga-systems/Genesys2/cache-ip/amber/)

| File | Basis |
|---|---|
| `rtl/amber_pair_genesys2_top.sv` | copy of `dma-ip/stream/rtl/stream_genesys2_top.sv` clock/reset shell |
| `rtl/amber_pair_harness.sv` | stream_harness.sv integration template |
| `rtl/amber_traffic_gen.sv` | new: AXIL-CSR-driven cpu_req GAXI master (LFSR addr within masked region, R/W mix, TRANS_COUNT stop, accepted/rsp counters) |
| `rtl/bridges/configs/bridge_amber_axil.toml` | copy `bridge_stream_char_axil.toml` |
| `rtl/bridges/generated/bridge_amber_axil/` | generated (house bridge generator) |
| `fpga/constraints/amber_pair_genesys2_top.xdc` | copy stream xdc, adapt pins unchanged (same board) |
| `Makefile`, `build-bringup/Makefile` | stream area Makefiles |
| `fpga/tcl/{create_project,build_all,synth_only}.tcl` | stream tcl verbatim |
| `host/amber_board.py` | tiny pyserial driver: config regs, run, poll done, dump tally bins |

## Validation ladder

1. Verilator lint/elab of the top (house lint flow) — must be clean.
2. Cocotb smoke of `amber_pair_harness` (optional if time; host bridge
   replaced by a BFM master in sim): gens run 1k txns, tally counts move,
   quiescence clean. SKIP for v1 if the bitstream path is slow — DV
   already proves the caches/fabric/memory; the new RTL is the gens +
   wiring.
3. Vivado synthesis → bitstream via the per-build Makefile.
4. Board: program via JTAG/UART (board registry:
   `projects/fpga-systems/bin/boards/genesys2.py`, UART serial AU05X8RM);
   run `host/amber_board.py`: configure both gens, run 100k txns each,
   read tally bins (hits/misses/fills/snoops), compare against
   expectations, report.

## Decisions pinned

- D1: stimulus = bespoke RTL traffic gens (no soft-core CPU; kestrel
  integration is a later milestone). Deterministic LFSR seeds →
  reproducible tally counts.
- D2: on-board data correctness is NOT deeply checked (no golden model on
  the board); confidence comes from DV + tally/counter ratios + a directed
  "same-line ping-pong across both caches" smoke whose tallies are known.
- D3: no DDR3 (pumice territory). Shared memory is on-chip sdpram BRAM.
- D4: tally bins read over UART at 115200; record-ingest path exists in
  RTL but v1 host only polls counts.
- Diagrams (if any) follow the repo AGENTS.md house style
  (mem-ctrl-ip STYLE.md reference); v1 docs are text-only.

## Out of scope (v1)

- kestrel integration, on-chip data golden-check, record-stream host
  readout, performance counters beyond tally bins, DDR3 memory.
