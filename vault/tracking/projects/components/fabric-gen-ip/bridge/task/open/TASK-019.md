# TASK-019: Genesys 2 bridge stress model -- AXI3/AXI5, then AXI-Lite / APB / WB4 shells

**Date:** 2026-10-19
**Priority:** P2
**Status:** OPEN (phases 1 and 2a-2e done on the board: AXI4, AXI3, AXI5 incl. sideband, poison, IDUNQ, atomics, MTE, and third-party IP on LiteDRAM in build-xil and build-xmix; phase 3 next)
**Owner:** unassigned
**Where:** `projects/fpga-systems/Genesys2/bridge-stress/` (PRD.md), cores in `rtl/amba/shared/axi_stress_*.sv`

## Goal

Silicon validation of the bridge generator on every protocol it builds, with
nothing else on the board: one stress master per DUT master port, one stress
slave per DUT slave port, every byte / ID / response / burst shape checked at
both ends.

## Done (phase 1, 2026-10-19)

- Protocol-neutral cores (master generator + per-ID ordered scoreboard; hash
  slave with reorder / interleave / latency / throttle / SLVERR window), the
  AXI4 shells, regblocks, the generated harness, the Genesys 2 build, the host
  library and board program.
- `val/amba/test_axi_stress_pair.py` (21 cells incl. eight fault injections),
  `dv/tests/test_bs_harness.py` (nine profiles, the board's host code over the
  sim UART), board 27/27.
- Found bridge BUG-018 and converters BUG-010.

## Done (phase 2a, AXI3, 2026-10-19)

- `axi3_{master,slave}_stress`: the generator's LEN_MASK cuts bursts to 16
  beats; the write core carries each beat's WID; the AXI3 slave checks it
  (`ERR_S_WID`). Pair test: AXI4 and AXI3, 42 cells at full level, nine
  faults incl. a flipped WID.
- `bridge_bs_axi3` / `build-axi3` (the CDC ports stay AXI4: no AXI3 CDC in
  the generator), harness generator protocol-aware, board 27/27 and a
  15-minute soak 168/168.
- Found and fixed converters BUG-011 (unaligned chopped INCR).

## Done (phase 2b, AXI5 sideband + poison, 2026-10-19)

- Cores: generic request / response sideband and poison hooks (`SB_MASK`,
  `RSB_MASK`, `POISON`; fixed `SB_M_*` layout in `axi_stress_pkg`). Request
  fields are `f_sb(start address)`; responses echo the request's TRACE
  (`f_rsb`); poison is `f_poison(beat address)`, 1 in 2^n. Nothing is
  stored. Two new codes: `ERR_S_SB`, `ERR_M_SB` (err_mask is now full).
  A slave tells sideband-carrying masters from the rest by the fabric's
  master-index ID field (`SRC_LSB` / `SRC_W`, cfg `sb_src`).
- `axi5_{master,slave}_stress` on the `axi5_*` channel modules (NSAID,
  TRACE, MPAM, MECID, POISON). Pair test: AXI4 / AXI3 / AXI5, 63 cells at
  func, fourteen faults on AXI5 incl. flipped ARTRACE, AWMECID, WPOISON,
  RTRACE, RPOISON, BTRACE.
- `bridge_bs_axi5` / `build-axi5`: a poison clique (cpu -> mem0, mem2), a
  sideband mesh where mem1 takes native (dma), width-converted (io) and
  AXI4 (acc) requests at once, AXI4 CDC ports. Harness generator takes the
  AXI5 pin set and ID layout from the bridge generator itself. Harness sim
  9/9 profiles; board 27/27 and a 15-minute soak 174/174 (~11.1 M bursts);
  WNS +0.066 ns.
- Learned: a trace-capable bridge master port echoes AxTRACE itself
  whatever the slave (bridge BUG-010), and asserts in sim that a
  trace-capable slave echoes it too; the stress slave now does.
- Filed bridge BUG-019 (unaligned INCR steps in several converters).

## Done (phase 2c, IDUNQ + atomics, 2026-10-19)

- IDUNQ: masters mark a burst unique (address hash) only when its ID has
  nothing outstanding and hold the ID until it completes; slaves check the
  rule on the IDs they see; BIDUNQ / RIDUNQ checked. The ord table exposes
  the key's tail (`alloc_tail_vec`) for this. Pair test faults: flipped
  RIDUNQ / BIDUNQ, a forced ARIDUNQ on a busy ID. Harness sim through the
  bridge 9/9.
- Atomics: one-beat Store / Load / Swap / Compare by address hash on IDs
  with the MSB set, held until the ID is free (incl. a read-return owed);
  stateless "original value" = the read hash; the slave queues the R beat
  behind its W beat and `axi_stress_r_merge` puts it on R between read
  bursts; the master steers RID-MSB beats to its write core. Faults: a
  corrupted read-return, a reserved AWATOP. DUT: atomics on the cpu ->
  mem0 / mem2 clique (cpu IDs 4: an rw atomic master is not remapped).
- Limits stated (stress PRD "Limits"): the bridge's 8 read-return atomics in
  flight per slave port (now documented in the MAS / HAS / module doc; bridge
  TASK-020 makes it a key), no limit on atomic masters, and the model's own.
- Harness sim 9/9 on all three builds; the harness TB now counts atomics,
  IDUNQ and poison at the pins and fails a run where they did not happen.
  Board 27/27 and a 15-minute soak 172/172; WNS +0.298 ns, 92.1k LUTs.

## Done (phase 2d, MTE, 2026-10-19)

- Stateless tag contract (axi_stress_pkg): AxTAGOP / WTAG / WTAGUPDATE /
  RTAG / BTAGMATCH as hashes of addresses both ends know; window `mte` for a
  far end that answers tags (the bridge's DECERR answers none). Pair test:
  four tag faults caught (23 on AXI5).
- Every per-address pick moved to the keyed hash `f_hk`: XOR-keyed xorshift
  picks were correlated, and the first MTE run never failed a tag match.
- bridge_bs_axi5's cpu clique is 128-bit and carries every AXI5 feature.
  Sim 9/9 on all three builds, board 27/27, soak 172/172; WNS +0.020 ns.

## Done (phase 2e, build-xil / build-xmix: third-party IP, 2026-10-20 to 10-22)

- Real memories: window `mem` (writes carry the read hash at `f_maddr`, so
  they are idempotent) and cfg `fill`; each run is fill GO, run, read sweep.
  `val/amba/test_axi_stress_mem.py` (BFM memory, 3 widths) catches one
  flipped byte at its word.
- Generator `[harness] vendor` brings ports out as pins; the configuration
  bridge gains ext0 / ext1 AXI4-Lite windows; EXT_STS0..3 carry IP status.
- `bs_genesys2_xil_top`: MIG, dual-port BRAM controller, AXI Traffic
  Generator, AXI CDMA, a protocol checker per memory link. Board 27/27 with
  mig excluded.
- Found: bridge BUG-020 (W waits on the slave's AW handshake; the CDMA
  register slave deadlocks it). MIG wedges on this board (spurious
  `app_rd_data_valid` within ~35 us of a write sweep, ILA); owner decision
  2026-10-20: LiteDRAM DDR3 replaces MIG, as in the fabric benchmark.
- BUG-020 fixed with the stress-slave `w_first` gate (AWREADY held until
  WVALID): board `w_first` 20/20, CDMA on ext1 with no AW skid.
- `build-xmix`: AXI3, AXI4 and AXI5 masters together with the third-party
  IP.
- Found and fixed on the way, every one with a board re-run:
  - converters BUG-012: a `narrow` write into mem1 hung about once in 50
    runs. After the fix, 300/300 with zero Ocelus records.
  - converters BUG-013 (`axi4_to_axi3_wr`, BUG-020's class at AXI3 slave
    ports).
  - bridge BUG-018 (width-converted FIXED / WRAP / narrow / unaligned
    bursts). Its fix removed the host's `path_caps` limit, so `--full-axi`
    is a no-op.
  - bridge BUG-019, BUG-022, BUG-023 and BUG-024.
- Final board, rebuilt with the `bridge_id_remap` timing fix (f02b67aef),
  every profile x seeds 1-3, 20000 bursts per master direction:
  - build-xil: 30/30, max latency 15,866 cycles, routed WNS +0.050 ns.
  - build-xmix: 30/30, max latency 20,337 cycles, routed WNS +0.086 ns.
  - CSVs: `bridge-stress/reports/board/bridge_bs_{xil,xmix}_20261022_22*`.

## Remaining

| Phase | Work |
|---|---|
| 3 | Single-beat shells for `axil` / `axil5`, `apb` / `apb5` (slaves in offset mode: the bridge hands an APB slave a window offset) and `wb4`, plus the DUT `bridge_bs_mixed_b.toml`. 3a done 2026-10-23: `axil4_{master,slave}_stress` (cores built single-beat via `LEN_MASK = 0` and the new `SIZE_FIXED`; per-direction issued-ID FIFO in the master), pair test `axil4` cells 11/11 at func with 5 faults. 3b done 2026-10-23: `axil5_{master,slave}_stress` (IDs on the bus, out-of-order across IDs, TRACE and POISON), `axil5` cells 15/15 at func with 12 faults. 3c done 2026-10-23: `apb{4,5}_{master,slave}_stress` (one bus round-robin, `{write, ID}` response FIFO, slave in offset mode, APB5 slave waits for PWAKEUP), `apb4` / `apb5` cells 4/4 each at func with 5 faults, the request faults fired at the setup phase. 3d done 2026-10-23: `wb4_{master,slave}_stress` (pipelined and classic; in-order termination across the two cores by a direction FIFO), `wb4` / `wb4c` cells 8/8 each at func with 5 faults, pipelined runs overlapping 4 transfers. Next (3e): the harness generator for these protocols, the `bridge_bs_mixed_b` DUT, its build and the board. |

The earlier "re-run `--full-axi` once BUG-018 is fixed" row is done: the
BUG-018 fix removed the converted-path limits, and the 10-22 runs above use
none.
