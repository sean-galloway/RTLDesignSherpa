# TASK-018: Transaction-ID remap: fabric ID = {master index, slot}

**Status:** CLOSED 2026-10-19, same day. `bridge_id_remap` in every master
adapter whose ID is wider than `$clog2(max_outstanding)`; full clean bridge
regression 765/765, generator unit tests 203/203, the table proven unbounded
(PDR) with ten mutants each caught by a named property.
**Priority:** P1.
**Filed from:** Sean, 2026-10-18: "ID growth width: we should have
master/slave id's for the fabric with maybe 32-deep cam to map the 8-bit ID's
to 5 bits", then the agreed design: a per-master remap table per direction,
`max_outstanding` entries, fabric ID `{master index, slot}`, CAM
match-or-allocate on the request, indexed restore on the response. Taken up
after R interleaving (PRD FR-9), whose per-ID converter state made the width
an area problem: `bridge_5x3_channels` grew from 30,835 to 47,850 LUTs at
11-bit fabric IDs (2048 per-ID entries in the CPU master's 64-to-256 read
converter).

## What changed

- `rtl/bridge_id_remap.sv` (hand-written, `filelists_static/bridge_id_remap.f`).
  A request's ID is matched against the live entries; a hit reuses its slot
  (one ID stays one fabric ID, so it stays ordered at the slave), a miss
  takes the lowest free slot. `req_ok` refuses an ID live toward another
  slave, or with other metadata (the trace bit on trace-echo ports); `full`
  at `max_outstanding`. The slot in B / R restores the ID. The pop is
  registered: counting it on the same cycle, behind the path arbiter, was
  the slowest path in the adapter (-0.445 ns reg-to-reg on the 5x3).
- Generator: `width_utils.remap_slot_width / id_remapped /
  fabric_local_id_width`, and `xbar_id_width` is now index bits plus the
  widest local ID. The adapter instantiates the table in place of the per-ID
  target table, drives `xbar_axi_{aw,ar}id` from the slot and has the B / R
  mux select the slot. A read-return-atomic port keeps its ID (its atomic AW
  answers on B and R under one AWID). The filelist pulls the table when a
  master remaps. `MASTER_ID_WIDTH` is the widest master-local ID.
- Found on the way: slave-port protocol checkers were bound at the slave's
  DECLARED `id_width`, a floor, not the pins' width; with the fabric ID
  narrowed that broke every `bridge_5x3_channels` build. They bind at
  `xbar_id_width` now.
- Fixtures: nine test configs widen their master IDs from 4 to 8 bits so the
  regression runs the remap (2x2_rw, 2x2_rw_lat, 2x2_rw_cdc, 2x2_axi5 with
  trace, 2x2_axi3_masters, 3x2_rw_mcdc, 4x4_rw, 1x2_rd_axi5w single-master,
  mix_e beside a kept 4-bit master); 2x2_rw_depth remaps at 4 outstanding.
  The other multi-master fixtures keep 4-bit IDs, so the kept-ID path stays
  covered.

## Evidence

- `formal/bridge/bridge_id_remap`: prove (abc pdr) PASS, bmc 20 PASS, cover
  PASS. Mutants: free ignores live, hit ignored, target ignored, meta ignored,
  wrong restore, live never clears, full late, meta not restored, pop slot
  lost, pop counted early -- each FAIL on its property.
- `dv/tests/test_bridge_2x2_rw_id_remap.py`: three times as many IDs as slots
  from both masters at once, then runs of one ID; checks every word and, at
  all four ports, that an in-flight fabric ID belongs to one master ID and
  vice versa. Fails on the hit-ignored and free-ignores-live mutants.
- `make clean-all && make run-all-full-parallel`: 765 passed, no reruns.
- Artix-7 -1, 10 ns (HAS 6.4): 5x3_channels 47,850 -> 25,304 LUTs, 50,894 ->
  23,845 FFs, -0.309 -> +0.089 ns; 4x4_rw (now 8-bit masters) 44,627 LUTs,
  -0.024 ns, worst path not in the table; mix_e 16,036 LUTs, +0.111 ns.

## Left as is

- The AXI5 `unique` echo still keeps a bit per ORIGINAL ID (256 per
  direction at 8 bits). It could ride the remap metadata, but the write-only
  atomic filter answers some B locally, outside the table.
- The FPGA-system bridges (Genesys 2, Nexys A7) are regenerated separately;
  where their masters are wider than a slot, their slave-side IDs narrow, and
  whatever is sized to those ports follows.
