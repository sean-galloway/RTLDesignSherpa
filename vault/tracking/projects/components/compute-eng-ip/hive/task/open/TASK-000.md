# TASK — hive Phase 1 RTL: finish the five blocks and close the CN-04 rotation issue

**Status:** open · **Priority:** high · **Filed:** 2026-10-13 · **Area:** projects/components/compute-eng-ip/hive

## 2026-11-25: gatling replaces the SERV monitors; renamed to hive

Owner: "in hive I got rid of the serv cores and replaced them with a single
gatling for four compute engines". Owner answers the same day: four compute
engines on a 2x2 delta mesh; gatling is a monitor like the SERVs (context
*n* monitors engine *n*); the component and this tracker area are renamed
`hive-serv` -> `hive`, and `rtl/serv_monitor/` -> `rtl/engine_monitor/`.
PRD 0.3, the HAS/MAS, CLAUDE.md and the testplans are updated.

What this voids or changes below:
- `vendor/serv/` is no longer used by HIVE (nothing else in the repo uses
  it; removing it is a separate decision).
- Next step 2 (`serv_monitor.sv` top with the vendored `serv_top.v`) is
  void. Its replacement is `engine_monitor_top.sv`: `gatling_core` +
  `gatling_mem_bram` (4 KB per context) + four per-engine peripheral sets,
  with peripheral-window accesses routed by the issuing context
  (MAS ch02 `03_engine_monitor.md`, testplan `hive_engine_monitor`,
  SM-07 rewritten and SM-08 new). `local_mem` (SERV buses) is unused.
- `test_hive_engine_monitor.py` (renamed from `test_hive_serv_monitor.py`)
  still skips; its scenario bodies assume the v0.2 per-tile SERV wrapper
  and must be reworked before the skip is removed.
- The control network's `SLAVE_COUNT` default (4) is now the full count, not
  a Phase-1 bring-up size.
- Status at the rename (gate, from clean): axis_cda_master, descriptor_gen
  and ctrl_network PASS; engine_monitor and c_loader SKIPPED (no top RTL).
  ctrl_network passes because the test logs CN-04 as a known issue and
  returns before CN-05..07 (it no longer fails at CN-05 as written below).

## Where this was left (session ran out of context mid-bring-up)

Phase 1 of the HIVE RTL started 2026-10-13: cores acquired, scaffold + five
testplans written, five TDD coder agents dispatched. The agents wrote ALL
tests and MOST RTL, then died on the account's weekly subagent quota; the
parent agent finished integration inline.

### Green (working tree, NOT yet committed)
- `vendor/serv/` — SERV 1.4.0 vendored (ISC, PROVENANCE.md)
- `vendor/vexriscv/` — HIVE-C netlist generated from VexRiscv master @ baf7dc8
  via `hive/bin/generate_hive_cores.sh` (sbt 1.10.7 forced over upstream's
  1.6.0 for Java 21; the 1.0.1 tag's sbt 0.13 toolchain cannot run here)
- Scaffold: rtl/dv layout, 4-line Makefiles, `hive` area in bin/filelists.toml,
  conftest, five testplans under dv/testplans/
- **descriptor_gen** — gate+func GREEN (two fixes: fifo_sync mux-mode output,
  DG-04 full-queue expectations)
- **axis_cda_master** — gate+func GREEN (ReadOnly-phase import + 1 ps phase
  advance fix in the test)

### Red / incomplete (do NOT commit the tree wholesale)
- **ctrl_network** — CN-01..03 PASS. CN-04 (round-robin rotation) serves
  [0,1,2,0]: slave 0 re-arms after pop, slave 3 never served. CN-05..07 are
  blocked by CN-04's leftover fifo state. Root cause is the choreography
  between the arbiter's grant history (`r_last`) and the up-fifo sync windows;
  the VCD forensics are in the parent session's wire log (windows 9-15,
  /tmp/ctrl*.vcd may still exist). The test currently logs CN-04 as
  KNOWN-ISSUE and then fails at CN-05 — gate is RED.
- **serv_monitor** — submodules exist (traffic_counter, trigger_logic,
  axis_injector, ctrl_net_slave, local_mem); the **top serv_monitor.sv was
  never written** (agent died mid-block).
- **hive_c_loader** — test exists; **no RTL** (netlist landed after the agent
  died, so the block is now unblocked).

## Repo bug to file separately (tooling/common)
`rtl/cdc/gaxi_fifo_async` at DEPTH=2: all four command FIFOs stuck `full=1`
with write pointer == read pointer after light traffic (captured: wr=03/rd=03,
wr=00/rd=00, full=1, write-domain synced rd pointer diverged/stale). Also
observed: read-valid stuck high after early pops at DEPTH=4. Workaround in
place: `rtl/control_network/hive_cdc_fifo.sv` (textbook binary-pointer +
Gray-cross, combinational rd_valid, transactional full lookahead matching
counter_bin semantics — note: counter_bin's `next` is enable-gated; an
unconditional ptr+1 in full lookahead asserts one slot early). Revert
hive_ctrl_network to gaxi_fifo_async after the library fix, and re-run the
hive CN suite as the regression.

## Next steps (in order)
1. ctrl_network: fix the CN-04 rotation (arbiter grant-history vs fifo sync),
   then CN-05..07 pass as written. File the gaxi_fifo_async bug with the
   evidence above.
2. ~~Write serv_monitor.sv top~~ (void 2026-11-25, see the top section):
   write `engine_monitor_top.sv` (gatling core + memory + four per-engine
   peripheral sets; MAS ch02_blocks/03_engine_monitor.md, the
   hive_engine_monitor testplan).
3. Write hive_c_loader.sv (vendor/vexriscv/VexRiscv.v iBus/dBus cmd/rsp to
   32 KB BRAM, AXIL slave loader, kestrel load-then-run; see testplan + MAS
   decision: kestrel pattern).
4. Wire per-block filelists into rtl/filelists/hive_all.f; run the full
   gate/func sweep (`make run-all` in dv/tests or per-file pytest); commit.
5. Update PRD/CLAUDE status lines (they say "no RTL yet").

## Verification commands
```bash
source env_python
cd projects/components/compute-eng-ip/hive/dv/tests
python -m pytest test_hive_descriptor_gen.py test_hive_axis_cda_master.py -q   # green
python -m pytest test_hive_ctrl_network.py -q -x -s -k gate                     # red at CN-05
```

## Decisions already made (owner, recorded in HAS/MAS v0.2 — do not relitigate)
AXIS-only communication; kestrel loader; dual-flop taps; mailbox register-file
default; mailbox+descriptor_gen (custom instruction rejected); quiesce via
fabric IDLE into a PeakRDL register; delta IS the fabric.
