<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# bridge — closed

## BRIDGE-006 — the test generator reverts hand-fixes to its own output
**Status:** closed 2026-08-31 (opened 2026-08-31)
**Priority:** P2
**Owner:** TBD

`bridge_generator.py --generate-tests` overwrites `dv/tests/` and
`dv/tbclasses/`, so any fix made in the generated files is reverted the next
time anyone regenerates. That is working as designed for generated code; the
defect is that real fixes keep landing in the output instead of the template,
and nothing detects the reversion.

**Found how.** The Genesys 2 stream area ran `regen_bridges.sh` as the PREBUILD
for `make bitstream`, so building a bitstream regenerated the tests. Three
rounds of committed fixes were silently reverted (33ac787e, 90bca4c1,
bd79af49). That area is fixed: the generator no longer emits an import that is
a SyntaxError on a path containing `fpga-systems`, and `regen_bridges.sh` no
longer writes DV at all (guarded by
`Genesys2/stream/bin/tests/test_bridge_dv_not_generated.py`).

**What is still open, in this component.** `projects/components/bridge/dv/tests/`
has the same shape of drift. Diffing a fresh generation against the committed
files, every `test_bridge_*.py` differs in two lines:

```
committed:  from TBClasses.shared.utilities import get_repo_root, sim_build_path
            sim_build = sim_build_path(tests_dir, sim_build_name)
generator:  from TBClasses.shared.utilities import get_repo_root
            sim_build = os.path.join(tests_dir, 'local_sim_build', sim_build_name)
```

That is the per-session `SIM_BUILD_ROOT` work from f01853fe, applied to the
output and not to `jinja_templates/bridge_test_file.py.j2`. A regeneration of
this component today reverts it and puts every bridge test back on a shared
build directory — the concurrency hazard f01853fe was written to remove. The TB
classes are clean; only the test runners drifted.

**Done looks like:** the template emits `sim_build_path`, every bridge tree is
deleted and regenerated per CRITICAL RULE #0, the suite is green, and a fresh
generation diffs clean against the committed files. The last clause is the one
that matters — it is the check that was never being run.

### Resolved 2026-08-31

`jinja_templates/bridge_test_file.py.j2` now emits `sim_build_path(tests_dir,
sim_build_name)` and imports it, at all three `run()` sites. The hand-applied
fix from f01853fe is in the generator, so a regeneration can no longer revert it.

Full CRITICAL RULE #0 regeneration: `make regen` (clean + all), 23 batch entries
-> 35 RTL trees + 39 test files, nothing deleted.

**The acceptance criterion was the diff.** After regenerating, the ONLY dirty
file in the bridge area was the template itself -- the generated output is
byte-identical to what was committed. That is the whole proof: the generator now
produces what was previously being patched into its output by hand. Zero test
files still hand-join `tests_dir/local_sim_build`.

Suite green: 38 passed, 0 failed (1:22:05).

Not carried over from the sibling defect: `regen_bridges.sh` in the Genesys 2
stream area no longer writes DV at all (17ef6f2f), so that area's five bridge
tests are hand-maintained and unaffected by this template. The two areas are
deliberately different now -- this one regenerates its tests, that one does not.

## BRIDGE-005 — generated xbar had no request arbiter: concurrent multi-master traffic OR-merged
**Status:** closed 2026-08-25 (opened 2026-08-25)
**Priority:** was P1 — silent data/address corruption under contention

The crossbar generator's multi-master routing OR-merged every master's
request contribution per slave with no grant: two masters presenting
AW/AR to one slave in the same cycle merged field-by-field (observed
addr = A|B arriving at a slave neither master addressed), and both saw
the ORed ready. Was a documented deferral in crossbar_generator.py.

**Shipped (same day):**
- Per-slave round-robin AW and AR arbiters, grant locked until the
  handshake completes; one-hot gated field muxes; grant-gated readies.
- Per-(master, width-path) W destination FIFO + per-slave W owner FIFO
  (slave AW-accept order owns the W channel) — replaced the per-pair
  occupancy FIFOs that also lost cross-slave W order.
- Host adapters: response-side readies gated by the tracked response
  head (unselected width paths used to handshake R/B into the void).
- Single-outstanding-target per master (new AW/AR only while all
  outstanding transactions hit the same slave) — the in-order response
  heads otherwise deadlock across masters.
- Shared struct ID width = max across masters (was first-master's; a
  6-bit RID 0x14 returned as 0x04 and never matched its waiter).
- Fallout fix in `axi4_to_axil4_wr`: `w_burst_capture` missing the
  `s_axi_awready` qualifier — a burst AW PARKED by the one-outstanding
  guard blocked the pending write's W forever (deadlock). Pinned by
  `test_pending_w_blocked_by_waiting_burst_aw` (converters suite).

**Gates:** DV bridge concurrency suite 8/8 (no xfails), the four killer
RANDOM_SEEDs replay green, RDS bridge suite 38/38, converters
run-all-full-parallel green.

---

## BRIDGE-001 — Generator emits NUM_SLAVES as a body localparam used in the port list
**Status:** closed 2026-08-08 (opened 2026-07-28)
**Priority:** P1 — blocked clean commits of any regenerated bridge

**Resolution (2026-08-08):** fixed on `fix/bridge-xbar-num-slaves-param`:

- Generator emits `NUM_SLAVES` in the parameter port list
  (`16841bce`); all bridges regenerated together; pre-commit
  decl-order hook passes with no `--no-verify`.
- The class sweep found and fixed the bigger sibling: all four
  generators emitted `import <bridge>_pkg::*;` at $unit scope with
  package types/localparams in the ANSI header — same
  Verilator-tolerant / strict-frontend-fatal asymmetry, plus $unit
  struct-type collisions for multi-bridge compilation units. Now the
  LRM module-header import form (`6f99c889`).
- Full bridge DV: 25/25 non-monitor tests green from clean builds.
  **Still broken (pre-existing, NOT this task):** all six
  `*_mon_monitor` stress tests fail identically at this branch's
  BASE commit (verified in a worktree at the pre-fix parent) — see
  BRIDGE-003.

## BRIDGE-004 — three 1x2_wr_*_mon_monitor stress tests fail at init
**Status:** closed 2026-08-17 — 426e3b3d; all 13 monitor stress tests
pass together from a verified clean (13/13, 56m57s)

`KeyError: 0` on `tb.master_read(0, addr)` → `self.master_rd[0]`.
Write-only bridge configs populate `master_wr` and leave `master_rd`
empty, but the shared harness assumed a read path in three phases, so
these died in about a second before any traffic.

**The characterisation was what cracked it.** Running all 13 together
showed every read variant passing, `mix_a`–`mix_d` passing, and
`1x2_rw_apb5` passing *while driving writes*. So the common factor was
never "writes" or "AXI5" — it was **no read master**, and `rw_apb5` was
the control that ruled the other two out.

Fix: `has_read_master()` (checks `master_rd` or `master_apb`, since APB
serves both directions through one object) gates three phases.
`run_traffic_phase` drives the same address plan as writes and verifies
through the slave memory model rather than a read-back — same traffic,
same addresses, same assertion, only the observation point moves.
`run_write_bp_phase` / `run_err_bp_phase` drive writes, since those
phases are about backpressure and packet flow.

SLVERR injection needed a write-side twin: `install_slverr_override`
replaces the read response generator, but the write path hardcodes
`resp=0` deep inside `_complete_write_transaction`, so
`install_slverr_override_wr` patches `b_channel.create_packet` — used
only for B responses on that slave, so the same blast radius rather
than a broader monkey-patch.

It took two rounds. Fixing the traffic phase moved the failure from
1.1 s to 31.9 s, which surfaced the SLVERR layer underneath; each fix
exposed the next assumption. The read path is untouched, so the ten
already-passing tests run byte-identical code.

**The bridge monitor stress suite is now fully green**, which it has
not been in this repo's recorded history.

## BRIDGE-003 — All six *_mon_monitor stress tests fail (pre-existing)
**Status:** closed 2026-08-16 — 6/6 green; 5963b2dc

Two independent causes, which is why this looked stuck for so long.

**Cause 1 (monitor RTL, fixed by the other agent).** Landed on main as
3ca1b9fb / merge 1451b5a8. Rerunning the six immediately after took the
suite from **0/6 to 3/6**: `1x2_rd`, `1x2_rd_regblock` and `mix_a`
passed, `mix_b/c/d` still failed.

**Cause 2 (testbench, fixed here).** `stress_read_plan` stepped offsets
by the SLAVE word (4 B) while `run_err_bp_phase` computed its expected
value via `tb.slave_mem_read(...)`, which derives `byte_count` from the
MASTER width. With a 64-bit master over the 4 KB seeded window, drawing
the top offset gave an 8-byte read at `0xFFC` — four bytes past the
cap. `MemoryModel` raised `ValueError`, and since that call sits
outside the phase's `try/except` (which only catches `RuntimeError` for
SLVERR), the phase died on an uncaught exception instead of reporting a
mismatch. Hence logs that simply stopped mid-run at the warning.

The plan now reserves room for a full master-width access:
`max_word = (CAP - access) // WORD + 1`. A 32-bit master still gets
1024 choices, so previously-passing tests are untouched.

**Worth remembering:** this was latent, not per-test. `mix_a` has the
same 64-bit master as `mix_b/c/d` and passed only because its random
draw never landed on the last word — a seed change would have moved the
failure around and made it look flaky.

**Re-verified 2026-08-17** from a genuinely clean build (all 13
`*_mon_monitor` in one pass, 55 min): all six are green. The earlier
6/6 had run behind a `make clean-all` that silently aborted, so this is
the result that actually counts.

**Not in scope, still failing:** of the seven other tests sharing this
helper, `1x2_wr_axi5`, `_axi5a` and `_axi5n` fail. Confirmed
pre-existing and unrelated by stashing this change and reproducing the
identical failure at HEAD in 1.1 s, before any traffic runs. Tracked as
[[BRIDGE-004]].

### BRIDGE-009: an out-of-range address hangs the master forever; the docs promise DECERR

**Status:** FIXED 2026-09-07 (1d442e76 + 24260594). An address matching no
slave range is claimed by an internal subtractive slave and answered with
DECERR + 0xDEADBEEF; the hit is sticky, carries the FIRST offending address and
a saturating count, raises `unmapped_irq`, and is readable/clearable over the
cfg APB window (`SUBTRACTIVE_STATUS`, `SUBTRACTIVE_ADDR`). Documented in HAS 4.5
and MAS 2.2. Bridge suite 70/70 at FULL; all 24 variants elaborate clean.

**What it cost, because the shape is worth remembering.** Seven defects, all
mine, in three kinds:

* *Verified narrow, shipped wide* (3): decl order, read-only variants, and the
  first decode fix each passed on the one variant I checked and failed on
  others. The check that finally held was all 24 filelists, not a
  representative one.
* *Assumed one owner where there were three* (2): the crossbar re-derives
  decode from address RANGES (a full-span catch-all became `1'b1`, routing
  every transaction to real slave AND catch-all, muxes ORing the payloads --
  corruption, worse than the hang), and the cfg regblock enumerates slaves
  separately (52 added fields RENUMBERED the map and switched the monitors
  off).
* *Wrong tool for the claim* (2): `--lint-only` elaborates without compiling
  C++, so it could not see `hwif_in = '0` failing g++; and the first
  W-before-AW test sent AW anyway, so it passed against a deliberately broken
  slave.

**Original report follows.**

**Found by** bridge qc round_1 (2026-09-07), verified against generated RTL.

**What the RTL does.** The adapter decodes the address into a one-hot slave
select and has no else:

```systemverilog
comb_slave_select_aw = '0;
if (fub_axi_awaddr <= 32'h3FFFFFFF)               comb_slave_select_aw[0] = 1'b1;  // ddr
else if (fub_axi_awaddr >= 32'h40000000 && ...)   comb_slave_select_aw[1] = 1'b1;  // scratch
```

For an address in no range the select stays all-zero, the AW-ready MUX falls to
`default: // No slave selected` leaving `fub_axi_awready = 1'b0`, and in the
crossbar every `*_aw_to_*` decode wire is false, so no slave ever sees
`awvalid`. Nothing generates a B or R response. **The master stalls forever.**

The only `DECERR` in the whole generated set is two COMMENTS in
`axi5_atomic_filter` about load-class atomics -- unrelated to address decode.
Verified across every generated bridge, read and write paths.

**What the docs claim.** `ch02_system_overview/03_system_context.md`:
"**Out-of-range detection** - DECERR for unmapped addresses". The integration
chapter plans an "Error handling test - OOR address response", and Table 6.4
says "All master addresses must map to slaves or OOR". An integrator reads that
and reasonably assumes a stray access is reported, not fatal.

**There is a proven pattern in-repo.** `apbx-xbar` implements exactly this:
`apbx_xbar_1to4.sv` carries 11 `decerr_pending` references and completes a
decode miss locally with an error response instead of stalling. The bridge
generator should emit the AXI equivalent -- a decode-miss path that accepts the
address beat and returns `DECERR` on B/R with the right ID -- rather than
leaving the one-hot all-zero.

**Two things to decide, in order:**
1. RTL: emit decode-miss completion in the generator (all variants, read and
   write). Until then the behaviour is a hang.
2. Docs: whatever is decided, the current text is wrong TODAY. Either it
   describes behaviour that exists, or it says plainly that unmapped addresses
   are a configuration error the fabric does not detect.

**Do not** fix only the docs. "Unmapped addresses hang the fabric" is a
defensible documented limitation only if someone chooses it deliberately; it is
not the sort of thing to arrive at by editing a sentence.

### BRIDGE-010: slave-port response routing assumes in-order completion, and nothing says so

**Status:** RESOLVED 2026-09-08 by way (1) below -- document the constraint
and make the violation loud. The constraint is now stated in the PRD
(comparison table, risk register, glossary), HAS, MAS and `CLAUDE.md`; every
generated slave adapter carries a `BRIDGE-010` comment and an `$error`
assertion that fires when a returned B/R does not match the FIFO head; the
arbitration tests were made real and detect the ordering (`a43b032dd`); the
out-of-order/CAM/ID-table claims were swept to zero across both books
(`a71a4c989`, `a31a5366`). Way (2), ID-keyed tracking via `bridge_cam`, is
NOT chosen: it is a design change, and the books now say so instead of
describing it as built. Reopen as a new task if OOO support is ever wanted.

**Priority (as filed):** High. Silent misroute, not a hang -- a master receives another
master's response, carrying that master's BID.

**Found by** bridge qc round_1 (2026-09-07), verified against generated RTL.

**The mechanism.** Each generated slave adapter tracks the originating master
in a plain in-order FIFO -- push on the address handshake, pop on the response:

```systemverilog
// push
wr_fifo[wr_ptr[...]] <= xbar_bridge_id_aw;   // on AW accept
// route the response by the FIFO HEAD, not by the returned BID
assign bid_bridge_id = wr_fifo[rd_ptr[...]];
```

IDs are **pass-through** -- the slave port is the same width as the master
port, with no `bridge_id` prepended (confirmed: `input logic [3:0]
cpu_axi4_awid` -> `output logic [3:0] ddr_s_axi_awid`, and the generator
comment says "Master id_width drives the slave-port ID width (pass-through)").
So the FIFO *is* the return path. It only works if responses come back in
request order.

**Why it is reachable.** Two masters can have writes outstanding at one slave
simultaneously: `bridge_2x2_rw` connects both `cpu` and `dma` to `ddr`, the
crossbar's W-owner FIFO explicitly supports interleaved AW ownership, and the
arbiter releases its grant at the ADDRESS handshake rather than the response.
The per-master single-outstanding-target gate prevents one master spanning
several slaves; it does not prevent several masters sharing one. AXI4 permits a
slave to complete different-ID transactions out of order, so a reordering
slave -- a multi-ported DDR controller is the normal case -- makes the head
stale. The response then goes to the wrong master AND carries an ID that master
never issued, which is an AXI violation at its port.

**Nothing detects it.** No assertion, no ID comparison, no check that the
returned BID/RID matches the head. The failure is silent data misattribution.

**And the docs claim the opposite.** The HAS documents out-of-order completion
as a supported feature, with a BID-prepend/extract scheme and slave IDs widened
by `clog2(NUM_MASTERS)`. None of that is built (same finding cluster as
round_1 findings 1-3). So an integrator is told the fabric handles reordering
when in fact reordering breaks it.

**Two ways out, and the choice is a design decision:**
1. **Document the constraint** -- "each slave port must return B/R in request
   order across ALL IDs" -- and add a simulation assertion that fires when a
   returned BID/RID does not match the FIFO head. Cheap, honest, and makes the
   limitation loud instead of silent. `bridge_cam.sv` exists but is
   instantiated in zero generated bridges, so the in-order design is the real
   one.
2. **Make tracking ID-keyed** (use `bridge_cam`, or prepend `bridge_id` to the
   slave-side ID as the docs already claim). Larger change; buys real OOO
   support.

Whichever is chosen, the HAS/PRD claims must match it. Today they describe (2)
while the RTL implements (1) without saying so.

**Related:** [[BRIDGE-009]] (the other round_1 RTL finding, fixed). The
in-order `bridge_id` FIFO is the same structure both touch.

### BRIDGE-011: Response-tracking FIFOs overflow silently (HIGH)

**Status:** FIXED 2026-09-08 (`c64660f47`, master-side analysis corrected in
`6a824aeb2`). `awready`/`arready` now gate on the tracking FIFO being not-full
on both sides: the master adapter folds not-full into `aw_gate_ok`/`ar_gate_ok`,
the slave adapter splices it into the sub-block handshake (valid and ready
together). Test: 80 concurrent writes from two masters to one slave with B
held off, asserting occupancy never exceeds depth -- RED 3/3 before (peak 31),
GREEN 3/3 after (peak 16). Bridge 71/71 at FULL. Filed by bridge qc round_1's
follow-up (2026-09-08); this entry was first written into the legacy
`projects/components/bridge/TASKS.md` and moved here 2026-09-08.

Original filing follows.

**Found** 2026-09-08 while checking BRIDGE-010's reachability.

Every generated bridge carries two 16-entry response-tracking FIFOs, and
NEITHER has a full check or applies backpressure:

| FIFO | File | Depth | Routes |
|---|---|---|---|
| `wr_fifo` / `rd_fifo` | `<slave>_slave_adapter.sv` | `WR/RD_FIFO_DEPTH = 16` | B/R back to the originating MASTER |
| `aw_trk_mem` / `ar_trk_mem` | `<master>_master_adapter.sv` | `AW/AR_TRK_DEPTH = 16` | B/R back to the originating SLAVE |

Push is unconditional on the address handshake:

```systemverilog
end else if (xbar_..._awvalid && xbar_..._awready) begin
    wr_fifo[wr_ptr[$clog2(WR_FIFO_DEPTH)-1:0]] <= xbar_bridge_id_aw;
    wr_ptr <= wr_ptr + 1'b1;
end
```

The 17th outstanding request wraps the 4-bit index and overwrites entry 0. The
two FIFOs then fail DIFFERENTLY, and the difference matters:

**Slave-side (`wr_fifo`/`rd_fifo`) -- silent misrouting.** These hold the
originating MASTER id. Two masters may hold writes to the same slave at once
(the per-master gate restricts each master to one slave, not one master per
slave), so the entries are a genuine MIX. Overwriting entry 0 routes the 1st
transaction's response by the 17th's entry: B/R delivered to the WRONG MASTER,
no error, no protocol violation on any port. Needs >=2 masters on one slave.

**Master-side (`aw_trk_mem`/`ar_trk_mem`) -- NOT a misroute; a stall at 32.**
Corrected 2026-09-08: this was filed as a wrong-slave misroute and that was
wrong. `aw_gate_ok` admits a new AW only while it targets `r_aw_active_target`,
so every in-flight entry holds the IDENTICAL slave-select and the overwrite
writes the same value back. The real failure is pointer lapping: the pointers
are `[AW_TRK_AW:0]`, so at exactly 32 outstanding `aw_trk_wptr == aw_trk_rptr`
reads as EMPTY, `b_slave_select` falls to `'0`, no slave is selected and B
stops flowing. A hang, not corruption, and it needs 32 outstanding from ONE
master.

**Reachability -- verified, not inferred.** Nothing anywhere caps the count:

1. `axi4_master_wr.sv:156` -- `assign int_skid_awready = m_axi_awready;`
   Straight passthrough. No outstanding counter in the module at all.
2. Master adapter `aw_gate_ok` gates on WHICH slave, never HOW MANY:
   `(aw_trk_wptr == aw_trk_rptr) || (comb_slave_select_aw == r_aw_active_target)`
   Same-slave pipelining is explicitly unlimited -- the comment says so.
3. `grep -niE "outstanding|credit|max_txn|in_flight|throttle"` over every
   generated `.sv` in `bridge_4x4_rw` returns only the aw_gate_ok comments.

So the bound is whatever the attached slave accepts. A DDR controller that
takes 32 outstanding writes -- ordinary -- overflows this on every run. The
slave-side FIFO sees the SUM across masters, so it fills faster still.

**Why no test caught it.** The 70-test FULL regression passes because the AXI4
BFM slaves return B/R promptly, so depth stays far under 16. The bug needs a
slow slave plus a deep pipeline, which no current bridge test builds.

**Recommended fix:** gate `awready`/`arready` on the tracking FIFO being
not-full. No deadlock risk -- entries drain on responses, which never depend
on accepting a further request. Deepening the FIFO is NOT a fix; it moves the
cliff. An assertion alone detects it in sim but leaves silicon corrupting.

Needs a test that holds B off while issuing >16 -- that test should be written
FIRST and shown RED, since a test whose stimulus cannot reach depth 17 passes
against the broken RTL.

Related: BRIDGE-010 (ordering, same FIFOs). Both are consequences of routing
by FIFO position rather than by returned ID.

### BRIDGE-008: the two slave BFMs disagree about an out-of-range access

**Status:** CLOSED 2026-09-09 -- unified in the framework (RDS-DV `fc0112e`),
Sean: "unify what out of range means". One contract, every memory-backed
slave BFM (AXI4/AXI5/AXIL4/AXIL5 Slave{Read,Write}, APB/APB5 Slave): an
access beyond the model answers SLVERR (PSLVERR on APB), nothing is written
(AXI write bursts are checked whole first), read data is 0xDEADDEAD
replicated to the beat width, one WARNING names the slave, address and
model size. Implemented as ONE code path -- `MemoryModel.in_range` /
`oor_warning` / `oor_read_data` in `shared/memory_model.py` -- with a
structural unit test that every family calls it. APB's grow-the-memory
behaviour is now opt-in (`error_overflow=False`); the default is the error.
On the bridge side the generated `master_write` now raises on an error
response (single_write only reported it in a dict, so a SLVERR write used to
pass through unnoticed), the boundary probe swallows the SLVERR only for
probes past the seeded region, and the TB/test comments that described the
AXI4 slave's old silent-OKAY as "the framework behaviour" are rewritten.
The model's limit is distinct from the design's: an address the bridge does
not decode at all is the subtractive slave's DECERR (BRIDGE-009).

**Priority (as filed):** P3, downgraded 2026-09-05. The two red tests are FIXED and the
suite is 70/70; what remains open is the BFM asymmetry itself, which still
applies to any slave whose window exceeds the TB's memory model.

**The tests were fixed by widening the model, not by resolving the
disagreement.** SLAVE_MEM_CAP_BYTES went 4 KB -> 64 KB so a peripheral window
is covered whole and those probes now land in real memory (they verify DATA as
well as routing as a result). A slave larger than the cap still depends on
whatever the BFM does out of range -- which is the thing below, still unsettled.
**Status:** open 2026-09-05. Surfaced by the axil5 work (A5-3d): fixing the
`logic [-1:0]` build failure on AXI4-Lite MASTER ports made mix_a..d compile
for the first time, and two simulation failures appeared behind it.

**Failing:** `test_bridge_mix_a_boundary_probe`, `test_bridge_mix_c_boundary_probe`.

**The discriminator is exact** -- it is the AXI4-Lite SLAVE's region size:

| bridge | AXI4-Lite slave | region | result |
|---|---|---|---|
| mix_a | `axil_periph` | 64 KB | FAIL |
| mix_c | `cfg_regs` | 64 KB | FAIL |
| mix_d | `doorbell` | 4 KB (= the cap) | pass |
| mix_b | none | -- | pass |

**Mechanism.** The generated TB seeds only `SLAVE_MEM_CAP_BYTES = 4096` of each
slave's MemoryModel, and its class comment states the premise this rests on:

> Routing-only probes (address_decode beyond page 0) work outside the cap --
> the framework slave BFMs silently drop OOR writes and fall back to
> addr-as-data on OOR reads, so the AW/AR routing assertion still fires.

That premise is false for the AXI4-Lite slave BFM. `AXIL4SlaveWrite`'s response
path does:

```python
except Exception as e:
    if self.log: self.log.warning(f"Memory write failed at 0x{address:08X}: {e}")
    resp = 2  # SLVERR
```

So a probe at `base + 0x8000` on a 64 KB axil slave reaches the right slave --
routing is CORRECT, which is what the probe set out to test -- and is then
answered SLVERR because the model holds 4 KB. The AXI4 master's
`write_transaction` raises on the error response and the test dies.

**The two slave BFMs genuinely disagree, and the TB comment describes the
AXI4 one.** Confirmed by reading both (2026-09-05):

```python
# AXI4SlaveWrite -- logs and leaves resp alone. Silent drop, answers OKAY.
except Exception as mem_error:
    if self.log:
        self.log.warning(f"AXI4SlaveWrite: Memory write failed for txn ...")

# AXIL4SlaveWrite -- same situation, different answer.
except Exception as e:
    if self.log: self.log.warning(f"Memory write failed at 0x{address:08X}: {e}")
    resp = 2  # SLVERR
```

So this is not a case of the TB believing something no BFM does -- it is one
BFM behaving one way, its AXI4-Lite sibling the other, and the TB written
against the first. That asymmetry is the actual defect; the two red tests are
a symptom.

**Two candidate fixes, and they are not equivalent:**

1. **Cap the probe addresses** to the modelled window for protocols whose BFM
   errors out of range. Smallest change, but it narrows what the boundary
   probe covers -- and covering the far edge of the window is the point of
   the test.
2. **Make `AXIL4SlaveWrite`/`AXIL4SlaveRead` behave as the TB comment says**
   (drop OOR writes, addr-as-data on OOR reads), matching the AXI4 slave BFM.
   This is the fix that makes the comment true, but it lives in RDS-DV and
   changes behaviour every AXIL test sees -- so it needs its own check that
   nothing was relying on the SLVERR.

Decide which contract is right before writing either. Whichever wins, the TB's
class comment has to end up describing what the BFMs actually do -- a comment
asserting a behaviour no BFM implements is what let this sit unnoticed.

**Not a blocker for anything.** Routing is proven correct by the same run.

---

---

### BRIDGE-012: trace is not echoed on B/R when the slave lacks trace; the AXI5 checker calls that a violation

**Status:** CLOSED 2026-09-10 by way (1), echo at the boundary -- Sean asked
for the most robust option. The master adapter's AW/AR tracking FIFO already
holds one entry per outstanding request, in the order responses return
(BRIDGE-010's in-order contract), so the request's trace now rides in the
entry that routes its response and the port drives B/RTRACE from it. The
promise is kept on every path: native, trace-less slave, and across a dwidth
converter that cannot carry sideband at all.

It does not launder a downstream fault. The response mux still records what
the SLAVE said in `b_slave_trace`/`r_slave_trace`, and a generated
`` `ifndef SYNTHESIS `` assertion `$error`s when a trace-CAPABLE slave (a
generated one-hot mask) returns a bit that differs from the tracked request.
Only `trace` echoes -- `poison` on R is slave-sourced data integrity and
echoing it would launder corrupt data.

Verified: pure-AXI4 bridges byte-identical (only the 12 trace-carrying AXI5
bridges changed); five AMBA5 sideband tests moved to the echo contract and
pass, each with a NEGATIVE half asserting an untraced request still returns
trace=0, so the echo cannot be a tie-high; the AXI5 compliance checker at
every master port reports zero violations with no allowance, where before it
counted one per drop-path response.

**Residual, NOT fixed here:** a read-return atomic swallowed by
`axi5_atomic_filter` gets its B generated inside the filter, which sits
upstream of the adapter's tracking FIFO, so that response's trace is whatever
the mux holds rather than the swallowed request's. Pre-existing and unchanged;
the filter is shared `rtl/amba` RTL and out of scope for a bridge task.

**Priority (as filed):** P2. A design decision, not a bug hunt: the fabric and
the checker disagreed about what an AXI5 port promises.

**Found by** arming `AXI5ComplianceChecker` on every AXI5 master port
(2026-09-09, BRIDGE-007). `test_bridge_1x2_wr_axi5n_sideband[full]`: 12
`TRACE_CONSISTENCY_VIOLATION`s in 4668 checks -- exactly the 12 writes that
went to `sram_wr`, the poison-only slave. AW carried `awtrace=1`, the B came
back with `btrace=0`, and the checker's rule is "B.trace == AW.trace".

**What the fabric does, on purpose.** A5-2 slice 2: sideband a slave does
not support terminates mid-fabric with a generation-time WARNING
("AXI5 sideband 'trace' terminates on path cpu_wr -> sram_wr"), and the
xbar muxes b/r sideband from featured slaves only, so a trace-less slave
returns 0. The wr sideband test asserts `btrace=0` on that path as the
expected result; the MAS AMBA5 chapter documents the drop.

**What the checker says.** From the master's port the bridge IS the
Subordinate, and it advertised trace on that port; AXI5 expects the response
trace bit to follow the request's. The checker does not know (and should not
have to know) that the slave behind the path is trace-less.

**Two ways out:**
1. **Echo at the boundary.** The master adapter already tracks each
   outstanding request in its response FIFO (BRIDGE-011); a trace bit per
   entry lets it set `btrace`/`rtrace` = the request's trace whenever the
   returning response carries none. The port then keeps the promise
   regardless of the slave; the generation-time warning goes away for
   trace (nsaid/mpam/mecid/unique have no response half and are unaffected).
2. **Document the drop as the port contract** and keep the checker's
   expectation for those paths as an explicit exact-count allowance in the
   sideband tests (what the tests do today, via
   `tb.assert_compliance(allow={'TRACE_CONSISTENCY_VIOLATION': n})`).

(1) is cheap and makes the AXI5 port honest; (2) leaves a port that
advertises trace and sometimes does not return it. Owner decides.

### BRIDGE-013: in the _mon variants the subtractive slave's monitor is built and left unconnected

**Status:** CLOSED 2026-09-10 by way (2), stop emitting it. An INTERNAL
slave now gets no monitor: `enable_monitoring and not slave.internal` in
`bridge_module_generator._generate_slave_adapter`. That is what
`bridge_generator.py` already claimed ("the subtractive catch-all has no
monitor wrapper") -- now the RTL agrees.

Verified: the subtractive adapter's monitor ports go 24 -> 0 and its
`axi4_master_rd_mon` instance disappears; exactly 13 files change, all of
them `*_mon/subtractive_adapter.sv`, matching the 13 failing variants
one-for-one; non-`_mon` variants are byte-identical; and `make verilator`
in `projects/components/bridge/rtl` reports **"✓ Bridge RTL lint passed"**
for the first time, so the gate is an instrument again.

Nothing is lost. An unmapped access is still reported through the
subtractive slave's sticky `SUBTRACTIVE_STATUS` / `SUBTRACTIVE_ADDR` and
`unmapped_irq` (BRIDGE-009), which the top does wire, and the tests that
cover BRIDGE-009 are unaffected.

**Way (1) remains available as a FEATURE, not a repair.** The subtractive
slave's own monbus port is still tied off in the generated top with an
explicit `assign subtractive_monbus_ready = 1'b1;  // TODO: -> monbus_arbiter`
and an explicit unused-sink -- acknowledged, not dangling. Putting unmapped
accesses on monbus means adding an arbiter source and moving the `_mon`
tests' packet expectations; file it as its own task if wanted.

**Priority (as filed):** P2. Not lint noise -- the lint gate was pointing at
a real disconnection, and 13 of 38 variants failed on it, which is why the
gate reported nothing useful.

**Found by** running the bridge lint gate 2026-09-10 (BRIDGE-007 follow-up).
`make verilator` in `projects/components/bridge/rtl`: **13 of 38 variants
FAIL, 427 `%Warning-PINMISSING`, and every one of them is the same
instance** -- `u_subtractive_adapter` in a `*_mon` top.

**The mechanism.** In a `_mon` variant the generated `subtractive_adapter`
declares **24 monitor ports** (`i_mon_time`, `monbus_{rd,wr}_{valid,ready,
packet,timestamp}`, `cfg_{rd,wr}_*`) and instantiates a monitor behind them
(`subtractive_adapter.sv:255` wires `i_mon_time` and `monbus_valid` into the
submodule). The bridge top instantiates that adapter and connects **none of
them**. So the subtractive slave's monitor is elaborated, occupies area, and
its monbus output goes nowhere; its cfg inputs float. The non-`_mon`
variants emit zero such ports, so this is specific to the monitor build.

BRIDGE-009's subtractive slave also reports unmapped accesses through its
sticky `SUBTRACTIVE_STATUS` / `SUBTRACTIVE_ADDR` cfg registers and
`unmapped_irq`, which DO reach the top -- so the observable BRIDGE-009
behaviour is intact and the tests that cover it are honest. What is lost is
the monbus path: an unmapped access never produces a monbus packet in a
`_mon` bridge, and nothing says so.

**The generator says it is deliberate, and the RTL disagrees.**
`bridge_generator.py:796` reads "The subtractive catch-all has no monitor
wrapper (it reports on its own monbus port)" -- but in `_mon` variants the
adapter generator emits one anyway and the top does not wire it.

**Two ways out, and it is a design decision:**
1. **Connect it.** Add the subtractive's monbus as a source on the
   monbus arbiter tree so an unmapped access is reportable like any other
   error. Costs an arbiter input per `_mon` bridge and changes the monbus
   topology (and the tally/coverage expectations of the `_mon` tests).
2. **Stop emitting it.** Suppress the monitor and its 24 ports on an
   INTERNAL slave, matching what the generator comment already claims.
   Cheaper, removes dead area, and makes the lint gate meaningful.

(2) matches the stated intent; (1) is the one to take if an unmapped access
ought to be visible on monbus. Either way the lint gate goes green and starts
reporting real findings again -- do NOT waive PINMISSING to get there, which
would hide exactly this class.

**Correcting the record:** the note carried on [[BRIDGE-002]] said `make
verilator` fails on "all 36 variants, entirely from pre-existing
PINCONNECTEMPTY on deliberate open pins". Measured: 13 of 38, all
PINMISSING, one instance, not deliberate.

### BRIDGE-002: AMBA5 bridge support (AXI5 ports alongside AXI4)
**Status:** CLOSED 2026-09-10. Every phase landed: A5-1 (AXI5 masters on
the AMBA4 fabric), A5-2 (AXI5 slaves, native sideband through the structs),
A5-3a (store-class atomics, filter for write-only ports), A5-3b (read-return
atomics native on rw ports, with the out-of-range answer and the response-mux
invariant guard), A5-3c (APB5 slaves), A5-3d (AXI5-Lite slaves). Verified by
the bridge FULL regression on 2026-09-10: 249 passed across 27 fixtures with
the AXI5 compliance checker armed on every AXI5 master port. Deliberately not
done, and not owed by this task: AXI5-Lite and APB5 as MASTER protocols
(slave-only by decision; nothing in-tree needs a requester), and the
"native-AXI5 fabric as follow-on" from the original goal, which the sideband
structs made unnecessary for every feature anyone has asked for. Either wants
its own task if it ever becomes real.
**Priority:** P1
**Owner:** TBD

Goal: a bridge that is AMBA4-shaped like today but accepts AXI5
masters/slaves at the boundary, with a native-AXI5 fabric as the
follow-on.

**Already in-tree (verified 2026-08-08):** `rtl/amba/axi5/` has full
master/slave wr/rd wrappers + `_mon`/`_cg` variants + stubs,
feature-parameterized (ENABLE_ATOMIC / POISON / TRACE / UNIQUE / MPAM /
MTE / MECID / NSAID, AXI_ATOP_WIDTH); `rtl/amba/apb5/` has APB5
master/slave/monitor; CocoTBFramework has AXI5 BFMs and
`axi5_compliance_checker`.

**Genuine gaps:** no AXI5<->AXI4 feature converter/terminator IP; no
`*_to_apb5` shim (bridge APB path is APB4-only).

**Phasing:**

1. **A5-1 interop boundary (AMBA4 fabric, AXI5 ports):** config gains
   `protocol = "axi5"` per port + optional `axi5_features = [...]`
   mapped to the wrapper ENABLE_* parameters; validator rules (axi5
   master -> axi4/apb slave allowed with feature-drop warnings;
   `atomic` requires a termination policy — default DECERR + monitor
   event); adapter generator instantiates `axi5_*` wrappers and emits
   the feature-gated signal set; fabric stays AXI4. DV: AXI5 BFM
   master + compliance checker on an existing config.
2. **A5-2 native AXI5 sideband:** extend generated `_pkg` structs with
   feature fields; pass-through on AXI5->AXI5 paths (trace, unique,
   poison, MPAM/NSAID).
3. **A5-3 atomics + APB5:** AWATOP returns data on the R channel — the
   crossbar needs AW-issued R-response routing and read-return ID
   tracking (the hard part; design note before coding). New
   `*_to_apb5` shim for APB5 slaves.

**Done looks like (A5-1):** an `axi5` port type generates, validates,
simulates green with the AXI5 BFM + compliance checker, and feature
signals terminate per policy at the AMBA4 fabric boundary.

**Progress (2026-08-08):** A5-1 core LANDED for AXI5 masters —
`protocol = "axi5"` + `axi5_features` config, validator split
(sideband nsaid/trace/mpam/mecid/unique allowed; atomic/poison/mte/
chunking rejected naming their delivering phase; AXI5 slaves rejected
until A5-2), axi5_slave_{wr,rd}[_mon] boundary wrappers with
feature-gated external ports (no region — AXI5 dropped it) and full
tie/open termination at the AXI4 fabric, bridge_1x2_rd_axi5 fixture
in the manifest (+_mon variant), 10 new unit tests (37 total), sim
smoke green with the AXI4 BFM driving the base subset. axi5+mon is
supported (monitor surface verified identical to axi4's).
**A5-1 SIGNED OFF (2026-08-09):** both remaining items landed —
bridge_1x2_wr_axi5 fixture (wr emission path exercised: aw/w/b
surface with awtrace/awunique/btrace, sims green) and
test_bridge_1x2_rd_axi5_bfm5.py, a hand-written test driving the AXI5
port with the real AXI5MasterRead BFM plus AXI5ComplianceChecker on
the same prefix: 6 reads across both slaves data-correct, 708
compliance checks, 0 violations, status PASSED. The BFM resolved the
sideband pins (artrace/arunique) as optional signals on the DUT.
Note for A5-2: the BFM issues trace-clear transactions by default
(traced_transactions=0 in the report) — asserting sideband VALUES
end-to-end belongs with the native-sideband work.

Next: A5-3 (atomics + APB5). [All of A5-3 landed by 2026-09-10; see the slices below.]

**A5-3 design note (2026-08-09):** three slices, in order of
tractability. Facts on the ground: the axi5 wrappers already
transport AWATOP feature-gated through their skid path (both
families); the DV BFM's `atomic_operation` is write-shaped
(`write_transaction` + atop — it does not collect an R return); the
converters IP has `axi4_to_apb4_{convert,shim}` as the template and
`apb5_pkg` provides apb4<->apb5 m2s/s2m conversion functions.

*Why read-return atomics are the hard part in THIS fabric:* AWATOP
classes — `01xxxx` AtomicStore (B-only response), `10xxxx`
AtomicLoad, `11000x` AtomicSwap/Compare (original data returns on
the R channel, using the AW ID). The bridge splits wr and rd into
separate wrappers, adapters, and xbar paths per port; every R-return
tracker (slave adapter rd-side FIFO/CAM pushing on AR handshake,
master adapter r_slave_select FIFO, xbar rready gating on rid_valid)
learns only about ARs. A load-class atomic issues on the wr path and
returns on the rd path — invisible to all three trackers, so the R
response would hang. Fixing it properly needs a per-ID tracking
block SHARED between a port's wr and rd adapters (cross-adapter
ports through the bridge top), pushed on atomic-AW handshake, plus
per-ID (CAM) rather than in-order tracking on the master rd path.
The AXI spec's "an atomic's ID must not be concurrently in use by
reads" rule keeps routing unambiguous once tracked.

- *A5-3a — store-class atomics, native transport:* `atomic` becomes
  connectivity-gated exactly like poison (every connected path
  AXI5-both-ends + atomic-enabled + width-matched); `aw.atop[5:0]`
  joins the sideband spec table and rides the fabric structs by the
  slice-2 mechanism unchanged. NEW RTL: a small atomic filter at the
  atomic-enabled master boundary (fub side, before the structs) —
  read-return ATOP (`awatop[5]==1`) is NOT forwarded: the filter
  swallows the AW + its W burst and generates a local DECERR B (the
  A5-1 termination policy, narrowed from "all atomics" to
  "read-return atomics"), with a monitor event on mon variants.
  Store-class forwards natively; the external slave performs the op.
  The filter is a real little FSM (must consume W beats) — build it
  as reusable IP (rtl/amba/axi5/axi5_atomic_filter.sv) with its own
  val tests before wiring it into the generator.
  *Filter IP DONE (2026-08-10):* control-plane-only design (handshakes
  + atop + id + wlast; payload routes around it): route queue pushed
  per AW / popped at WLAST steers or sinks W bursts, response queue
  drains local DECERRs when downstream B is idle. W stalls until its
  AW is queued (deadlock-free — AW never depends on W). Documented
  limitation: a local DECERR can pass a same-ID in-flight write's B,
  which the AXI atomic ID rule already forbids a compliant master
  from observing. val/amba/test_axi5_atomic_filter.py green (mixed
  forward/swallow traffic, multi-beat discard, DECERR ids/order);
  -Wall lint + decl-order + registry-audit clean. *A5-3a DONE
  (2026-08-10, commit be2fd6bc):* aw.atop[6] in the sideband table +
  external surface; 'atomic' connectivity-gated (validator check
  generalized over gated features); master adapter inserts the
  filter pref_axi_* -> fub_axi_* on atomic-enabled wr paths
  (handshakes + B payload through the filter, the rest passes
  around); filelist emission -f's the filter closure. Fixture
  bridge_1x2_wr_axi5a (+_mon) sims 2/2 green; hand-written atomics
  test: plain/AtomicStore forward with atop intact at the slave AW
  and land in memory, AtomicLoad/Swap DECERR locally with no slave
  AW and no memory write; 52 generator unit tests; 23/23 bridges
  regenerate, pre-existing byte-identical. A5-3 remaining: only
  A5-3b (read-return atomics), deferred until a consumer exists.
- *A5-3b — read-return atomics: LANDED 2026-09-10.* The consumer the
  deferral was waiting on was built alongside it: the AXI5 slave BFM now
  performs atomics on its memory model and returns the original data on R,
  and the AXI5 master BFM collects it. With that, the fabric side.

  *What the design note above got right, and what it did not need.* A
  read-return atomic is invisible to every AR-fed tracker, that part held.
  But the "per-ID tracking block SHARED between a port's wr and rd
  adapters" did not need to exist: the master adapter's wr and rd paths are
  one module, so the atomic AW simply pushes into the existing AR->R
  slave_select FIFO. What that FIFO needed was a DUAL push (an AR and an
  atomic AW can handshake in the same cycle; AR takes the first slot, the AW
  the second) and the AW's own single-target gate requiring two free slots.
  The AW is the last entry pushed, so it becomes the active target. In-order
  routing stays sound because the single-target rule already guarantees
  every live entry shares one slave. Per-ID tracking is needed only at the
  SLAVE adapter, where reads and atomics from the same requester return in
  an order no FIFO can predict: `rtl/amba/axi5/axi5_atomic_rr_tracker.sv`
  (its own val test, gate/func/full) records (AWID -> requester) at every
  AW with AWATOP[5], answers combinationally from RID, and an R beat it
  claims is routed by its tag and does not pop the in-order FIFO. The
  atomic AW's awready is held while it is full. The BRIDGE-010 sim check
  skips tracked beats and reports an RID that matches both a tracked atomic
  and the FIFO head: two requesters aliasing one ID at a slave, which this
  fabric never disambiguated.

  *The out-of-range case, found while writing the test.* A read-return
  atomic whose address nobody owns decodes to the subtractive slave, which
  answers DECERR on B and knows nothing about R. With the master adapter now
  holding an R-return slot for it, that beat never coming would have wedged
  every later read on the port behind the stuck head: BRIDGE-009's hang,
  reborn on the atomic path. So the master adapter answers those itself: the
  tracker entry carries a `local` flag and the AW's ID, and when it reaches
  the head the R mux presents one DECERR beat with that ID while holding
  every slave's rready off. The rw fixture's sram range was halved
  (0x8000_0000, 0x4000_0000) so 0xC000_0000 and up is genuinely unmapped
  and the test can exercise it: B and R both DECERR, then a plain read and
  an in-range atomic still complete. Mutation-checked RED: with
  `r_local_head` forced to zero the OOR atomic's R never arrives.

  *One invariant the dual push nearly broke, and the guard that now names
  it.* The crossbar's response mux is an OR-merge; it is a mux only while at
  most one connected slave's tracker head belongs to a given master, which
  the master adapter's single-outstanding-target gate guarantees. With the
  AR->R FIFO empty, an AR and an atomic AW to DIFFERENT slaves both pass
  their target rule in the same cycle, and the first dual push happily held
  both -- two slaves then drove one master's R lines and the ORed IDs sent
  beats to the wrong per-ID queues. It surfaced as a seed-dependent read
  starvation in the sign-off test (two cells of three, one seed base), and
  passed clean under another base. The AW now yields in that cycle. And
  every generated crossbar carries a sim-only `$countones(...) > 1` guard on
  each master's response-mux select vector, so the invariant slipping is a
  named error in the cycle it happens rather than a starvation a thousand
  cycles later. That guard is the one change to the 26 pre-existing
  bridges' RTL (their `*_xbar.sv`); adapters are byte-identical.

  *Where the filter stays.* A write-only atomic master has no R path, so it
  keeps the A5-3a `axi5_atomic_filter`; `rr_atomic` on the master adapter
  is exactly "atomic AND rw". Validator: an rw atomic master's connected
  atomic slaves must be rw (else DECERR-by-filter would have been the honest
  answer, and now there is no filter) and must not use enable_ooo (the CAM
  read path has no hook for the return tracker; it is also unexercised, no
  fixture sets it). Filelist emission pulls the filter only for write-only
  atomic masters and the tracker only for rw atomic slaves.

  *Also fixed on the way.* The AXI5 slave BFM used to write an
  AtomicStore's operand as a plain write; it now performs the store-class
  ALU op, and the A5-3a test's expectation (memory == operand) was that old
  behaviour written down. It now expects old + operand.

  *Verified.* Fixture `bridge_1x2_rw_axi5a` (+mon), the rw twin of the
  A5-3a fixture. 27/27 bridges regenerate; the 26 pre-existing are
  byte-identical in RTL (the 2x2_axi5 TB picked up one line pairing its
  slave BFMs). Lint gate 40/40 clean. 71 generator unit tests (5 new: the
  two validator rules, generation of both atomic fixtures, and that the
  write-only one still gets its filter). Hand-written
  `test_bridge_1x2_rw_axi5a_atomics.py`: AtomicLoad ADD/SET/UMAX, Swap,
  Compare match and mismatch on both slaves, each checked three ways (R data
  is the pre-op value, memory holds the post-op value, a plain read agrees),
  then reads and atomics in flight together across and within slaves; 16 /
  112 read-return atomics routed at func / full. Mutation-checked RED: with
  the tracker's hit removed from the slave adapter's rid_valid, the R beat
  is never routed and the test dies on "atomic read-return timeout".

  *Checker.* `AXI5ComplianceChecker` treats a read-return atomic AW as an
  outstanding single-beat read (RLAST and ordering checks apply) -- but only
  on an interface that has an R channel, since on a write-only port the
  boundary filter answers with DECERR on B and no R can ever come; the first
  version registered it regardless and the A5-3a test then reported every
  second atomic as reusing a live ID. It flags an
  atomic whose ID is still in use by an outstanding read or write
  (ATOMIC_ID_IN_USE), and flags an R beat with no outstanding request
  (R_WITHOUT_REQUEST) -- previously such a beat was silently ignored. The
  first version of the hand-written test tripped the ID rule itself at full
  depth: it rotated 14 IDs over 32 in-flight transactions, so a word's four
  transactions reused IDs a still-outstanding word held, and two read
  coroutines then shared one per-ID response queue. It now runs in batches
  of three words so twelve distinct IDs cover everything in flight.
- *A5-3c — APB5 slaves (independent, do first):* new converters IP
  `axi4_to_apb5_shim` = the axi4_to_apb4 conversion core + the
  apb5_pkg m2s/s2m conversion functions + PWAKEUP generation (assert
  with PSEL, deassert after the transfer) + user-signal ties;
  slave_adapter_generator gains a protocol="apb5" branch mirroring
  the apb one; validator apb5 constraints mirror APB4's (rw-only,
  32-bit). DV: apb5 slave BFM exists (CocoTBFramework apb5), so a
  bridge_1x2 fixture with one apb5 slave closes it.
  *Step 1 DONE (2026-08-10, commit f6f30762):* the shim IP itself —
  converters/rtl/axi4_to_apb5_shim.sv (pin-superset wrapper over the
  apb4 shim; PAUSER/PWUSER tied '0 out, PWAKEUP/PRUSER/PBUSER
  terminated in; mirrors apb5_slave.sv pin-for-pin) + its closure
  filelist; lint/audit/decl-order clean.
  *Step 2 DONE (2026-08-10):* protocol="apb5" through the whole
  generator stack per the map below — all 14 protocol-test sites,
  the Axi4ToApbShim component's protocol switch, bridge-top +
  adapter + instance external surfaces (5 extra pins), validator/
  config whitelist, filelist emission, and the TB template's three
  apb branches (APB4 BFM drives the APB5 port: same transfer
  protocol, extras terminate in the shim). Fixture
  bridge_1x2_rw_apb5 (+_mon) in the manifest; sims 2/2 green;
  50 generator unit tests; 22/22 bridges regenerate — RTL
  byte-identical for all 21 pre-existing (TBs picked up one
  semantically-neutral template line). A5-3c CLOSED; next is A5-3a
  (store-class atomics + the axi5_atomic_filter IP).
  *Step 2 implementation map (as executed):* treat apb5
  as "the apb branch + 5 extra external pins" everywhere:
  (a) Axi4ToApbShim component gets protocol='apb4'|'apb5' (module
  name swap + connect_apb4_master emits the 5 extra pairs);
  (b) slave_adapter_generator: extend the protocol tests at lines
  ~90/97, ~328/330, ~507, ~634, ~724 to include 'apb5' and add the 5
  signals to _generate_apb_external_ports for the apb5 case;
  (c) SlaveAdapterInstance: allow 'apb5', external-interface branch
  += the 5 signals; (d) bridge_module_generator external apb port
  emission + validator (validate_protocol whitelist, and
  validate_apb_constraints applies to apb5 too) + config_loader
  protocol whitelist; (e) bridge_generator.py filelist emission: apb5
  slaves -f axi4_to_apb5_shim.f instead of the apb4 one; (f) fixture
  bridge_1x2_rw_apb5 (axi4 master rw, one axi4 + one apb5 slave) +
  generated tests + a hand-written check against the CocoTBFramework
  apb5 slave BFM; regen all bridges, zero drift on the existing 21.

**A5-3d — AXI5-Lite slaves (protocol="axil5"): LANDED 2026-09-05.**
Follows A5-3c beat for beat -- treat axil5 as "the axil branch plus the
AXI5-Lite sideband".

*The IP first:* `converters/rtl/axi4_to_axil5{,_wr,_rd}.sv`, wrappers over
`axi4_to_axil4_{wr,rd}` (AXI5-Lite keeps the AXI4-Lite transfer protocol
unchanged, so burst decomposition and response folding are inherited) plus
closure filelists. Sideband disposition is FORWARDED (lock/user/wuser, and
buser/ruser returning) / TIED (loop, mpam, mecid, nsaid, trace, poison) /
TERMINATED (bloop, btrace, rloop, rtrace, rpoison). Two design calls worth
recording:

- **The tied group has no `ENABLE_` parameter.** They are driven `'0`
  unconditionally, so a knob for them could not change the design --
  worse than no knob, because a reader sets it and believes something
  happened. Only `ENABLE_LOCK` and `ENABLE_USER` exist. Verilator agrees:
  the modules lint clean with UNUSEDPARAM *unwaived*.
- **The tied group's PORTS do exist.** An AXI5-Lite boundary whose shape
  changes with a config knob cannot be wired to a fixed external
  completer. Always present, always driven.

*One real bug, found and fixed before commit:* the AW/AR sideband must be
HELD, not passed through. The core decomposes, so one AXI4 AW handshake
becomes N AXI5-Lite ones, and `s_axi_awready` drops on acceptance -- the
master then presents the NEXT transaction's AW while beats 2..N are still
going out. The first version passed it combinationally, and burst A's beats
carried burst B's USER from beat 0. The fix mirrors the core's own
`r_aw_active ? r_aw_addr : s_axi_awaddr`. Only OVERLAPPING bursts can catch
it; sequential traffic cannot. Mutation-checked: RED against the unfixed
RTL, GREEN after.

*Generator, per the A5-3c map:* (a) new shared table
`bin/bridge_pkg/axil5_sideband.py` -- port names, widths, directions and
the ENABLE_ mapping in ONE place, read by the adapter, the shim component
and the bridge top, so the three port lists cannot drift; (b)
`Axi4ToAxilShim` gains `protocol='axil4'|'axil5'` (module-name swap +
sideband pairs + parameter suffix); (c) slave_adapter_generator protocol
tests extended and `_generate_axil5_sideband_ports`; (d)
SlaveAdapterInstance + bridge_module_generator external surfaces; (e)
validator/config_loader whitelists, plus `validate_axil5_features`:
`axi5_features` on an axil5 port accepts ONLY `user`/`exclusive`, and
REJECTS a tied group by name rather than ignoring it, so the config cannot
imply something it does not do; (f) filelist emission -f's the axil5
closures; (g) TB template picks the AXIL5 BFMs, with the import made
conditional so bridges without an axil5 slave stay byte-identical.

**Verified:** 63 generator unit tests (10 new, incl. one asserting the
table and the RTL name the same ports); fixture `bridge_1x2_rw_axil5` in
the batch manifest; 24/24 bridges regenerate with the 23 pre-existing
byte-identical in RTL *and* TB classes; the generated bridge lints at
parity with its axil4 sibling (13 PINCONNECTEMPTY vs 26, no new class);
generated bridge test 2/2 green; converter suite 8/8 across three levels.

**Not done, deliberately:** axil5 as a bridge MASTER protocol. apb5 is
slave-only too; a master-side AXI5-Lite requester is a different piece of
work and nothing in-tree needs one.

*Adjacent finding, now RESOLVED:* `make verilator` in
`projects/components/bridge/rtl` used to fail -- measured 2026-09-10 as 13
of 38 variants, all PINMISSING on one instance, and not deliberate. (An
earlier version of this note said "all 36 variants, entirely from
pre-existing PINCONNECTEMPTY on deliberate open pins"; both halves were
wrong, which is what a gate nobody runs buys you.) [[BRIDGE-013]] was the
cause and is closed: an internal slave no longer gets a monitor built and
left unconnected. Re-measured after the fix, same day: 38 of 38 variants
elaborate with zero errors and zero warnings, the `mon` variants included,
so the WIDTHEXPAND/UNDRIVEN noise this note attributed to
`rtl/amba/monitor/*` went with them. Nothing owed here.

**A5-2 design note (2026-08-09):** two slices.

- *Slice 1 — AXI5 slave ports, interop mode:* LANDED 2026-08-09.
  `axi5_master_{wr,rd}[_mon]` boundary wrappers on axi5-protocol
  slave ports, same feature whitelist, sideband terminates at both
  boundaries. Mixed-protocol fixture bridge_1x2_rd_axi5s (axi4 master,
  one axi4 + one axi5 slave) in the manifest; 46 generator unit
  tests; 19/19 bridges with the 18 pre-existing byte-identical; sims
  green incl. the mon variant. Known benign dangle: the axi5 slave
  adapter's xbar_*_arregion input (fabric has region, AXI5 doesn't).
  Deferred with slice 2: wr-channel axi5-slave fixture (wr path
  generated/compiled, not simulated).
- *Slice 2 — native sideband pass-through:* LANDED 2026-08-09.
  Implementation matches the design note below: shared spec table
  `bin/bridge_pkg/sideband.py` (feature -> per-channel struct fields:
  nsaid[4]/trace/mpam[11]/mecid[16]/uniq on aw+ar, trace on b+r,
  poison on w+r; `uniq` because `unique` is an SV keyword); `_pkg`
  structs carry the bridge-wide feature UNION (pure-AXI4 bridges
  byte-identical — zero-drift held across all 19 pre-existing
  bridges); master adapters pack own-feature fields from the
  wrapper's fub sideband on the DIRECT width arm and '0 on converter
  arms; the xbar forwards request fields unconditionally (non-native
  sources are already '0) and muxes b/r fields from featured slaves
  only; slave adapters ride `xbar_<slave>_axi_<sig>` nets into the
  axi5_master_* wrapper via the component's new `native_sideband`
  flag. Validator: `poison` moved from phase-gated to
  connectivity-gated (every connected path AXI5-both-ends +
  poison-enabled + width-matched, else ERROR — dropping POISON would
  launder corrupted data); droppable sideband that terminates
  mid-path now prints generation-time warnings. mte/chunking stay
  phase-gated.
  **Verified:** 47 generator unit tests (3 new poison rules); new
  native fixtures bridge_1x2_{rd,wr}_axi5n (+_mon) — the wr one
  closes the deferred wr-channel-AXI5-slave-sim item and exercises
  poison + per-slave feature asymmetry; hand-written VALUE tests
  drive arnsaid/artrace/arunique/awtrace/wpoison and assert the same
  values at the far boundary + rtrace/btrace return paths + rtrace=0
  from AXI4 slaves (closes the A5-1 deferred values item); all
  interop axi5 fixtures re-simed green with the new plumbing.

### BRIDGE-007: scrub the tests for completeness (bridge)

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** CLOSED 2026-09-10. The testqc round ran end to end: twelve units,
nine clean, one seed finding, two CONFIRMED and both fixed in the shared test
template (a boundary probe that accepted any exception as the expected
SLVERR; a write-path error raise that was dead for AXI-Lite masters). Against
the checklist below: every generated test drives its DUT through the BFMs;
the two assertions a bug could satisfy are gone and replaced by ones that name
the response code; gate/func/full are measured distinct (48 of 48 tests level-
compliant, 60/113/171-style grids and per-cell depths confirmed in the logs);
the generated wrappers pin one cocotb test each by design and every cocotb
test in every module has a wrapper; and every fix landed this week carries a
recorded mutation check, including the two A5-3b ones. Two more findings of
exactly this task's kind surfaced while signing off A5-3b and were fixed the
same day: an AtomicStore expectation that had encoded the BFM's old plain-
write behaviour, and a concurrency phase whose ID reuse violated the rule it
was meant to exercise. Bridge FULL regression 249/249 on 2026-09-10.
Originally: open 2026-09-04. Raised by Sean: test scrubbing was meant to be
part of the kimi review packets and got dropped along the way. Applies to the
components suites as well as rtl/.

**Sequencing.** A FOCUSED pass, run after qc/humanize is finished everywhere
and BEFORE coverage and formal are driven clean. Doing it after coverage would
mean chasing numbers produced by tests nobody has audited.

**Scope:** `projects/components/bridge/dv/tests/` -- 39 test files, the largest components suite, and almost all of it is generated.

**The capability already exists and was simply never run here.**
`bin/review/run_batch.py` has a `testqc` mode alongside `qc` and `humanize`,
with `bin/review/TEST_REVIEWER_BRIEF.md` as its brief and
`bin/review/build_test_review_bundle.py` to build the units. The brief audits
test collateral against the project's test contract and treats the
CocoTBFramework as reviewed ground truth rather than an audit target. Start
there rather than inventing a method.

**Why this is not busywork.** A test that passes because the RTL is broken is
worse than no test, and the repo has already produced them. The template is
apb5 (2026-09-04): nothing drove `rsp_ready`, so the response skid filled and
never drained, and the TB's completion check returned True on exactly the
state the defect produced. The suite was green BECAUSE the RTL was broken. The
witness added with the fix counted 59 protocol violations across 70 bus
completions on the unfixed design that no prior test had noticed.
**Area-specific:** the suite is generated, so a defect in the test generator
is replicated across every configuration at once. Audit the generator's test
template first; a finding there is worth 39 findings in the output. Note also
that generated tests must be regenerated, never hand-edited (CRITICAL RULE #0).

**What "complete" has to mean, at minimum:**

- Every `test_*.py` actually exercises the DUT it names.
- No test asserts a condition the bug itself satisfies.
- Inputs the DUT needs are actually driven.
- gate/func/full levels mean something distinct, not three names for one run.
- No `run()` call pins `testcase=` to a single cocotb test. A pinned
  `testcase=` silently hides every OTHER `@cocotb.test` in that module, so a
  test can sit in the file for months and never execute. `test_apb5_master.py`
  did exactly this (2026-09-04) -- a witness added beside the basic test ran
  zero times until the pin was widened. A comma-separated list is the fix when
  a pin is genuinely wanted.
- A fix landed with a test has a mutation check recorded: the test was seen
  RED against the unfixed RTL. Without that the test is decoration.

**Related:** [[TASK-078]], [[COMMON-025]], [[MATH-010]], [[CDC-001]] are the
same task in the rtl/ areas.

**Audit 2026-09-09, AMBA5 focus (hand audit against the checklist; the
testqc round has still not been run).** Measured on a clean FULL run:
72 passed / 0 failed / 0 reruns, 40 files, 6m08s. 63/63 generator unit
tests, 21 of them AMBA5 validator rules.

*Premise check first.* "Full AMBA5" is not what the tree does, and the
tests match the tree, not the phrase. Support is the interop scope:
AXI5 master and slave ports with native sideband (nsaid/trace/mpam/mecid/
unique/poison) and STORE-class atomics; AtomicLoad/Swap/Compare are
DECERR'd at the master boundary by `axi5_atomic_filter` (A5-3 read-return
routing is still not built); mte/chunking rejected by the validator;
axil5 and apb5 are slave-only. Every AMBA5 fixture is 1x2, single
master, all ports 32-bit.

Findings, in impact order:

1. **Levels: 0 of 40 compliant** (`check_test_levels.py`). The jinja
   template `bridge_test_file.py.j2` never reads REG_LEVEL, never exports
   TEST_LEVEL, and the TBs never read it -- so `run-all-gate`, `-func` and
   `-full` run the identical suite. Both halves of the HARD REQUIREMENT
   are missing, suite-wide, from one template. One fix, 40 files
   (regenerate, never hand-edit).
2. **No SEED anywhere.** No generated test or TB reads SEED or seeds an
   RNG; the only env reads are the boundary-probe mode and the xdist
   worker id. Same template.
3. **One test drives an AXI5 port with the AXI5 BFM**
   (`test_bridge_1x2_rd_axi5_bfm5`: `AXI5MasterRead` + compliance
   checker, 6 reads, read side only). Every other AXI5 fixture is driven
   by the AXI4 BFMs; `AXI5MasterWrite`, `AXI5SlaveRead/Write` and the
   write-side compliance checker (ATOP_*, POISON_PROPAGATION,
   TRACE_CONSISTENCY, NSAID/MPAM/MECID checks all exist in it) are never
   instantiated. The AXI5-only inputs (awatop, awtrace, arnsaid, wpoison
   ...) are left undriven on those fixtures -- Verilator zeros them, which
   is why it works.
4. **Sideband and atomics are hand-poked.** The two `_sideband` tests and
   the `_atomics` test set `dut.cpu_*_axi_awatop/awtrace/wpoison/arnsaid`
   directly beside an AXI4 BFM and sample the far side with a pin
   sampler. They do check values end-to-end (nsaid/trace/unique on AR,
   rtrace on R, wpoison on W, btrace on B; STORE routed with data
   verified in memory, LOAD and SWAP DECERR'd) -- but Compare
   (`0b11xxx1`) is not exercised, and the protocol-level checks the BFM
   would add (ATOP burst-length, atop-vs-response) are absent. This is
   the [[feedback_always_use_axi4_bfms]] rule's AXI5 twin.
5. **APB5 slave driven by the APB4 BFM.** `bridge1x2_rw_apb5_tb` imports
   only `APBMaster/APBSlave`; the framework has `APB5Slave/APB5Monitor`.
   The A5-3 note's "hand-written check against the apb5 slave BFM" does
   not exist in the tree. axil5 is correct (`AXIL5SlaveRead/Write`).
6. **Untested shapes:** AXI5 through arbitration (no multi-master AXI5
   fixture, so sideband muxing in the xbar's b/r return is unexercised);
   AXI5 across a width converter (droppable sideband terminating mid-path
   is only a generation-time warning, never simulated); mte/chunking
   rejection is unit-tested only, which is correct for a rejection.

Clean on the checklist: TB separation (dv/tbclasses, three reset methods
present), sources from `.f` filelists, every `cocotb_test_*` is pinned by
exactly one `run()` (no hidden tests), memory-backed slaves verify DATA
not just routing, boundary probes cover decode edges.

Recommended order: (1)+(2) in the template and regenerate all 40; then
an AXI5-BFM write-side test with the compliance checker on `wr_axi5a`
(atomics incl. Compare) and `wr_axi5n` (poison/trace), and an APB5 BFM
on `rw_apb5`; then a 2x2 AXI5 fixture. Then the testqc round.

**(1)+(2) DONE 2026-09-09 (Sean: "fix levels please").** 41 of 41 compliant;
grid GATE 72 / FUNC 144 / FULL 216 cells; clean runs at every level with 0
reruns (GATE 72/72 5m10s, FUNC 144/144 9m47s, FULL 216/216 9m38s), and the
FULL run's sibling cells prove distinct depth: 4x4 boundary probe 4s / 5s /
40s, arbitration 16 / 32 / 96 transactions, monitor ERR_BP 128 / 256 / 512
reads, BRIDGE-011 40 / 80 / 128 writes, atomics 1 / 2 / 8 rounds. Depth
profile lives in `dv/tbclasses/bridge_levels.py`; the 8-line REG_LEVEL grid
is per wrapper file (the val/common form); SEED is exported per cell and
seeds one RNG per TB. Three things had to be fixed on the way, each worth
more than the levels:

* **The generator could not regenerate its own tests.** BRIDGE-009's
  internal subtractive slave was templated as a real slave (a BFM on
  prefix "subtractive", probes into a 4 GB window at 0x0), so every
  regenerated test failed at TB construction -- which is why nobody had
  regenerated since 1d442e76, and why the tree carried the real arbitration
  test that a43b032dd hand-edited into seven generated files while the
  template still emitted the TODO stub, two hand-written tests inside the
  generated 2x2 file, and a TB method the template lacked. Fixed: test and
  monitor-test generation see external ports only; the template emits the
  real arbitration test and the `set_slave_response_delay` / `txn_id`
  helpers; the 2x2 tracking tests moved to hand-written
  `test_bridge_2x2_rw_tracking.py`. All 36 tests + 36 TB classes are
  regenerated from the template, RTL byte-identical.
* **The bridge conftest stamped REG_LEVEL into `os.environ['TEST_LEVEL']`,
  and cocotb_test lets the environment override `extra_env`** -- so the
  first leveled FULL run executed all 216 cells at full depth while the
  grid reported three levels. Stamp removed here; the same block is in
  twelve other conftests: [[TOOL-016]].
* **`check_test_levels.py` never followed Pattern B imports**, so a project
  TB that read TEST_LEVEL and one that never did both printed
  `depth:never-read`. Fixed, plus a WARNING for the conftest stamp. Under
  the fixed tool: stream fub 2 of 7, apbx-xbar 0 of 6, misc 0 of 4, rlb 0
  of 9 -- unmeasured before, real now.

Also fixed: the gate monitor stress count sat exactly at the 64-entry err
FIFO depth, so the ERR_BP saturation assertion was a race against the drain
pump (11 variants won, mix_d peaked at 58); gate uses 2x depth.

**(3)-(6) DONE 2026-09-09 (Sean: "beef up the tests").** Template-level, so
every fixture got it, verified FULL 237/237 (45 files, 0 reruns):

* **(3) AXI5 ports are driven by the AXI5 BFMs.** The TB template picks the
  BFM family per port protocol -- `axi5` -> `AXI5Master/Slave{Read,Write}`
  (every AMBA5 sideband field is optional in the framework's binding rule,
  so one BFM fits any feature subset), `apb5` -> `APB5Slave` at the
  generator's 1-bit USER widths -- and arms an `AXI5ComplianceChecker` on
  every AXI5 master port; every generated test calls `tb.assert_compliance()`
  before PASSED. 14 TBs now drive AXI5 BFMs, 2 drive APB5.
* **(4) No pin pokes.** The sideband and atomics tests drive
  nsaid/trace/unique/poison/atop as BFM transaction arguments and read the
  echoed trace from the BFM result; the slave-side samplers stay as
  observation. Compare (`0b110001`) added: store forwards, load/swap/compare
  answered DECERR by the filter, asserted as the EXPECTED response.
* **(5) APB5 slave on the APB5 BFM** (template).
* **(6) Two new fixtures**, generated with their own tests plus a
  hand-written sideband test each: `bridge_2x2_axi5` (two AXI5 masters with
  distinct NSAIDs contending for an AXI5 slave -- every slave-side AW/AR
  NSAID must belong to its issuing master and the counts must match; trace
  echoes from the AXI5 slave, returns 0 from the AXI4 one) and
  `bridge_1x2_rd_axi5w` (32b AXI5 master into a 64b AXI4 slave -- data
  round-trips through the converter, trace returns 0; native path echoes).

Two framework findings on the way, both fixed in RDS-DV: the out-of-range
disagreement ([[BRIDGE-008]], closed) and `write_transaction` returning
`response=None` on an error B (19f866b) -- the generated `master_write` now
raises on an error response, which is how the atomics test caught that a
DECERR used to pass through the helper silently.

**The compliance checker was vacuous, and had been since 2026-08-09.**
Arming it in every TB is what exposed it: the first summary line printed
empty statistics. `AXI5ComplianceChecker.setup_monitors` built its channel
monitors without a `protocol_type`, so every AMBA5 sideband field was
REQUIRED; on any real port the AR monitor failed to bind, the failure was
caught and logged as a WARNING, the checker set `enabled=False`, and
`get_compliance_report()` returned `compliance_checking: disabled` -- which
the bfm5 sign-off test had been reading as "zero violations" for a month.
The AXI4 checker had the identical defect. Fixed in RDS-DV (9505cce,
6b35cc9): monitors take the BFMs' per-channel `protocol_type`, a setup
failure raises, and a structural unit test pins both. The generated
`assert_compliance()` now refuses a checker that is not `enabled` or that
performed zero checks. Measured after the fix on one gate cell: checker
active on AR/R, 294 checks, 2 AR transactions -- a verdict with something
behind it.

**Every AXI master port now carries a protocol checker, AXI4 as well as
AXI5 (2026-09-10).** The TB template arms `AXI4ComplianceChecker` on every
`axi4` master port alongside the AXI5 one, and `assert_compliance()` requires
the report to be `enabled`, `armed`, and to have performed a non-zero number
of checks before it will accept "zero violations".

Arming it found a second blind-checker defect, one layer below the one found
yesterday: `_has_channel_signals` concatenated the port prefix naively, so a
port written `cpu_m_axi` rather than `cpu_rd_axi_` resolved NO channels --
no monitors, `monitors_active` False, both loops returning immediately -- and
the report still said `enabled` with zero violations. `bridge_2x2_rw`
reported "0 violation(s) in 0 checks" and the `checks > 0` assertion caught
it. Fixed in RDS-DV (`09ef5dc`): the prefix is resolved against both
spellings, a checker that binds nothing logs a WARNING, and the report now
carries `armed` and `channels` so a caller can refuse a verdict with nothing
behind it. With that, `bridge_2x2_rw` checks both masters at 1790-4505 checks
per cell, zero violations.

**The testqc round is RUNNING (2026-09-10) -- the first on any
projects/components area.** Getting there needed three fixes to the review
pipeline, which is why no such round had ever run:

* `build_test_review_bundle.py` only looked under `val/<area>`. It takes a
  path now, so a Pattern B area can be bundled at all.
* It resolved `TBClasses.*` and `CocoTBFramework.*` imports but not
  `projects.components.<c>.dv.tbclasses.*` -- so a Pattern B bundle would
  have shipped its tests with NO testbenches and the reviewer could not have
  seen what the tests drive.
* `RTL_IFACES.sv` came out EMPTY: the bundler re-parsed the `.f` itself,
  skipping any line starting with `-` or `+` and never expanding
  `$REPO_ROOT`, which is 707 `-f` lines and 311 `$REPO_ROOT` lines across the
  bridge's filelists. It uses the repo's own `get_sources_from_filelist` now.
* `FRAMEWORK.py` is reduced to its API surface, which is what its GOLDEN
  banner says it is for. Full bodies were 364 KB of a 490 KB unit and pushed
  every single test over the size limit.

**Scope: 12 units, not 45.** The seven hand-written tests plus five
representative generated ones (simple rd, multi-master rw, mixed-protocol,
monitor stress, apb5). This task's own text says why: the suite is generated,
so "audit the generator's test template first; a finding there is worth 39
findings in the output" -- reviewing 45 near-clones would spend the budget
proving the same thing forty times.

*First unit's findings (part_01, test_bridge_1x2_rd):* one real, in code
written the same day -- `seeded_rng()` fell back to a FIXED seed of 0, and
`TBBase` drew a seed without publishing it, so a TB built outside the pytest
flow would freeze its address RNG while logging a seed that does not replay
the run. Fixed at both ends: TBBase now writes its drawn seed to
`os.environ`, and `seeded_rng` draws instead of pinning 0. Also acted on: the
generated TB reported `addr_width=64 / id_width=8` while every fixture's
ports are 32/4 -- vestigial template constants, now derived from the ports.
Everything else in that unit was confirmed against the contract.

*Round complete, 2026-09-10: all 12 units reviewed and triaged.* Nine came
back clean against the contract. One produced the seed finding recorded
above. Two were CONFIRMED, and both were the same class of defect -- an
assertion that the bug itself satisfies -- which is exactly what this task
was raised to catch, and both were in the shared test template, so each fix
propagated to all 45 generated tests at once.

**part_10 -- the boundary probe swallowed any exception as proof.** The probe
walked addresses past the end of the map expecting a decode error, and its
`except RuntimeError` accepted whatever came back. A timeout, a BFM teardown,
a driver bug and a genuine SLVERR were indistinguishable, so a decode defect
confined to addresses above the 64 KB seed cap would have passed the entire
suite. The reviewer's phrasing is worth keeping: the test proved that
something went wrong, never that the right thing went wrong.

**part_12 -- the write path's error raise was dead for AXI-Lite masters.**
`master_write` raised on a bad response, but the three BFM families report
failure three different ways: a dict with a response field, a raised
`RuntimeError`, and a bare integer code. Only the first was handled, so on
every AXI-Lite fixture the raise could not fire and the probe's expectation
was unreachable.

**The fix, in the template rather than the output.** A new `AxiResponseError`
carries the numeric response alongside the message, `master_write` and
`master_read` normalise all three BFM shapes into it, and both probes now
assert `is_slverr` instead of accepting any failure. A probe that cannot
determine the response code re-raises rather than passing. Regenerated across
all 26 configurations per CRITICAL RULE #0.

*Mutation check.* The discrimination was verified RED before GREEN: with the
old accept-anything handler the probes passed against a response the new
assertion rejects.

*A note for whoever reads the run logs.* The FULL run that validated this
reported 8 failures, and none of them were the bridge. All eight were one
shared file, `rtl/common/fifo_control.sv`, caught half-written by another
agent mid-conversion to the reset macro -- Verilator died on an unterminated
macro argument list at EOF. The tell was that every failure was a build exit,
not an assertion. On a shared tree, read the error kind before reading the
test name.


---
