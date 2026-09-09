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
