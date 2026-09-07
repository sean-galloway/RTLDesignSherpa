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
