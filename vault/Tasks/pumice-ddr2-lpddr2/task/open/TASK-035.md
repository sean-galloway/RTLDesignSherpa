# TASK-035: finish pumice's formal coverage — 5 of 27 blocks proven

**Priority:** P3 — the blocks where a wrong answer damages a device or corrupts
data silently are already done; what remains is depth, not exposure.
**Status:** open 2026-09-28
**Owner:** TBD
**Related:** [[ISSUE-019]] (tier 1 below is how to settle it), [[TASK-034]]

## Where it stands

`formal/pumice/` exists as of 2026-09-28: **5 modules, 11 sby tasks, 11/11 PASS**
(`python3 bin/formal_status.py --areas pumice`). Wired in as
`make -C formal formal-pumice` and into the top-level `formal:` list.

| Proven | What it closes |
|---|---|
| `bank_timer` | the six per-bank JEDEC windows + the three K-map cross-module implications |
| `global_timers` | tFAW/tRRD/tWTR/tRTW/tCCD; found and fixed [[ISSUE-018]] |
| `refresh_ctrl` | the retention headroom, for all 16 postpone CSR values |
| `pumice_rd_return_ring` | the occupancy level sim structurally cannot see, no-fabrication, end-to-end data integrity |
| `addr_mapper` | injectivity (no aliasing) across every `bank_lsb`, hash on or off |

Each carries mutation evidence in its wrapper header, and every wrapper uses the
sv2v-flatten flow because yosys cannot parse `pumice_pkg.sv`.

## What is left, ranked by what a bug there would cost

**Tier 1 — a bug is silent on the wire and expensive to find.** Do these next.

| Block | Lines | The property worth proving |
|---|---:|---|
| `pumice_cmd_arbiter` | 1613 | no two `evt_act_o` closer than `t_rrd_i`, none five inside `t_faw_i` — **this settles [[ISSUE-019]]**; also that every fired command was permitted by the gate it claims to honour |
| `pumice_wr_data_cam` | 798 | a beat written is the beat drained, in order, with no slot reuse before its drain (the family of the fixed `wr_data_cam` bug) |
| `pumice_rd_cmd_cam` | 317 | a ticket is allocated once, freed once, and never issued for a free slot |
| `pumice_dfi_cdc` | 247 | the async-FIFO crossing: no beat lost or duplicated across the domain (the one block where a bug is a metastability class, not a logic one) |

**Tier 2 — a bug shows up as a stall or a wrong count, so sim finds it.**
`pumice_rd_intake` (503), `pumice_wr_intake` (435), `pumice_dfi_cmd_path` (416),
`dfi_cmd_formatter` (416), `init_sequencer` (407), `pumice_page_policy` (303),
`pumice_dfi_rd_aligner` (255), `mode_register` (204),
`pumice_axi_burst_chopper` (199), `pumice_wr_splitter` (189),
`powerdown_ctrl` (163), `dfi_signal_pack` (120),
`pumice_dfi_wr_serializer` (109).

**Tier 3 — thin wrappers and macros over already-proven parts.**
`pumice_bank_timers` (116, instantiates the proven `bank_timer`),
`pumice_cmd_history_checker` (264, itself a checker),
`pumice_mem_cmd_scheduler` (623), `pumice_axi4_ifc` (617),
`pumice_dfi_layer` (360). Macro-level proofs are usually better spent as a
handful of integration properties than as a full wrapper.

## Definition of done

This task closes when **tier 1 is proven** — not when all 27 blocks are. Tier 2
and 3 should be reconsidered as a separate item at that point, because the
marginal value drops sharply once the silent-failure blocks are covered and the
cost per block does not.

Per block, "proven" means all four of:

1. `prove` and `cover` both PASS under `make -C formal formal-pumice`.
2. **Every cover point reached.** An unreachable cover is the first sign a
   property is vacuous — see `vault/handbook/dv/formal.md`.
3. **At least one mutation per property family FAILS the proof**, recorded in the
   wrapper header. A property that cannot fail is not coverage.
4. The wrapper states its environment assumptions explicitly and does not assume
   away the hazard (ISSUE-018 was found precisely by assuming only what a block
   publishes).

## Traps already paid for

* **sv2v flatten is mandatory.** yosys stops at `pumice_pkg.sv:131` (a multi-line
  `return` in a package function). Wrappers carry no package import and use
  immediate assertions in `always @(posedge clk)`; concurrent
  `assert property (@...)` is rejected by that frontend.
* **Use bitwuzla, not z3,** for anything with a memory array — 14 seconds versus
  never finishing on `pumice_rd_return_ring`. Split an expensive property family
  into its own sby task via `chparam`, and make the area `prove` target run both.
* **Bound each input past what the OTHER bounds already imply,** or the property
  is vacuous while every cover still passes. `a_tfaw` survived a mutation that
  broke the tFAW window outright because tRRD's range already forced the spacing.
* Flat files are untracked in this area on purpose — see `formal/pumice/.gitignore`.

---

## Tier-1 sweep, 2026-09-29 -- what landed and what did not

The area is now **9 modules / 19 sby tasks, all green**
(`make -C formal formal-pumice`). All four tier-1 blocks have proofs running in
the gate. Two are complete against this item's own criteria and two are not, and
the difference is worth stating precisely rather than averaging away.

| block | state | headline property |
|---|---|---|
| `pumice_cmd_arbiter` | **complete** | composed with the real `global_timers`; **found [[BUG-021]]** |
| `pumice_rd_cmd_cam` | **complete** | ticket integrity + the age-order matrix as a strict order |
| `pumice_wr_data_cam` | partial | framing + lifecycle proved; **commit data integrity NOT** |
| `pumice_dfi_cdc` | partial | init-latch monotonicity only; **token/data pairing NOT** |

### The result that justifies the exercise

`pumice_cmd_arbiter` was the block this tier existed for, and composing it with
the REAL `global_timers` -- not free `*_ok_i` inputs, which would prove nothing --
produced [[BUG-021]]: two ACTs to different banks one cycle apart with `t_rrd=3`,
the second firing while the timers already say not-ok. It survives the CAM
age-order invariant **proved** in `rd_cmd_cam`, so it does not rest on a CAM
state the real CAMs cannot produce. That is exactly the hazard [[ISSUE-019]]
predicted and closed on "not observed", and it is now reproducible in one
command.

### What remains: two properties, each blocked on something specific

**1. `wr_data_cam`: "a beat written is the beat drained".** Five models of it
were wrong, each recorded in the wrapper. The blocker is attribution: the drain
is started by an upstream DECISION rather than by `commit_valid/ready` (a beat
fires at cycle 11 for a commit whose handshake lands at cycle 12), and entry
slots are not SRAM slots. The fifth model -- shadowing the SRAM by the DUT's own
`w_fill_idx`/`w_rd_idx` -- produces a readback counterexample that is left
DISABLED and uncorroborated. **Corroborating or refuting that counterexample is
the first step**, and it is the one piece of this item that could be a
data-corruption defect.

**2. `dfi_cdc`: token/data pairing and the rising-edge push.** Blocked on
hierarchical NAME RESOLUTION in that block specifically: it instantiates five
FIFOs with near-identical flattened net names, and the first version asserted on
wires that demonstrably were not the source signals. Hierarchical access itself
works here -- `wr_data_cam` uses it -- so the fix is to check the flattened names
against the source instance by instance, which is mechanical.

### A capability worth knowing about, discovered doing this

**Hierarchical references into the sv2v-flattened DUT work under yosys.**
`dut.w_dq_rd_slot` elaborates. That was assumed impossible when this item was
written, and it is what makes SRAM-level and internal-anchor properties
expressible at all. It is also what makes remaining item 1 tractable.

### Traps paid for, added to the list at the top of this item

* **Labelled assertions inside a `for` loop** create one cell per iteration with
  the same name and yosys rejects the build. Compute a predicate in the loop and
  assert it ONCE -- which also keeps the failure named.
* **Counters must start where the assertion starts.** Counting from reset while
  asserting from `f_past_valid > 2` lets the two diverge in the untested window
  and reports it as a mismatch for ever, with the instantaneous property holding.
* **Count handshakes, not offered signals.** A push qualified by only half its
  ready condition asserts into a full FIFO and stores nothing.
* **The filelist is the dependency authority.** Hand-assembling `dfi_cdc`'s
  closure missed `gray2bin` and `counter_bingray` and the build failed outright.
