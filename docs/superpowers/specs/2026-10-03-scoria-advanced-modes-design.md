# scoria advanced modes (TASK-001) — design

**Date:** 2026-10-03
**Status:** approved in conversation (design sections presented and corrected); awaiting spec-file review
**Task:** scoria-ddr3-lpddr3 TASK-001 (the advanced scheduling / refresh modes survey and implementation)
**Scope ruling (Sean, 2026-10-03):** implement the bounded commodity-legal tranche in RTL (Modes A-C below); the research-grade candidates are surveyed and planned with named unblock conditions, not implemented. Per-mode design lives in `design-requirements.md` (pumice's pattern); no scoria MAS is authored by this work. **CSR offsets may be reorganized for logical placement** — the access contract is name-based through the generated regmap, not offset-based.

---

## 1. Context and grounding

TASK-001 seeds eight candidates: LPDDR3 per-bank refresh (already inherited —
HAS Ch 3.4, `REFpb` rotor), RAIDR, temperature-compensated refresh (TCR),
elastic refresh, SALP, ChargeCache, PARA/Rowhammer targeted refresh, and
self-refresh/power-down scheduling, plus ZQ calibration scheduling. This design
implements three; §6 carries the rest.

What exists in the RTL today (measured, not assumed):

- **Elastic core**: `scoria_refresh_ctrl` implements the JEDEC ±8
  postpone/pull-in credits (`REF_CTRL.postpone_limit`/`pullin_limit`) keyed
  off a one-cycle binary `demand_i`. The demand-*aware* layer is absent.
- **TCR**: `TEMP_DERATE_RANK0` exists but is LPDDR3-MR4-shaped — hardware
  written, software read. DDR3 has no MR4; temperature arrives as a
  firmware-written class (board sensor → host). No DDR3-usable derate input
  exists.
- **ZQCS placement**: `scoria_zq_ctrl` implements request/grant with interval
  countdown, `zq_overdue`, and issued counters. HAS Ch 6 Q2's revisit
  condition — "if characterization shows ZQCS starved under sustained demand,
  placement becomes TASK-001's scheduling question" — is live and instrumented.
- **Telemetry**: `SCHED_STATS_*` / `PAGE_STATS_*` / `REF_STATS_*` exist; the
  pumice characterization pattern (sweep by CSR, compare in-system) carries
  over.
- **ZQ_CFG reserved space**: bits 15:1 are unused (`zq_enable` at 0,
  `t_zqcs` at 31:16); Mode C's fields fit without moving anything.

## 2. The three modes

Every mode obeys the standing rules: reset = baseline bit-identical (all new
fields reset to today's behavior; pumice's one deliberate shipped exception
does **not** extend here), and the RDL regenerates through
`bin/peakrdl_generate.py` (RTL + docs + Python regmap together, never raw
peakrdl).

### Mode A — demand-aware elastic refresh

`REF_CTRL.elastic_en` (reset 0 = today). Two CSR thresholds on the *existing*
credits, no new credit arithmetic, JEDEC ±8 remains the hard ceiling:

- Pull-in fires only after demand has been idle ≥ `pullin_idle_streak` MC
  cycles. This generalizes the inherited 16-cycle sustained-idle confirmation
  (HAS Ch 3.4's note) into a sweepable CSR behind the enable.
- Postpone engages only under a sustained demand streak ≥
  `postpone_demand_streak`.

Telemetry: `REF_STATS` gains a postpone/pull-in histogram bin pair so the
sweep is measurable in-system.

### Mode B — temperature-compensated refresh (TCR)

`REF_CTRL.tcr_en` + `trefi_derate[1:0]` (reset off / 1x). Firmware writes the
derate class (1x/2x/4x — JESD79-3F 7.3.3 refresh-rate cases); `refresh_ctrl`
scales the tREFI tick accordingly. `TEMP_DERATE_RANK0` keeps its LPDDR3-MR4
hardware-written path untouched for the future LPDDR3 build; the DDR3 path is
the new software-written select.

The retention formal property is **re-derived with the derate factor in the
interval arithmetic** — HAS Ch 6's rule that a changed interval changes the
proof, never carried forward green.

### Mode C — ZQCS placement policy

`ZQ_CFG.placement[1:0]` (reset 0 = today's request-on-expiry) +
`ZQ_CFG.overdue_max`. Policy 1 *defer-under-demand*: hold the request while
demand is sustained, up to `overdue_max`; the existing `zq_overdue` and
issued counters make starvation measurable — exactly the Q2 revisit
condition's instrument. Policy 2 reserved. The Q2 answer stands in all
policies: request/grant, never preempt.

## 3. CSR surface policy

New fields are placed in the logically-owning register where reserved space
allows (Mode C fits in `ZQ_CFG`'s free bits). Where a register has no
reserved space, the register group may be reorganized and **offsets moved** —
authorized by Sean 2026-10-03 — because the access contract is name-based via
the generated regmap (HAS Ch 4.2's rule; host code never hardcodes offsets).
Every offset move is recorded in the RDL comment for that register and in the
generated docs.

Touched groups: `REF_CTRL` (Mode A enables + thresholds; Mode B enable +
derate), `ZQ_CFG` (Mode C), `REF_STATS` / `ZQ_STATUS` (telemetry). The
retired-placeholder convention ("address kept so the map does not shift") is
superseded by this authorization for registers this work reorganizes.

## 4. Documentation updates

- `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/docs/design-requirements.md`
  gains **"6. Advanced modes"**: the survey of all eight seeds with the
  commodity-legal vs model-only split, the three bounded modes specified to
  implementation depth (this design, expanded), and the named unblock
  conditions of §6.
- `PRD.md` roadmap: TASK-001 entry updated — bounded tranche landed, survey
  in design-requirements §6, deferred items with conditions.
- HAS Ch 6 (`ch06_integration/01_verification_open.md`): pointer to §6 and a
  note that Modes A-C exist behind CSRs (TASK-008's marking-confirmation
  bookkeeping absorbs the detail).

## 5. Verification, per mode (pumice's red→green)

Each mode, in order:

1. A failing FUB test against the real RTL first (the faithful-model check
   the mode's contract names), watched red.
2. The RTL behind its enable; the same test green.
3. A macro-tier composition test through `scoria_mem_cmd_scheduler` with
   demand driven realistically.
4. For Modes A and B: the retention property re-proved in `formal/scoria`
   with the new arithmetic (credits + derate). Mode C: the existing ZQ
   proofs (if any) re-run; spacing properties through `cmd_history_checker`.

Standing gates after all modes: verilator lint, the pre-existing regression
suite green (221 tests as of v0.8, more after the new suites land),
`bin/check_task_ids.py`, and the OOC synthesis re-measured for BUG-003
interaction (these blocks are not the arbiter pick cone, but the numbers are
re-checked, not assumed).

## 6. Deferred candidates, with named conditions

| Candidate | Class | Unblock condition |
|---|---|---|
| RAIDR (retention-aware refresh) | research | a retention-profiling path exists (board or model) to feed per-row/bin data; Bloom-filter bin hardware is its own design |
| ChargeCache | research | BUG-003 timing headroom — it makes the arbiter cone hotter, the opposite of what the 100 MHz closure needs now |
| PARA / Rowhammer targeted refresh | research | after a bitstream exists, with a Rowhammer test methodology; adjacency tracking is its own design |
| SALP | model-only | belongs to andesite (DDR4/LPDDR4) per the task's own split |
| Self-refresh / power-down scheduling | excluded by decision | reverses the recorded 2026-09-30 HAS decision (dormant `powerdown_ctrl`/`dfi_signal_pack`); re-opened only by the owner |

## 7. Risks

- **BUG-003 interaction**: Modes A-C touch `refresh_ctrl` and `zq_ctrl`, not
  the arbiter pick cone; still, OOC timing is re-measured after the RTL lands.
- **Scope honesty**: this delivers three bounded modes plus the survey; it
  does not deliver the research-grade mechanisms, the MAS, or power-down.

## 8. Done when

- design-requirements §6 written; PRD roadmap and HAS Ch 6 updated.
- Modes A-C implemented behind CSRs, RDL regenerated through the house
  wrapper, generated docs + regmap in the same commit.
- Per-mode FUB red→green and macro composition tests; Modes A/B retention
  re-proofed; the pre-existing regression suite + lint green; check_task_ids
  green.
- BUG-003 OOC synthesis re-run with the new RTL (numbers recorded in the
  bug, whatever they say).
- TASK-001 updated: implemented-tranche items checked, deferred items
  carrying §6's conditions; vault INDEX counts current.
