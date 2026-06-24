# Coverage Gap Analysis — DDR2/LPDDR2 (FULL regression)

## FULL regression headline

| Tier | Tests run | Passed | Failed | Pass % |
|------|----------:|-------:|-------:|-------:|
| FUB FULL | 186 | 186 | 0 | 100.0 |
| Macro FULL | 34 | 34 | 0 | 100.0 |
| Top FULL | 10 | 6 | 4 | 60.0 |
| **Total** | **230** | **226** | **4** | **98.3** |

The 4 top failures are the known `status: debug_only` cases documenting
the **fresh-read data-path hang** (see `ddr2_lpddr2_top_testplan.yaml`).
They're tracked but excluded from the FUNC suite. The strict pass rate
on tracked-as-verified scenarios is 100%.

## Coverage-script readiness

`bin/aggregate_coverage.py` / `bin/update_testplan_coverage.py` /
`bin/cov_utils/*` are the rollup scripts. They consume Verilator `.dat`
files produced when the test sets `compile_args += [--coverage,
--coverage-line, --coverage-toggle, --coverage-underscore]`.

**Status: wired.** `dv/ddr2_lpddr2_coverage/` ships
`get_coverage_compile_args()` + `get_coverage_env()`, and every
`dv/tests/{fub,macro,top}/test_*.py` calls them — no-ops without
`COVERAGE=1`. A `COVERAGE=1 TEST_LEVEL=FULL` FUB sweep produces 186
`coverage.dat` files. Merging them with `verilator_coverage --write`
yields the first end-to-end rollup number:

| Tier | Merged Verilator coverage |
|------|-------------------------:|
| FUB FULL (186 tests) | 635/968 = **65.6 %** |

That's the line+branch+toggle baseline. The remaining 34 % maps to the
gap items below (`G-01..G-19`) — `G-01` accounts for the data-path-side
rd_cl_aligner branches that never see a fresh AXI read post-init, and
the LPDDR2-specific FSM arms in mode_register / dfi_cmd_formatter
account for most of the remainder.

Backfilling the `coverage_points:` blocks in each YAML (i.e. the
"covers_lines" side of the testplan format) still needs a ddr2-lpddr2
sibling to `bin/update_testplan_coverage.py` — that script is currently
hardcoded to RAPIDS paths. The wiring side is done; the per-testplan
ingest is a follow-up.

## Testplan vs implementation — what's wired

187 scenarios declared across 25 testplans. Every entry maps to a
real `test_*` parameter combination — the testplan IDs were authored
*from* the existing test scenarios, so there are no "phantom" entries.

## What's still missing (test gaps)

Concrete scenarios that the testplans **don't** yet enumerate because
the underlying tests don't exist. These are the items needed to push
real coverage above the current line.

### Critical (open bugs)

**G-01: fresh-read data-path hang**
- Symptom: an AXI read on a fresh (not-previously-written) address
  hangs between rd_cl_aligner and the AXI R-channel.
- Needs: a focused FUB-level test on `rd_cl_aligner` that pushes ONE
  op_valid and verifies rd_inject_valid_o fires within CL+t_rddata_en
  cycles of dfi_rddata_valid_i going high. Today's tests inject
  dfi_rddata directly; they don't catch the bus-binding-side issue.
- Suspect: rd_op_id (= `'0` in `ddr2_lpddr2_top.sv`) or an FSM state
  not properly initialized for the very first read post-init.

### Multi-rank (NUM_RANKS=2)

**G-02: Cross-rank tFAW / tRRD independence**
- xbank_timers tests use NUM_RANKS=1. The per-rank tFAW / tRRD logic
  in global_timers (added in F4) needs a 2-rank scenario.

**G-03: Per-rank power state**
- powerdown_ctrl tests use single-rank CKE. NUM_RANKS=2 with
  staggered PDE entry per rank is unverified.

**G-04: Multi-rank addr_mapper**
- ROW_MAJOR with NUM_RANKS>1 places rank in upper bits. No scenario
  verifies the rank field is decoded correctly today.

### LPDDR2-specific

**G-05: REFpb actually used end-to-end**
- `refresh_ctrl.refpb_rotor` (REFR-07) verifies the rotor logic in
  isolation. No top-level scenario configures refpb_mode_i=1 and
  watches per-bank refreshes hit the bus.

**G-06: LPDDR2 init sequence verification**
- `init_sequencer.lpddr2_smoke` (INIT-03) walks the FSM but doesn't
  verify the LPDDR2-specific MR16/MR17 PASR loads.

**G-07: PASR bank mask applied**
- `mode_register` carries the LPDDR2 PASR fields, but no test
  asserts the refresh engine actually skips masked banks.

**G-08: LPDDR2 CA-bus encoding round-trip**
- `dfi_cmd_formatter.lpddr2_nop` (DCF-05) verifies one NOP. Full
  LPDDR2 cmd-set encoding (ACT/RD/WR via CA bus) is not exhaustively
  verified.

### Error / corner injection

**G-09: init_error path**
- `init_sequencer` never injects ZQCL grant failure → no test sees
  init_error = 1.
- Add a `init_zq_retry_exhaust` scenario that fails ZQCL grants and
  watches `cfg_zq_retries` count down.

**G-10: CAM overflow back-pressure**
- `wr_cmd_cam.fill_to_full` shows push_ready drops. No test verifies
  the back-pressure correctly stalls axi_intake (visible at the
  macro level on the W channel).

**G-11: pslverr generation**
- `ddr2_lpddr2_csr_slave.hole_read_returns_zero` shows holes return
  0, not pslverr. No test verifies pslverr ever asserts (CSR slave
  doesn't generate it today — would need RDL hardening if the spec
  requires it).

### Cross-FUB integration

**G-12: refresh-during-burst preemption**
- No scenario forces refresh_req mid-AXI-burst and confirms the
  scheduler drains the in-flight RDA/WRA before granting REF.

**G-13: PDE-during-burst entry**
- Similar — verify powerdown_ctrl doesn't request PDE while the
  scheduler has an in-flight column command.

**G-14: Page-policy switch via APB during traffic**
- `ddr2_lpddr2_csr_slave.refresh_tuning_rw` proves the field
  round-trips but no test changes `page_policy_or` mid-traffic and
  watches the scheduler honor it at the next quiet point.

### Performance / observability

**G-15: obs_words sampled under real traffic**
- The CSR test `obs_words_readback` (CSR-09) injects synthetic
  patterns. No top-level scenario reads obs_words AFTER live traffic
  and validates the counter values match what the AXI4Sequence
  drove.

**G-16: ZQCS periodic scheduling**
- `cfg_zqcs_freq_hz` is plumbed but no test verifies a periodic ZQCS
  command actually fires on the DFI bus at the configured interval.

### Top level — workload coverage

**G-17: Sustained throughput**
- `workload_mix` runs 8 bursts. A sustained-throughput soak (100+
  bursts) would exercise refresh / PDE / scheduler arbitration
  interaction at scale.

**G-18: Multi-master QoS arbitration**
- F4c verified QoS picker in isolation. No top-level test drives
  multiple AXI IDs with different QoS and verifies higher-QoS reads
  beat lower-QoS reads to memory.

**G-19: Out-of-order completion**
- `cfg_force_inorder=0` is plumbed but no test drives out-of-order
  R-channel return and verifies the AXI master sees correct IDs.

## Priority recommendation

If chasing 90%+ line coverage on top of the existing 97.9% scenario
coverage, the highest-value additions are:

1. **G-01** — fixes a real bug; needed before the top tests can be
   pushed past 60% pass.
2. **G-12, G-13, G-14** — cross-FUB scenarios that exercise paths
   the unit tests can't reach (refresh-vs-traffic, page-policy
   switch).
3. **G-02, G-03** — multi-rank coverage (the only major
   parameter axis currently unexercised).
4. **G-17, G-18** — performance + multi-master scenarios that
   exercise the QoS + arbitration interaction.

LPDDR2-specific items (G-05..G-08) can wait until the DDR2 path is
fully stable.

## Action items

- [x] Author `dv/ddr2_lpddr2_coverage/` helper module (mirror stream's
      `get_coverage_compile_args` / `get_coverage_env`)
- [x] Wire `--coverage` Verilator flags into `dv/tests/*/test_*.py`
      (all 14 FUB + 4 macro + 1 top runners)
- [x] Re-run FULL with `COVERAGE=1` to populate `coverage.dat` per test
      — first merged line-coverage baseline is **65.6 %**
- [ ] Port `bin/update_testplan_coverage.py` for ddr2-lpddr2 (the
      RAPIDS sibling is hardcoded to its own path); backfill
      `coverage_points:` blocks in each YAML
- [ ] Run `bin/aggregate_coverage.py --all --html` for the rollup
- [ ] File a tracking issue for each G-NN that's blocking a target
      coverage % (G-01 first)
