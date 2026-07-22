# Advanced Scheduling / Refresh Modes — DDR3 / DDR4 Roadmap

Model-only DRAM scheduling/refresh mechanisms that were **removed from the
`pumice-ddr2-lpddr2` project** (they need DRAM-chip / JEDEC-command changes the commodity
DDR2/LPDDR2 device does not implement, so they cannot run on the Nexys A7 DDR2 part).
They are parked here and assigned to the future `ddr3-lpddr3` / `ddr4-lpddr4` projects,
where the standard either makes them commodity-legal or where a faithful DRAM model is
the right home for the research schemes.

- **Commodity-legal modes stay in `pumice-ddr2-lpddr2`** — see
  `pumice-ddr2-lpddr2/docs/design-requirements.md` ("Advanced modes" section): all
  scheduling policies, all page policies, REFab / REFpb-round-robin, JEDEC ±8
  postpone/pull-in scheduling.
- **Papers** (algorithms preserved; re-derive when implementing):
  `/mnt/data/github/dfi-specs/ddr2-lpddr2/papers/` — Chang 2014/2016 (DSARP), Nair 2014
  (refresh pausing).

## Design philosophy — support the basics, illustrate the situational "spice"

Each tier (DDR2 → DDR3 → DDR4/LPDDR4) must **support the basic, standard version of that
technology's native mechanisms** (the table stakes: FR-FCFS, open/closed page, REFab, the
JEDEC ±8 refresh, and whatever the JEDEC spec adds at that tier — per-bank refresh, FGR,
bank groups). Beyond that, the *teaching* value of this family is to **illustrate the
lesser-known, sometimes-better-for-a-specific-situation** alternatives — the clever or
counter-intuitive schemes that a production controller usually skips. Every mode is
config-bit-selectable so **one bitstream demonstrates *when* each wins** by sweeping a CSR
against the same traffic.

So each mechanism below (and in every project's "Advanced modes" section) carries a
**"wins when"** tag — the specific situation it beats the default in — not just "it exists."
Curated situational cheat-sheet across tiers:

| Situation | Lesser-known lever that wins | Tier |
|---|---|---|
| Streaming/strided, high row locality | `static_open` / `most_pending` column selection | DDR2 |
| Random / low locality | `static_close` + auto-precharge fusion | DDR2 |
| **Mixed** — some rows hot-but-thrashing | **RBLA** (decide on row-buffer *misses*, not accesses) | DDR2 |
| Phase-changing locality | `adapt_time` (Happy Intel-adaptive per-bank timeout) | DDR2 |
| Low-demand rows starving the bus | **`fewest_pending`** column selection (counter-intuitive: drain the *least*-wanted row so it precharges sooner) | DDR2 |
| Latency-critical reads under write pressure | `load_over_store` + write-batching watermarks | DDR2 |
| Adversarial power-of-2 strides hot-banking | XOR / **permutation (prime-modulo, bit-reversal)** address hashing | DDR2/3 |
| Refresh-power / high-density bound | **RAIDR** retention-aware (weak rows often, strong rows rarely) | DDR3 |
| Thermally variable | temperature-compensated refresh (scale tREFI) | DDR3 |
| Short row reuse gaps | **ChargeCache** (reuse residual charge → shorter tRCD/tRAS) | DDR3 |
| Security / Rowhammer-adversarial | **PARA** probabilistic adjacent-row refresh | DDR3 |
| Tail-latency-sensitive under refresh | **refresh pausing** (interrupt tRFC at pause points) | DDR4 (model) |
| Same-bank subarray conflicts | **SALP** subarray-level parallelism | DDR4 (model) |
| Write-heavy, bank-parallel | write-refresh parallelization (`refpb_wrp`) | DDR4 |
| High-frequency throughput | bank-group scheduling (tCCD_L vs tCCD_S) | DDR4 |

The DDR2/LPDDR2 project already carries the commodity-legal spice (RBLA, `fewest_pending`,
`adapt_time`, `age_threshold`, XOR hashing) — see its design-requirements "Advanced modes".

## Removed modes → assignment

| Mode | Paper | Why not DDR2/LPDDR2 | Realizable in | Assigned |
|---|---|---|---|---|
| **`refpb_ooo`** — out-of-order per-bank refresh (controller names the bank; refresh idle/lowest-queue bank instead of the DRAM's round-robin) | Chang DARP #1 | commodity REFpb uses the DRAM's internal round-robin counter; no bank-ID field. Controller-directed per-bank refresh first appears in **LPDDR4 / DDR5** | LPDDR4 (commodity) | **`ddr4-lpddr4`** |
| **`refpb_wrp`** — write-refresh parallelization (REFpb the lowest-queue bank during a write-drain window) | Chang DARP #2 | same — needs controller-directed bank-ID (the write-drain *scheduling* half stays in DDR2 as commodity write-batching) | LPDDR4 (commodity) | **`ddr4-lpddr4`** |
| **`darp`** = `refpb_ooo` + `refpb_wrp` | Chang 2014/16 | as above | LPDDR4 (commodity) | **`ddr4-lpddr4`** |
| **Refresh pausing** — break a refresh bundle at Refresh Pause Points (`tRPC = tRFC/N`), resume via a checkpointed row counter | Nair 2014 | commodity REF is atomic (`tRFC`, non-interruptible); needs a modified DRAM refresh FSM + redefined RE semantics. **No JEDEC standard implements it** | research / **model-only** (faithful DRAM model) | **`ddr4-lpddr4`** (research) |
| **`sarp` / `dsarp`** — subarray-level access-refresh parallelism (access an idle subarray in a bank being refreshed) | Chang SARP/DSARP | needs DRAM array microarchitecture changes (+0.71% die, +13.8% tFAW/tRRD). **No commodity part** | research / **model-only** | **`ddr4-lpddr4`** (research) |

## Native advanced modes to add while there (not from the DDR2 papers, but DDR3/DDR4-commodity)

- **`ddr4-lpddr4`**: **Fine-Granularity Refresh** (FGR 1x/2x/4x, DDR4 MR3), **bank-group
  scheduling** (tCCD_L vs tCCD_S — same-group vs cross-group column pacing), commodity
  **per-bank refresh** (LPDDR4). These make several of the removed modes commodity here.
- **`ddr3-lpddr3`**: inherits the DDR2/LPDDR2 commodity baseline; **LPDDR3 per-bank
  refresh** (REFpb round-robin) is the only per-bank scheme commodity at this tier. The
  DDR2-paper model-only modes do not land here. **But DDR3 has its own research space** —
  `ddr3-lpddr3/TASKS.md` has a survey task for DDR3/LPDDR3-specific new/exotic mechanisms
  (retention-aware refresh / RAIDR, temperature-compensated refresh, ChargeCache,
  Rowhammer-aware targeted refresh / PARA, SALP, self-refresh/power-down + ZQ scheduling).

## Method (unchanged)

Each mode remains **config-bit-selectable** (`REFRESH_MODE` and friends), OFF-by-default
(reset = commodity baseline), added serially with a faithful-DRAM-model red→green test,
so one bitstream still characterizes every mode legal at that tier. Model-only modes live
in the `DFISlavePHY`/DRAM model and are gated by a PHY capability strap so firmware cannot
arm them against a device that does not support them.
