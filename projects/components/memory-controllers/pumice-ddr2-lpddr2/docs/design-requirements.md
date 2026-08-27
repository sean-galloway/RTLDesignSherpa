<!-- RTL Design Sherpa Documentation Header -->

<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

# pumice DDR2/LPDDR2 — Design Requirements

The rules every change to this controller must follow. Two lists: **Coding
Guidelines** (how the RTL is written) and **Implementation Guidelines** (the
structural/architectural invariants — bus-width relationships, config-vs-param,
gear/burst geometry). A change that violates any of these is a defect, not a
style preference. Many are enforced by elaboration asserts or by DV gates.

---

## Coding Guidelines

- **Minimize FSMs.** FSMs encode "what happens next" as state and are the source
  of edge conditions. Prefer **stateless / derived logic**: shift-register delay
  lines, windowed-OR enables, matured-count counters, combinational pickers with
  registered inputs/outputs. This project has repeatedly removed FSMs (DFI
  serializers, read aligner, bank timers, CAMs, split/aggregate) after each one
  produced a latent edge bug. If you reach for a state register, first ask
  whether the behavior can be *derived* from a delay line or a count.
- **Internal buses use valid/ready handshakes wherever practical.** As much as
  possible, module-to-module data/command interfaces are `valid`/`ready` (skid-
  buffered where needed) rather than assumed-ready strobes or fixed-latency
  pushes. This gives real backpressure (a downstream stall propagates instead of
  dropping data), makes FUBs composable and independently testable, and removes
  the "assumed the consumer was ready" race class. Size FIFOs so `ready` never
  deasserts in steady state — the handshake is the correctness net, not the
  throughput mechanism. Ad-hoc strobes are reserved for genuinely fixed-timing
  PHY/DFI signals (e.g. `dfi_rddata_en`), and even those are documented as such.
- **Reset:** always `aresetn` (active-low **async** reset). Use the reset macros
  `` `ALWAYS_FF_RST(clk, rst_n, ...)`` and `` `RST_ASSERTED(rst_n)`` from
  `reset_defs.svh` — never hand-roll `always_ff @(posedge clk or negedge rst_n)`.
  Never mix positive/negative reset. SRAM modules have **no** reset port.
- **Clocks:** `aclk` for the AXI/controller domain, `dfi_clk` for the PHY domain.
  Exactly **one** clock crossing (the DFI-layer async FIFOs); no other CDC.
- **Naming:** ports `i_*`/`o_*` (or the AXI/DFI standard names); registers `r_*`;
  wires `w_*`; parameters/localparams `UPPER_CASE`; derived params documented.
- **Array syntax** `logic [W-1:0] mem [DEPTH]` — never `[0:DEPTH-1]`.
- **FPGA attributes** on inferred memories (`ram_style`, `use_dsp`) guarded by
  `` `ifdef XILINX`` / `` `ifdef INTEL``.
- **No magic numbers / no hardcoded register offsets.** Config is reached
  **by name** through the generated register map (PeakRDL `*_regmap.py`), never
  a literal offset. RTL constants come from parameters or `localparam`.
- **Config registers, not compile-time parameters, for anything that can legally
  vary at runtime** (gear ratio, burst length, timings, phases). A wrong value
  must be *bad config programming* (a register write to fix), never a synthesis
  parameter-mismatch or a broken bitstream hybrid. See Implementation Guidelines.
- **Guard illegal parameter combinations with an elaboration assert**
  (`initial begin assert(...) else $fatal(1, "..."); end`). These fire at Vivado
  synthesis and sim time-0, turning a bad build into a **compile error** with a
  clear message. Do not weaken or delete a correctness assert to make a config
  "work" — make the datapath *satisfy* it.
- **Registered feedback is real latency.** A combinational picker fed by a
  registered state sees last cycle's value; always macro-test such logic (a FUB
  test with the registered feedback in place), never trust the combinational view.
- **Documentation is part of the change.** Update the module header, the HAS, the
  MAS, and `KNOWN_ISSUES/` in the same change. No emojis in specs (breaks the PDF
  pipeline). Regenerate PeakRDL RTL **and** docs **and** regmap in lockstep
  (`bin/peakrdl_generate.py`).
- **DV:** drive AXI via the AXI4 BFMs (`AXI4MasterWrite/Read` + sequences), never
  hand-poke `s_axi_*` — hand-poking misses protocol/timing bugs. Prefer one
  comprehensive test with incremental `TEST_LEVEL`s over many near-duplicates.
  A model/oracle must be **faithful** to the real device (see the DFISlavePHY
  a7ddrphy free-running model) — a lenient model that self-times masks the exact
  class of bug that fails on silicon.

---

## Implementation Guidelines

### Gear ratio (DFI rate)

- **`DFI_RATE` (the controller gear) must equal the PHY's `nphases`.** They are
  set in lockstep. Never infer, gearbox, or adapt one side to the other — that
  anti-pattern (a 1:2 controller NOP-ing half of a fixed-1:4 PHY's read phases)
  silently drops half the read data.
- On FPGA the PHY gear is **bitstream-fixed** (OSERDESE2/ISERDESE2 `DATA_WIDTH =
  2*nphases` is a static primitive attribute; the SERDES clock is sys2x vs
  sys4x). One bitstream = one fixed gear on both sides. Frequency flexibility
  comes from **MMCM dynamic reconfiguration**, not a runtime gear change.
- pumice's gear is a **runtime CSR** (`DFI_PHASE.gear_ratio` = `log2(active
  DFI_RATE)`), **built for max**: the datapath is synthesized for `MAX_DFI_RATE`
  and the register selects how many phases are *active*. At `gear == MAX` the
  behavior is bit-identical to a non-gated build. Set it equal to the attached
  PHY's fixed `nphases`.

### Burst length

- **Fixed BL per JEDEC (4 / 8 / 16), never inferred or dynamically negotiated.**
  It is a **config register** (`bl`, JEDEC value) that is the **single source of
  truth** — it drives both `MR0` and the controller framing.
- Build the datapath for the **max** legal burst geometry; the register selects
  the active BL. A DRAM burst may be a **fraction of a DFI word**: at gear 1:4
  with an x16 device, a BL4 burst = 64 b = half the 128 b DFI word, so
  `N = DFI_RATE / BL_PUMICE` bursts pack into one DFI word (like LiteDRAM). The
  burst framing (`CHUNK_BEATS`, intake `GEAR`/`BL`, read reassembly) is **derived
  from the runtime `gear`+`bl`**, not from a compile-time BL.

### Bus-width relationships (the only compile-time width params)

- **`HOST_AXI_DATA_WIDTH` and `DW` are the ONLY compile-time width parameters.**
  Everything else that *frames* data (active phases, burst length, timings) is a
  config register.
- **DFI word:** `DW = DFI_DATA_WIDTH = DRAM_BEAT_WIDTH × DFI_RATE`. The controller
  core is fixed **1:1** at the DFI word — one core AXI beat == one DFI word. The
  core never does data-width conversion.
- **`DRAM_BEAT_WIDTH`** = the DFI per-phase width = `2 × physical DQ width`.
- **Host width gearing:** a host AXI of a different width attaches only through
  `pumice_top_geared`, which inserts the formally-verified AXI dwidth converters.
  This is the **only** place a width changes.
- **HARD, COMPILE-ENFORCED RULE:** `HOST_AXI_DATA_WIDTH : DW` **must be an exact
  power-of-two ratio** — `AXI : DFI = G:1` or `1:G`, `G ∈ {1, 2, 4, 8, …}`.
  Enforced by an `initial assert … $fatal` in `pumice_top_geared` (fails Vivado
  synthesis / elaboration). Rationale — and this is exactly what LiteDRAM does
  (AXI frontend 1:1 with its native port; all width change through a power-of-two
  stride converter): the DFI word is the *atomic* memory-side transfer, so one
  AXI beat must be a **whole power-of-two number of DFI words**. Any other ratio
  yields partial words, fractional `CHUNK_BEATS`, and ragged bursts.
- **One AXI burst == one DRAM burst at the DW side** — the intake enforces the
  ragged-burst contract `(awlen+1) × GEAR == BL` (in the correct DRAM-beat
  units). Host-side burst sizing is the host's contract; the converter translates.

### Structure

- **Build-for-max, select-at-runtime.** Physical buses/FIFOs are sized for the
  maximum (widest gear × config range) — you cannot resize wires at runtime.
  Runtime registers select the *active* subset. This is the same pattern for
  gear phases and burst length. The modivation for this is to simplify characterization across many modes. With one bitstream program, one can run the full characterization suite.
- **Layering:** `pumice_axi4_ifc` (host AXI + CAMs) → `pumice_mem_cmd_scheduler`
  (bank timers + arbiter + refresh/init) → `pumice_dfi_layer` (single async CDC +
  DFI datapath). Internal data unit throughout is the **DFI word**.
- **Address/timing config by name** through the PeakRDL register block; the
  address map has one knob (`ADDR_MAP.bank_lsb`), not a scheme mux.

---

## DDR2 Timing Configuration

All DDR2 timing is **config registers** (PeakRDL `pumice_csr`, reached by name),
never compile-time constants. Complete list, grouped by register:

### JEDEC timing parameters (in MC/DRAM cycles)

| Register @ offset                 | Fields                                         |
| --------------------------------- | ---------------------------------------------- |
| `TIMINGS_RC_RCD_RP_RAS` @ 0x010   | `tRC`, `tRCD`, `tRP`, `tRAS`                   |
| `TIMINGS_RFC_REFI` @ 0x014        | `tRFC`, `tREFI`                                |
| `TIMINGS_RRD_FAW_WTR_CCD` @ 0x018 | `tRRD`, `tFAW`, `tWTR`, `tCCD`                 |
| `TIMINGS_CL_CWL_WR` @ 0x01C       | `CL`, `CWL`, `tWR`, `tRFCpb` (LPDDR2 per-bank) |
| `TIMINGS_RTP_RTW` @ 0x054         | `tRTP`, `tRTW`                                 |

### DFI / PHY timing + framing

| Register @ offset       | Fields                                                                      |
| ----------------------- | --------------------------------------------------------------------------- |
| `DFI_PHASE` @ 0x060     | `rd_phase`, `wr_phase`, `gear_ratio`, `bl`                                  |
| `PHY_TIMING` @ 0x064    | `t_phy_wrlat`, `t_rddata_en`, `memtype`, `refresh_burst`                    |
| (harness-side bring-up) | `dfi_cmd_delay`, `dfi_rddata_delay` — analog cmd↔DQ / read-capture leveling |

### Mode registers + init timing

| Register @ offset                     | Fields                                                          |
| ------------------------------------- | --------------------------------------------------------------- |
| `MR0`/`MR1`/`MR2`/`MR3` @ 0x020–0x02C | 16-bit DRAM mode-register values (encode CL, BL, WR, DLL, ODT…) |
| `INIT_TUNING` @ 0x050                 | `zq_retries`, `init_timeout_ms`                                 |
| `INIT_TIMING0` @ 0x058                | `t_init_wait` (tINIT/CKE settle), `t_dll_wait` (tDLLK)          |
| `INIT_TIMING1` @ 0x05C                | `t_mrd_wait` (tMRD), `t_rp_wait`, `t_rfc_wait` (tRFC)           |

### "Safe signals" — what may change at runtime, and what must not

The register bits fall into three hazard classes. Program the DRAM-locked and
structural bits **before** `CTRL.init_start`; treat the rest per class.

**A. Live-safe (change any time; effect is graceful).**
`tREFI` (as long as it stays ≤ the DRAM's retention/refresh requirement — a
larger value just refreshes less often, a smaller one more often), `refresh_burst`
(REFs drained per request — a pure scheduling knob). These only change *when* the
scheduler issues refreshes; they never violate a device parameter and never
touch an in-flight burst.

**B. Safe when quiesced (spacing counters — increase freely, decrease only when idle).**
`tRC`, `tRCD`, `tRP`, `tRAS`, `tRRD`, `tFAW`, `tWTR`, `tCCD`, `tRTP`, `tRTW`,
`tWR`, `tRFC`, and the PHY/leveling knobs `t_rddata_en`, `t_phy_wrlat`,
`rd_phase`, `wr_phase`, `dfi_cmd_delay`, `dfi_rddata_delay`. These are command-
spacing / capture-alignment counters. **Increasing** a spacing value is always
safe (the next command simply waits longer). **Decreasing** below the device's
requirement, or changing a capture-alignment knob **mid-transaction**, corrupts
data — so change them only while the controller is idle (no outstanding AXI
commands, between leveling passes). They need **no** re-init: they are counters,
not mode-register state. The leveling knobs are *meant* to be swept at bring-up
(this is how A7Leveling finds the read/write eye) — but always against idle
traffic.

**C. DRAM-locked / structural — require re-init (or an explicit MRS), never a live change.**
`CL`, `CWL` (the controller's latency must MATCH what `MR0`/`MR1` programmed into
the device — change one without re-issuing the MRS and the controller samples the
wrong cycle), `MR0`–`MR3` (a change is an MRS command to the device, i.e. part of
the init sequence), `bl` (JEDEC burst length — the single source of truth that
drives both `MR0` and the controller's burst framing; must be re-MRS'd and matches
the built datapath's max), `gear_ratio` (must equal the PHY's fixed `nphases`;
structural framing — a live change corrupts every in-flight beat), `memtype`
(DDR2 vs LPDDR2), and the `INIT_TIMING*` / `INIT_TUNING` waits (consumed only
during the init FSM — set them, then trigger init). The correct sequence for any
class-C change is: quiesce → update the register(s) **and** the matching `MR` →
`CTRL.init_start` (or `init_force_restart`).

**Rule of thumb:** anything that the DRAM itself latches (mode registers, and the
`CL`/`CWL`/`BL`/gear that must agree with them) is class C and needs re-init;
everything else is a controller-side counter that is safe to *raise* live and
safe to change freely only when idle.

---

## Scheduling & DRAM Management (FR-FCFS, paging, refresh)

The command-scheduling layer is `pumice_mem_cmd_scheduler` — one `aclk` layer that
wires a single pick core to the timing/bring-up blocks and emits one abstract DRAM
command `{op, rank, bank, row, col, ap}` per cycle into a FIFO for the DFI layer to
pack onto phases. It does **not** hold the transaction queue — pending requests
live in the two CAMs inside `pumice_axi4_ifc`; the scheduler reads them through
external lookup / `oldest` / commit / issue ports.

**Composition:** `pumice_cmd_arbiter` (the single pick core), `pumice_bank_timers`
(FSM-free per-bank JEDEC "safe" timers), `global_timers` (tFAW/tRRD/tWTR/tRTW/tCCD),
`refresh_ctrl`, `init_sequencer` (JEDEC MRS cold boot; gates traffic until done),
`mode_register` (CL/CWL/BL shadow), and an output command FIFO.

### Arbitration — FR-FCFS (First-Ready, First-Come-First-Served)

`pumice_cmd_arbiter` picks exactly **one** abstract command per cycle (PHY-agnostic,
single-issue). It never re-derives timing — per-bank readiness comes from
`pumice_bank_timers`, cross-bank/bus turnaround from `global_timers`. The priority
function is evaluated combinationally each cycle, descending:

1. **Init in progress** (`!init_done`) — forward the `init_sequencer` command
   verbatim; block all normal traffic.
2. **Refresh** (`refresh_req` or drain active) — precharge active banks one per
   cycle, then issue `REF` (see Refresh below).
3. **Column row-hit** — a `RD`/`WR` to an already-open row whose bank is column-
   ready (`bank_rdwr_ready`) and whose bus turnaround permits it (`tccd_ok` +
   `twtr_ok` for reads / `trtw_ok` for writes). This is the **First-Ready** term.
   **Reads have priority over writes**; within each, the **oldest** CAM entry (max
   relative age) wins the tie — the **First-Come-First-Served** term.
4. **Fallback** (no ready row-hit) — `ACT` the oldest pending op's row on an idle
   bank (subject to `tfaw_ok`/`trrd_ok` + the ACT/PRE guard), or `PRE` a bank open
   on the wrong row. Read CAM's `oldest` is consulted before the write CAM's.

So FR-FCFS here = **row-hit-ready commands first (reduce ACT/PRE overhead), oldest-
wins within a ready class, reads ahead of writes.** One issue per `aclk` cycle;
multi-phase/multi-cycle placement (incl. LPDDR2's 2-edge CA word) is downstream in
the DFI layer, so the arbiter always sees a single issue.

**ACT/PRE re-issue guard.** The bank timers register their readiness (two-cycle
event→`act_ready`/`pre_ready` latency), so a stateless arbiter would re-issue
ACT/PRE to the same bank before the timers catch up. The arbiter keeps a **two-cycle
per-bank guard** (`r_guard0`/`r_guard1`) blocking a bank for two cycles after an
accepted ACT/PRE. Column ops self-limit (both CAMs exclude a just-committed/issued
slot from the next lookup), so no column guard is needed. The shared-DQ-bus burst-
occupancy constraint (a BL burst owns the bus for `BL/DFI_RATE` DFI cycles) is
enforced **downstream in the DFI command path**, not here — the CDC decouples
`aclk` command issue from `dfi_clk` DQ timing.

### Paging (page policy / auto-precharge)

The column auto-precharge bit `ap` is set directly from `page_policy_i`
(`REFRESH_TUNING.page_policy_or` CSR, `page_policy_e`):

- **`OPEN`** (`ap=0`) — rows stay open; column ops stream to an open row at tCCD
  rate. Best for locality; the per-bank `bank_timer` holds the row open on RD/WR.
- **`CLOSE`** (`ap=1`) — every column op auto-precharges (issues `RDA`/`WRA`). Best
  for random access; no stale-row hazard.
- **`HAPPY_HYBRID`** — RETIRED (2026-08-25). It was never wired into the
  rearchitected core (treated as `OPEN`); `page_predictor.sv` and its CSR
  collateral (`happy_enable`, `PAGE_PRED_TUNING`, `OBS_PAGE_PRED_ACCURACY`)
  are deleted, and the `page_policy_or` encoding `11` maps to build default.
  Its Ghasempour-2015 successors are `adapt_time` (mode 4) and `adapt_access`
  (mode 5) of `PAGE_POLICY_CFG.policy_mode` in `pumice_page_policy` — both
  IMPLEMENTED 2026-08-25.

The "keep the row open" decision lives **inline** in the arbiter + per-bank
`bank_timer`, not in a separate predictor/lookahead — consistent with the
minimize-FSM rule (open-page state is genuine per-bank state in the timer, not a
control FSM).

### Refresh (`refresh_ctrl`)

Owns tREFI timing + refresh accounting; it does **not** issue commands — it raises a
request and the arbiter performs the precharge-then-REF sequence at refresh priority.

- **tREFI counter + pending accumulator:** `r_refi_cnt` counts down from `t_refi_i`,
  ticking only while `enable_i` (= `init_done`). On expiry it reloads and the pending
  accumulator increments, **saturating at the JEDEC max of 8 postponed refreshes**
  (a looming retention violation saturates rather than growing unbounded). Each
  accepted grant decrements it; `refresh_req_o` stays high while pending > 0.
- **Drain quota (batching):** `r_burst_remaining` loads `min(refresh_burst_i,
  pending)` and drains **back-to-back** (`refresh_drain_active` tells the arbiter to
  keep granting REF without yielding to RD/WR). `refresh_burst_i = 1` disables
  batching (one REF per tREFI).
- **REFab vs REFpb:** in REFpb mode (LPDDR2 per-bank) a bank rotor advances
  `0..NUM_BANKS-1` per grant (`refresh_bank_o`); default build wires REFab.
- **Arbiter sequence** (priority 2, second only to init): precharge every open bank
  on the target rank (one/cycle, lowest ready bank first, honoring the ACT/PRE
  guard) → once no row is open, issue `OP_REF` and pulse the grant → repeat while
  `refresh_drain_active`.

### Bank / global timing

`pumice_bank_timers` = FSM-free per-bank "safe" timers exposing
`bank_act_ready`/`bank_rdwr_ready`/`bank_pre_ready`/`bank_row_active`/`bank_open_row`
derived from tRCD/tRP/tRAS/tRC/tWR/tRTP (the derived-from-a-delay-line pattern, not
an FSM). `global_timers` covers the cross-bank/bus constraints: tFAW, tRRD (per
rank), tWTR, tRTW, tCCD. The arbiter consumes these as ready flags and never
recomputes timing.

---

## Advanced modes — selectable scheduling / paging / refresh (characterization)

The mechanisms below extend the baseline so that **one bitstream characterizes every
policy by flipping a CSR** (the "config not param" rule). Each is a paper-derived,
**config-bit-selectable MODE**; the reset/default is always the baseline above
(bit-identical), each mode is added **serially in pre-silicon** (faithful DRAM-model
red test → RTL → green) behind its own enable, and each carries read-only telemetry so
the host can sweep it and compare against the static baselines in-system.

**Commodity-legal only.** Every mode below runs on the real Nexys A7 DDR2 part (and
LPDDR2 where noted): all scheduling policies, all page policies, REFab / REFpb
round-robin, and the JEDEC ±8 postpone/pull-in refresh scheduling. Model-only schemes
that need DRAM-chip / JEDEC-command changes (out-of-order per-bank refresh, write-refresh
parallelization, refresh pausing, subarray parallelism) are **out of scope for this
DDR2/LPDDR2 project** and are tracked for the DDR3/DDR4 roadmap in
[`../../ADVANCED_MODES_ROADMAP.md`](../../ADVANCED_MODES_ROADMAP.md).

### Mode-select CSRs (the characterization surface)

- **`SCHED_POLICY`** — `ORDER_MODE` (in_order / fr_fcfs / age_threshold), `PRIO_SUB`
  (none / load_over_store / age_boost), `ROW_SEL`, `COL_SEL`, `ACCESS_PREF`,
  `AGE_THRESH`, `AUTO_PRECHARGE_EN`, write-drain `WR_HIGH_WM`/`WR_LOW_WM`, `QOS_EN`.
- **`PAGE_POLICY_CFG`** — `POLICY_MODE` (static_open / static_close / fixed_open /
  adapt_time / adapt_access / rbl_static / rbl_dyn), `POLICY_SCOPE`, plus `TIMEOUT_CFG`
  (`TR_INIT/MIN/MAX/STEP`), `ADAPT_CFG` (`MC_HIGH/LOW_THR`, `MC_INIT`, `CHECK_INTERVAL`),
  `HYBRID_CFG` (`CTR_WIDTH`, `CTR_OPEN_MAX`, `CTR_INIT`), `RBL_CFG` (`MISS_THRESH`,
  `RESET_INTERVAL`, `WAYS`/`SETS`, dyn hill-climb weights).
- **`REFRESH_MODE` / `REF_CTRL`** — `MODE` (refab / refpb_rr), `POSTPONE_LIMIT` /
  `PULLIN_LIMIT` (0..8), `TREFI` / `TREFI_PB` / `TRFC_AB` / `TRFC_PB`, capability strap
  `PERBANK_SUPPORTED`.
- **`SCHED_STATS` / `PAGE_STATS` / `REF_STATS`** — read-only: page hit/miss/empty counts,
  per-bank `TR`, ACT/PRE/REF counts, refresh-defer histogram (for in-system sweeps).

### Axis 1 — Arbitration / scheduling (Rixner, ISCA 2000)

Model each scheduler unit (precharge / row / column / address arbiters) as an independent
field so any policy combination is reachable. All commodity-legal.

- **`in_order` (IMPLEMENTED 2026-08-26, `SCHED_POLICY.order_mode=1`)** — issue only what
  the single oldest not-issued reference requires; no lookahead. As built: an arbiter
  overlay NARROWS the FR-FCFS class masks to the head-of-CAM entry (from the age-order
  matrix); between CAMs the older head wins by relative-age compare (both CAM age
  counters free-run from reset, same epoch; tie -> read).
- **`fr_fcfs` (First-Ready, First-Come-First-Served)** — among *ready* references (DRAM
  timing + resources free), pick **row-hit-ready** first, oldest as tie-break. The current
  default (modes 0/2); a ready-check + age compare (cheap, ~+25% BW in the paper).
- **`age_threshold` (IMPLEMENTED 2026-08-26, `order_mode=3` + `age_thresh`)** — references
  older than `AGE_THRESH` (MC cycles/16; the CAMs export a per-entry 1-bit aged flag, so
  numeric ages never leave the CAM) get a priority boost: while ANY aged entry exists,
  every class narrows to aged entries — an aged reference's PRE outranks fresh row-hits,
  bounding starvation. The boost triggers on the aged entry's EXISTENCE, not its momentary
  candidacy (a guard-blocked PRE must still engage the narrowing, or the competing column
  stream re-arms the guard forever).
- **`ROW_SEL` / `COL_SEL` = `most_pending` / `fewest_pending` (IMPLEMENTED 2026-08-26,
  `SCHED_POLICY.row_sel/col_sel`)** — activate/serve the row with the most (drain the
  hottest row) or fewest (let low-demand rows precharge sooner) pending references.
  As built: the paper's "expensive population counters" degenerate at CAM depth 8 to an
  8x8 same-{bank,row} match triangle per CAM; the pick is population-first with OLDEST
  tie-break, composing under the ORDER_MODE mask narrowing. row_sel steers ACTIVATE,
  col_sel steers COLUMN; precharge picks stay strictly oldest.
- **`ACCESS_PREF` = `column_first` / `row_first` / `precharge_first`** — address-arbiter
  class preference (latency-to-open-row vs bank parallelism). Static arbiter priority.
- **`load_over_store` (`PRIO_SUB`)** — reads outrank writes (already the baseline); a
  1-bit priority key protecting latency-critical reads.
- **Write batching (exotic)** — drain writes back-to-back once the write buffer crosses
  `WR_HIGH_WM`, stopping at `WR_LOW_WM`, to amortize tWTR/bus turnaround instead of
  ping-ponging RD/WR. Watermark comparators.
- **QoS-aware (exotic)** — factor `AxQOS` into the pick (highest-QoS ready first, age
  tie-break) when `QOS_EN`.
- **Presets** (apples-to-apples): `in_order`, `first_ready`, `{col,row}_{open,close}`,
  `load_row_open`. Recommended default = `row_closed` + auto-precharge fusion +
  load-over-store.

### Axis 2 — Page policy / auto-precharge (Rixner open/closed + Happy 2015 + RBLA/Yoon 2012)

The decision resolves to (a) the column command's auto-precharge bit and (b) a background
per-bank precharge *request* that still respects tRAS/tRTP/tRP/tRC. All commodity-legal.

- **`static_open`** — never auto-precharge; the `bank_timer` holds the row. Best on high
  locality (~68% of workloads, up to +18% vs close). Reset default.
- **`static_close`** — always auto-precharge (`RDA`/`WRA`); enables precharge fusion on
  the last column op to a row. Best on random/low-locality (up to +18% vs open).
- **`fixed_open`** (IMPLEMENTED 2026-08-25, `pumice_page_policy`) — leave the row open, close after an **idle timeout** of
  `TR_INIT` clocks (paper used ≈ tRC). One per-bank timeout counter.
- **`adapt_time` (Happy adaptive-timeout, recommended adaptive; IMPLEMENTED 2026-08-25, `pumice_page_policy`)** — per **bank**: Timeout
  Counter `TC`, Timeout Register `TR`, 4-bit Mistake Counter `MC`. Close the row when
  `TC==TR`. `MC`↑ on a premature-close mistake (page-empty reopening the just-closed row),
  `MC`↓ on held-too-long (a conflict that could have been an empty); every
  `CHECK_INTERVAL`, `MC>HIGH ⇒ TR+=STEP`, `MC<LOW ⇒ TR-=STEP` (clamped `TR_MIN..TR_MAX`).
  Best measured policy; ~16–32 small registers total + a last-closed-row latch/comparator
  per bank.
- **`adapt_access` (Happy "Hybrid"; IMPLEMENTED 2026-08-25, `pumice_row_pred_table`)** —
  per **row** 2-bit saturating counter; decision = counter vs `ctr_open_max` (default 2)
  at ACT time. As built: tagless direct-mapped, {bank, XOR-folded row} index (folding
  replaces the paper's full per-row BRAM — aliasing blends history, acceptable for a
  predictor), learning from accesses-per-activation at explicit PRE closes plus a
  premature-reopen decrement for auto-precharge closes.
- **`rbl_static` / `rbl_dyn` (RBLA / Yoon; IMPLEMENTED 2026-08-25, `pumice_rbl_table`)** —
  count row-buffer **misses only, not accesses** (a hit carries no signal). A small
  set-associative table of saturating **miss** counters (tag = row addr, true-LRU,
  `PAGE_RBL_CFG` shapes ways/sets/threshold/epoch); miss-count `> MISS_THRESH` ⇒
  low-locality row → auto-precharge. `rbl_dyn` hill-climbs `MISS_THRESH` per epoch on the
  measured page-hit fraction (divider-free cross-multiplication, direction memory).
  Separates hot-but-friendly from hot-and-thrashing rows that frequency-based schemes
  conflate. (Only the miss-predictor is kept; the paper's DRAM-cache migration machinery
  is dropped.)

### Axis 3 — Refresh (Chang DARP/DSARP 2014–16 + Nair pausing 2014 + JEDEC)

The JEDEC **±8 postpone/pull-in credit** (`ref_credit`, signed 4-bit/bank) is the hard
data-integrity budget every mode obeys.

- **`refab` (DDR2 baseline, commodity)** — one command refreshes the whole rank
  (`tRFCab`), interval `tREFI`. Current default. Postpone up to 8 + drain batching
  (`refresh_burst`) already implemented.
- **`refpb_rr` (LPDDR2, commodity; IMPLEMENTED 2026-08-26, `REF_CTRL.mode=2`)** —
  per-bank refresh via the DRAM's internal **round-robin** counter (JESD209-2 6.6:
  the command carries NO bank address; the controller keeps a rotor MIRROR that
  advances exactly when an OP_REFPB is granted onto the wire). As built: the
  arbiter's REFpb branch precharges only the rotor bank then issues REFPB;
  `tREFIpb` from `REF_TIMING_PB.trefi_pb` (0 = derive tREFI/8), recovery
  `trfc_pb` (< tRFCab). Conservative v1 interlock: the rank-wide ACT block during
  the (shorter) tRFCpb also spaces consecutive REFpb commands; columns to
  already-open rows in other banks flow throughout — the full ACT-during-tRFCpb
  overlap is a later optimization. LPDDR2-only: the scheduler degrades mode 2 to
  REFab on DDR2, and the `REF_CTRL.perbank_supported` strap advertises capability.
- **Refresh pull-in / postpone scheduling (commodity; IMPLEMENTED 2026-08-25,
  `refresh_ctrl` v3)** — as built the credit is rank-scoped (REFab), split into the
  pending backlog (postponed refreshes, 0..8) and a pull-in credit (refreshes run
  ahead, 0..8): under demand the request is withheld until the backlog exceeds
  `REF_CTRL.postpone_limit` (clamped 7 so the JEDEC ceiling always forces);
  on CONFIRMED idle (16-cycle hysteresis over CAM occupancy — micro-gaps between
  bursts must not release postponed refreshes) refreshes run ahead up to
  `pullin_limit`, and each later tREFI tick consumes a credit instead of adding
  backlog. 0/0 = strict baseline, bit-identical. Per-bank `ref_credit[b]` steering
  arrives with REFpb.
- **Fallback caution:** on traffic that can't use other banks during a per-bank refresh
  window, REFpb's serialized commands can total ≈3.5× tRFCab — keep `refab` as the safe
  selectable fallback.

### Serial pre-silicon implementation order

Foundation first (the mode-select CSRs + faithful DRAM-model hooks), then one mechanism
at a time, each with its own red→green model test and OFF-by-default:
1. `SCHED_POLICY` / `PAGE_POLICY_CFG` / `REFRESH_MODE` CSRs + `*_STATS` telemetry + PHY
   capability straps (no behavior change; defaults bit-identical).
2. Scheduling: `in_order` → `fr_fcfs` (confirm current) → `age_threshold` → `most/fewest
   pending` → `ACCESS_PREF` → write-batching → QoS.
3. Paging: `static_open/close` (confirm) → `fixed_open` → `adapt_time` → `rbl_static` →
   `rbl_dyn` → `adapt_access`.
4. Refresh (commodity): pull-in/postpone sweep → `refpb_rr`.

---

## Enforcement summary

| Requirement                             | Enforced by                                                   |
| --------------------------------------- | ------------------------------------------------------------- |
| `HOST_AXI_DATA_WIDTH : DW` power-of-two | `initial assert $fatal` in `pumice_top_geared` (synth/elab)   |
| One AXI burst == one DRAM burst at DW   | `pumice_wr_intake` ragged-burst assert                        |
| `CHUNK_BEATS` power-of-two              | `pumice_axi_burst_chopper` assert                             |
| `DFI_RATE == nphases` (gear lockstep)   | design rule + `gear_ratio` CSR set to PHY nphases             |
| gear=MAX bit-identical                  | macro regression (109) + `test_a7ddrphy_gear_mismatch`        |
| No hardcoded offsets                    | config reached by name via generated `*_regmap.py`            |
| Config not param (gear, BL, timings)    | runtime CSRs; a wrong value is bad programming, not a rebuild |
