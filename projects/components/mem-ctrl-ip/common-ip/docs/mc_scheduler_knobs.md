# mc_scheduler_core — knob inventory (Task 5 step 1)

Measured 2026-10-10. Goal: categorize every divergence among the three rock
schedulers so the merge step can decide what becomes a common `mc_scheduler_core`
knob vs. what stays rock-side.

Files compared:

- `projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/macro/pumice_scheduler_layer.sv`
- `projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/rtl/macro/scoria_scheduler_layer.sv`
- `projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/macro/andesite_scheduler_layer.sv`
- `projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/pumice_cmd_arbiter.sv`
- `projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_cmd_arbiter.sv`
- `projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_cmd_arbiter.sv`
- `projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_global_timers.sv`
- `projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_bank_timers.sv`

## 1. Size / divergence metrics

| file set | pumice lines | scoria lines | andesite lines | p↔s diff -w | s↔a diff -w | p↔a diff -w |
|---|---|---|---|---|---|---|
| scheduler layer (`*_scheduler_layer.sv`) | 662 | 692 | 882 | 176 | 556 | 592 |
| command arbiter (`*_cmd_arbiter.sv`) | 1684 | 1755 | 1809 | 609 | 176 | 705 |

The scheduler-layer deltas are dominated by port-list and child-instance
wiring changes. The arbiter deltas are dominated by (a) the unified prospect-pool
refactor that only pumice has received, and (b) generation-specific maintenance
requesters (ZQ calibration, training MRS/MPC) and DDR4 bank-group L/S admission.

## 2. A–E classification key

| class | meaning | resolution model |
|---|---|---|
| **A** | Mechanical / rock naming: module/package names, comments that only swap the rock prefix, documentation paths, local instance names. | Rename to `mc_*`; any rock-specific text moves to the rock wrapper or is removed. |
| **B** | Parameter / width knobs: values or widths that can be expressed as module `parameter`s or `generate` conditions. | Common core exposes a parameter; rocks pass their design point. |
| **C** | Port union / presence: inputs/outputs that exist in some rocks but not others. | Common core carries the union; unused inputs are tied off, unused outputs are left dangling or observed. |
| **D** | Behavioral / protocol differences: control structures that are not merely numeric parameters — maintenance requester type, init-sequencer protocol, output packing, fire-stage policy, pool structure. | Common core uses `generate`/`localparam` branches, or the behavior stays rock-side in a thin wrapper. |
| **E** | Silicon bug-history / design-rationale comments: `BUG-*`, `ISSUE-*`, measured regression numbers, timing arguments. | Carry verbatim into the common core; do not let cosmetic edits erase them. |

## 3. Scheduler-layer divergences

### 3.1 pumice ↔ scoria

| bucket | evidence (`file:line`) | what diverges | resolution hint |
|---|---|---|---|
| A | `pumice_scheduler_layer.sv:7` / `scoria_scheduler_layer.sv:7`; `p:23-24` / `s:23-24`; `p:16,18,54,141,169,220,225,260,282,286,422,424,432,467,640,662` / `s:16,18,55,141,169,237,242,282,304,312,320,456,458,466,501,670,692` | Module name, package import, rock-prefixed comments, doc paths, CAM-source comments. | Rename to `mc_scheduler_layer`; strip rock prefixes. |
| B | `scoria_scheduler_layer.sv:55-59` (added); `pumice_scheduler_layer.sv:54` (absent) | `NUM_CS` / `CSW` parameters for DDR3 chip-select tracking. | Add `NUM_CS`/`CSW` parameters; pumice ties `NUM_CS = NUM_RANKS`. |
| C | `scoria_scheduler_layer.sv:90` | `stall_zq_o` output added for ZQCS telemetry. | Add output; pumice drives 0 or observes unused. |
| C | `scoria_scheduler_layer.sv:130-151` | DDR3 init timing (`t_xpr_wait_i`, `t_zqinit_wait_i`, `dram_reset_n_o`, `mr_wr_o`, `wrlvl_en_o`) + ZQ calibration request/grant/t_zqcs + Mode A/B/C refresh CSR fields. | Union port set; pumice ties off DDR3/ZQ/Mode-ABC inputs. |
| C | `pumice_scheduler_layer.sv:175-184` | Pumice training command channel (`trn_cmd_req_i`, `trn_cmd_grant_o`, `trn_cmd_op_i`, `trn_cmd_bank_i`, `trn_cmd_row_i`, `trn_cmd_mrr_i`, `cal_busy_i`) + `cmd_mrr_o` removed in scoria. | Union ports; scoria/andesite tie off the pumice-style training ports if unused. |
| D | `pumice_scheduler_layer.sv:294` / `scoria_scheduler_layer.sv:322` | `w_refpb_en` compares `MEMTYPE_LPDDR2` vs `MEMTYPE_LPDDR3`. | Use family memtype enum; generate on `MEMTYPE_LPDDR2 \|\| MEMTYPE_LPDDR3` or per-rock parameter. |
| D | `scoria_scheduler_layer.sv:336-341`, `s:356-358` | Mode A/B/C refresh CSRs wired into `scoria_refresh_ctrl` and new observability outputs `obs_ref_postpone_events_o` / `obs_ref_pullin_events_o`. | Add `HAS_REFRESH_POLICY` generate branch or parameter bundle; pumice ties off. |
| D | `pumice_scheduler_layer.sv:576-578,625-626` / `scoria_scheduler_layer.sv:599-600,655` | Output command FIFO width and packing: pumice carries `{cmd_mrr, cmd_ap, ...}`; scoria drops `cmd_mrr`. | Output descriptor includes an `extra` bit with rock-defined meaning (pumice=MRR, scoria/andesite=unused or ZQ marker). |

### 3.2 scoria ↔ andesite

| bucket | evidence (`file:line`) | what diverges | resolution hint |
|---|---|---|---|
| A | `scoria_scheduler_layer.sv:7-18` / `andesite_scheduler_layer.sv:7-21`; `s:23-24` / `a:26-27`; `s:141,218,260,282,286,312,320,456,458,466,501,670,692` / `a:141,218,391,401,428,438,634,636,644,679,857,882` | Module/package names, header provenance, doc paths, child-instance names, CAM-source comments. | Common rename; rock headers move to wrappers. |
| B | `andesite_scheduler_layer.sv:44-47`, `a:431-434`, `a:249` | `NUM_BG`, `BGW_EFF_M`, and `cmd_bg_o` width added for DDR4 bank groups. | Parameter `NUM_BG` (default 1) + derived `BGW_EFF`; `cmd_bg_o` width derived from `NUM_BG`. |
| C | `andesite_scheduler_layer.sv:119-123` | L/S pair CSR inputs: `t_ccd_l_i`, `t_ccd_s_i`, `t_rrd_l_i`, `t_rrd_s_i`. | Union inputs; pumice/scoria tie to 0; common `mc_global_timers` already supports them. |
| C | `andesite_scheduler_layer.sv:129-135` | FGR inputs: `fgr_factor_i`, `t_rfc_2x_i`, `t_rfc_4x_i`; `t_rfc_i` becomes the 1x density value. | Add FGR port bundle; pumice/scoria tie `fgr_factor_i = 0` and `t_rfc_2x/4x = t_rfc_i`. |
| C | `andesite_scheduler_layer.sv:142-185` | P1 init sequencer pin set: `t_cke_wait_i`, `t_mod_wait_i`, `dram_reset_n_o`, `cke_o`, `wrlvl_en_o`; removes `t_xpr_wait_i` and DFI init handshake. | Init sequencer stays rock-specific; common core exposes a generic init-command stream. |
| C | `andesite_scheduler_layer.sv:186-?` (zq block), `a:95-104` | Andesite internal ZQ config + `zq_enable_i`, `zq_interval_i`, overdue/placement CSRs, LPDDR4 MPC `t_zq_i`/`zq_mpc_opcode_i`. | ZQ controller can be internal child or wrapper port; common core sees only `zq_req_i`/`zq_grant_o`/`t_zqcs_i`. |
| C | `andesite_scheduler_layer.sv:154-161` | Andesite maintenance-class training channel (`trn_cmd_req_i`, `trn_cmd_ack_o`, `trn_cmd_op_i`, `trn_cmd_bank_i[2:0]`, `trn_cmd_addr_i[17:0]`, `trn_cmd_mpc_i`). | Union training port; scoria ties off, pumice maps its narrower `trn_cmd_row/mrr` to the wide `addr` field. |
| C | `andesite_scheduler_layer.sv:195-216` | Andesite replaces scoria CL/CWL/BL shadow outputs with DDR4 policy outputs (`rtt_nom_o`, `rtt_wr_o`, `rtt_park_o`, `rd_dbi_en_o`, `wr_dbi_en_o`, `mpr_page_o`, `fgr_factor_o`, `ca_parity_lat_o`, `lpddr4_odt_o`, `wrlvl_en_o`, `init_err_o`, `zq_cal_start_o`, ...). | Mode-register shadow is rock-specific; common scheduler passes through MR data or keeps a generic policy vector. |
| D | `andesite_scheduler_layer.sv:485-528` | Andesite instantiates `andesite_zq_ctrl` inside the scheduler; scoria receives ZQ from the training layer. | Decide whether ZQ is a child of the scheduler or an external maintenance client. Both feed the same arbiter `zq_req_i`/`grant_o` contract. |
| D | `andesite_scheduler_layer.sv:577-625` | `mc_global_timers` instantiated with `HAS_LS_PAIRS=1`, group wires (`w_evt_bg`, `w_pick_group`) and L/S readiness loop. | Reuse common `mc_global_timers` with `HAS_LS_PAIRS` and `NUM_BG` parameters (already extracted in Task 2). |
| D | `andesite_scheduler_layer.sv:452-464`, `a:679`, `a:729-731` | `andesite_refresh_ctrl` FGR selection drives `w_refresh_trfc`; `andesite_cmd_arbiter` gets `NUM_BG`, `tccd_l_ok_i`, `trrd_l_ok_i`, `pick_group_o`. | Add `HAS_FGR` and `NUM_BG` parameters; refresh child rock-selectable. |
| D | `andesite_scheduler_layer.sv:341-387` | Andesite P1 init sequencer interface is incompatible with scoria DDR3 init sequencer. | Keep init sequencer rock-specific; common core consumes generic init-cmd valid/op/bank/row. |
| D | `andesite_scheduler_layer.sv:793-795`, `a:875-878` | Output FIFO packing and history checker add `cmd_bg_o`. | Descriptor includes optional `bg` field; width derived from `NUM_BG`. |

### 3.3 pumice ↔ andesite

This is essentially the union of the two tables above: pumice lacks DDR3 ZQ,
DDR4 bank-group L/S windows, FGR, and the P1 init-sequencer interface; andesite
adds all of them and also restores a maintenance-class training channel (now
MRS/MPC shaped) that pumice already has but scoria does not.

## 4. Command-arbiter divergences

### 4.1 pumice ↔ scoria

| bucket | evidence (`file:line`) | what diverges | resolution hint |
|---|---|---|---|
| A | `pumice_cmd_arbiter.sv:7-8` / `scoria_cmd_arbiter.sv:7-8`; `p:26-27` / `s:29-30`; rock-prefixed comments throughout | Module/package names, comments, doc paths, child references (`pumice_page_policy`/`scoria_page_policy`). | Rename to `mc_cmd_arbiter`; scrub rock prefixes. |
| C | `scoria_cmd_arbiter.sv:119-131`, `s:230` | ZQ calibration ports `zq_req_i`, `zq_grant_o`, `t_zqcs_i`; `t_rfc_pb_i` repositioned; `stall_zq_o` output. | Union ports; pumice ties off ZQ. |
| C | `pumice_cmd_arbiter.sv:140-147`, `p:212` | Pumice training ports `trn_cmd_*` and `cal_busy_i`; `cmd_mrr_o` output. Removed in scoria. | Union training/MRR ports; scoria ties off. |
| D | `pumice_cmd_arbiter.sv:704-735,753-793,928-954` / `scoria_cmd_arbiter.sv:733,739-822,967-975` | Pumice uses the unified 2N-entry prospect pool (`POOL`, `pool_*`, `f_pool_*`); scoria still uses split rd/wr classify and population loops. | Adopt the unified pool in the common core (Task 4.5 proved it bit-identical). |
| D | `pumice_cmd_arbiter.sv:332-359` / `scoria_cmd_arbiter.sv:328-369,372-396` | Pumice fire stage holds an ACT whose only obstacle is the rank-global tFAW/tRRD window (`w_out_hold`); scoria drops the hold and instead re-checks `tfaw_ok_i`/`trrd_ok_i` at the fire stage plus adds a `w_zq_busy` block. | Common core must preserve the fire-stage authority; choose hold-vs-drop via parameter or adopt the scoria/drop model with the same next-cycle readiness. |
| D | `pumice_cmd_arbiter.sv:1478-1482` / `scoria_cmd_arbiter.sv:1497-1548,1786-1809` | Pumice priority chain has a training pass-through branch; scoria replaces it with a ZQCS branch + `r_zqcs_cnt` window. | Add `MAINT_REQ` enum or slot vector; each rock maps its maintenance source(s) to the generic interface. |
| D | `scoria_cmd_arbiter.sv:1331-1345`, `s:1442-1455`, `s:1499-1504` | Scoria adds `stall_zq_o` accounting, `w_zq_safe`, and priority-2 tZQCS idle block. | Generate on `HAS_ZQ`. |

### 4.2 scoria ↔ andesite

| bucket | evidence (`file:line`) | what diverges | resolution hint |
|---|---|---|---|
| A | `scoria_cmd_arbiter.sv:7-38` / `andesite_cmd_arbiter.sv:7-21`; `s:29-30` / `a:23-24`; ANDESITE L/S DELTA comments | Module/package/header, doc paths, provenance comments. | Common rename; preserve delta comments in andesite wrapper or as design notes. |
| B | `andesite_cmd_arbiter.sv:29` | `NUM_BG` parameter. | Common `NUM_BG` parameter (default 1). |
| C | `andesite_cmd_arbiter.sv:134-140` | Andesite training command ports (`trn_cmd_req_i`, `trn_cmd_op_i`, `trn_cmd_bank_i[2:0]`, `trn_cmd_addr_i[17:0]`, `trn_cmd_grant_o`). | Union maintenance ports; scoria ties off, pumice maps existing training signals. |
| C | `andesite_cmd_arbiter.sv:158-170` | L/S readiness inputs `tccd_l_ok_i`, `trrd_l_ok_i`, `pick_group_o`. | Union ports; pumice/scoria tie to 1 when `NUM_BG==1`. |
| D | `andesite_cmd_arbiter.sv:382-384,387,390,775,809,1147` | Bank-group L/S gating added to fire stage, column masks, and `w_act_gate_live`. | Generate on `NUM_BG > 1`; reuse `mc_global_timers` L/S outputs. |
| D | `andesite_cmd_arbiter.sv:1550-1566`, `a:1479`, `a:1644`, `a:1657`, `a:1716` | Andesite adds `r_trn_grant`, training MRS/MPC branch in priority chain, and bottom bank-group admission logic (`w_pick_group`, `r_last_col_bg`, `r_last_act_bg`, `w_tccd_ls_ok`, `w_trrd_ls_ok`). | Generic maintenance slot + `NUM_BG` generate. |
| D | `andesite_cmd_arbiter.sv:1439,1450,1465` | `w_ref_safe`/`w_zq_safe` include `!r_trn_grant` term. | Extend maintenance-grant exclusion vector. |

### 4.3 pumice ↔ andesite

This is the union of 4.1 and 4.2: pumice has the unified pool and the
pumice-shaped training channel; andesite keeps the scoria split loops, adds ZQ
support, adds bank-group L/S admission, and reshapes training to MRS/MPC via
`trn_cmd_addr_i`.

## 5. Common timing FUBs — no new divergence

| FUB | status |
|---|---|
| `mc_global_timers.sv` | Already parameterized for DDR4 L/S pairs and bank-group windows (`NUM_BG`, `BGW`, `HAS_LS_PAIRS`). Pumice/scoria pass `HAS_LS_PAIRS=0` and tie off L/S inputs; andesite passes `HAS_LS_PAIRS=1`. See `mc_global_timers.sv:37-44,293-346`. |
| `mc_bank_timers.sv` | Already parameterized (`NUM_RANKS`, `NUM_BANKS`, `ROW_WIDTH`, `BANK_LA`). All three rocks instantiate with their design-point values; no source change required. |

## 6. Merge recommendations (answers to the four required questions)

### 6.1 Can pumice + scoria share a single `mc_scheduler_core` with only knobs?

**Yes, with two architectural knobs and one structural adoption.**

1. **Maintenance requester type.** Pumice exposes a training channel
   (`trn_cmd_*` + `cal_busy_i`); scoria exposes ZQ calibration (`zq_req_i`,
   `zq_grant_o`, `t_zqcs_i`). The common core should treat these as a generic
   maintenance-class slot with `req`/`grant`/`op`/`bank`/`row`/`extra`. Each rock
   maps its real source into that slot; unused inputs are tied off.
2. **Unified prospect pool.** Pumice has the pool refactor (Task 4.5); scoria
   still uses split rd/wr loops. The common core should adopt the unified pool —
   it is bit-identical and reduces duplicated code.
3. **DDR3 ZQ / Mode A/B/C / `NUM_CS`.** These are pure parameter / port-union
   additions. Pumice ties them off; scoria uses them.

The pumice-vs-scoria scheduler-layer port differences are therefore almost
entirely **C-class** union ports plus a few **B-class** parameters. The only
**D-class** work is the generic maintenance slot and the pool adoption.

### 6.2 Should andesite adopt the common core, or be wrapped?

**Adopt the common core, but with a thicker rock wrapper than pumice/scoria.**

Andesite's deltas are all parameterizable, but several are structural enough
that they should not be `generate`-spaghetti inside the core:

- **Bank-group L/S windows** — already supported by common `mc_global_timers`;
  the arbiter only needs `NUM_BG` and the L/S ports. This is a clean **B-class**
  parameterization.
- **FGR** — add `HAS_FGR` + the `fgr_factor_i`/`t_rfc_2x_i`/`t_rfc_4x_i` bundle;
  refresh child selects the recovery window. Mostly **B/C-class**.
- **P1 init sequencer** — the interface is fundamentally different from the
  pumice/scoria init sequencer. Keep `mc_init_sequencer` rock-specific (or a
  family of init children) and feed the common core a generic init-cmd stream.
- **ZQ controller placement** — scoria receives ZQ from the training layer;
  andesite embeds `andesite_zq_ctrl`. Either make ZQ a child of the common core
  behind `HAS_INTERNAL_ZQ`, or require every rock to source ZQ externally. The
  external contract is the same, so external sourcing is the simpler wrapper
  boundary.
- **Mode-register shadow outputs** — andesite's policy outputs (`rtt_*`, DBI,
  MPR, parity latency, etc.) differ from pumice/scoria's CL/CWL/BL. Keep the
  mode-register child rock-specific and pass a generic policy vector if the
  scheduler core needs it.

Conclusion: andesite should instantiate `mc_scheduler_core` with `NUM_BG=4`,
`HAS_LS_PAIRS=1`, `HAS_FGR=1`, and a rock-side wrapper that supplies the P1 init
sequencer, the internal ZQ controller, and the DDR4 mode-register shadow.

### 6.3 Upstream port width / presence differences

The upstream boundary of `mc_scheduler_core` (the layer that instantiates the
arbiter and timers) should be the union of the three rock port lists. The
significant differences are:

| signal group | pumice | scoria | andesite | common-core treatment |
|---|---|---|---|---|
| init sequencer | DDR2/LPDDR2 timing + MRS MR0..3, DFI init handshake | DDR3 timing + `t_xpr_wait`/`t_zqinit_wait`/`dram_reset_n`/`mr_wr`/`wrlvl_en` | P1 DDR4 timing + `cke_o`, MR0..6, no DFI handshake, `init_err`, policy outputs | Rock-specific init child; core sees generic init-cmd stream. |
| refresh control | basic postpone | Mode A/B/C CSR fields + ZQCS passthrough | Mode A/B/C + ZQ cfg + FGR + LPDDR4 MPC | Union CSR bundle + `HAS_FGR`/`HAS_ZQ`. |
| ZQ calibration | none (via training) | external `zq_req_i`/`zq_grant_o`/`t_zqcs_i` | external + internal `andesite_zq_ctrl` | Core keeps `zq_req_i`/`zq_grant_o`/`t_zqcs_i`; source is rock-side. |
| training / maintenance | `trn_cmd_*` + `cal_busy_i` + `cmd_mrr_o` | none | `trn_cmd_*` with `addr[17:0]`/`mpc[5:0]` | Generic maintenance slot with wide `addr`/`extra` fields. |
| bank group | none | none | `NUM_BG`, `t_ccd_l/s`, `t_rrd_l/s`, `cmd_bg_o` | `NUM_BG` parameter + derived `cmd_bg_o` width. |
| mode-register shadow | CL/CWL/BL | CL/CWL/BL + `mr_wr`/`wrlvl_en` | policy outputs (RTT/DBI/MPR/...) | Rock-specific child; core does not consume these. |
| output descriptor | `{mrr,ap,col,row,bank,rank,op}` | `{ap,col,row,bank,rank,op}` | `{ap,col,row,bg,bank,rank,op}` | Descriptor includes optional `mrr/extra` + optional `bg`. |

The common timing FUBs (`mc_global_timers`, `mc_bank_timers`) already expose the
necessary parameter surface; no port divergence is required there.

### 6.4 Risk notes — silicon-bug-history comments that must be preserved

The following comments carry measured regression numbers, bug IDs, or design
authority arguments. They must survive the merge intact:

| comment / rationale | location | why it matters |
|---|---|---|
| **ONE-CYCLE BLIND SPOT** in `mc_global_timers` — old `r_*_cnt == 0` readiness lagged one cycle; new core derives next-state once. | `mc_global_timers.sv:92-124` | Authority argument for the one-next-state structure; references board ILA capture with tRTW=20 honoured as 1. |
| **pumice BUG-021** — rank-global ACT gate hold vs. drop measured at 30.77% → 28.57% regression; hold recovers to 30.14%. | `pumice_cmd_arbiter.sv:314-329`, `p:332-359` | Justifies the `w_out_hold` policy. The common core must keep the same fire-stage authority even if the implementation switches to scoria's drop model. |
| **BUG-001 / scoria tRRD/tFAW fire-stage re-check** — measured 3/3 seeds failing with 1-cycle ACT spacing; adds `tfaw_ok_i`/`trrd_ok_i` at `w_out_safe`. | `scoria_cmd_arbiter.sv:328-369`, `s:1147` | Proves the rank-global window must be re-checked at fire. |
| **BUG-002 / tZQCS fire-stage block** — window counter loads on accepted fire, so classify-time check is one cycle early; demand classes gated by `!w_zq_busy` at fire. | `scoria_cmd_arbiter.sv:372-396`, `s:701`, `s:1497-1504` | ZQ calibration correctness; JESD79-3F 3.10 authority. |
| **ISSUE-002** — tFAW/tRRD must gate the fire, not the classify mask, or close-page throughput drops from 30.77% to ~18%. | `scoria_cmd_arbiter.sv:386-403`, `pumice_cmd_arbiter.sv:704-735` (pool comment references it) | Performance/correctness rationale for where the rank-global check lives. |
| **Parked-victim pattern** — PRE on a bank within 3 cycles leaves a stale row image; column picked against it wedges the AR-order drain. | `pumice_cmd_arbiter.sv:704-735` / `scoria_cmd_arbiter.sv:739-822` | Justifies `!w_pre_col_guard` in the column mask. |
| **tZQCS / refresh interaction** — `w_ref_safe` carries `!w_rfc_busy`; refresh is kept out of the ZQ window by cone priority, not by a symmetric term; do not "tidy" it. | `scoria_cmd_arbiter.sv:1786-1809` | Timing-critical design note; 75 MHz margin reference. |
| **P1 init accept/ack gating** — held init request would re-pick into the registered pick every cycle, producing MRS twins; gate must be combinational on the current accept. | `andesite_scheduler_layer.sv:260-302` | Functional bug prevented by the wrapper wiring; keep if the common core supports P1 init. |

Do not rewrite or abbreviate these comments during the mechanical rename pass.
The common-core merge should treat them as invariant documentation.

## 7. Deferrals / not in this step

- No RTL was changed in this step; the inventory is input to Task 5 step 2.
- The actual `mc_scheduler_core` extraction, the maintenance-slot generic
  interface, and the rock-wrapper thinning are out of scope until the merge
  design is approved.
- DV impact (test names, testplan module references, parity tables) is
  documented in the task plan and will be updated when the RTL moves.
