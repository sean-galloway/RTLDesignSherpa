# pumice scheduler + per-bank safe-timer anatomy

Reference for redesigning the command-issue path (issue-per-clock). Everything
below is the *current* RTL (`rtl/fub/scheduler.sv`, `rtl/fub/xbank_timers.sv`),
with the disconnects called out at the end.

---

## 1. What the scheduler is

`scheduler.sv` is the command arbiter at the core of the controller. **Every
cycle it decides what single command to drive on the DFI command bus.** It
consumes:
- the **CAM candidates** — pending read/write ops, each as `{rank,bank,row,col,len,qos,age}`;
- the **per-bank safe timers** — "is an ACT / RD-WR / PRE legal on this bank now?";
- **injection requests** — init sequencer, mode-register, refresh, power-down.

It emits **one DRAM command** (`ACT/PRE/RD/WR/RDA/WRA/REF/MRS/NOP`) plus two
feedback streams: `evt_*` (tells the timers what was issued) and `*_issued_we`
(retires the CAM slot).

```
   CAM (pending ops) ───────────┐
   xbank_timers (safe timers) ──┼──► [ scheduler ] ──► DFI command (1/cycle)
   init/MR/refresh/pdn reqs ────┘        │  │
                                         │  └─ evt_* ──► xbank_timers (update bank state/timers)
                                         └──── *_issued_we ──► CAM (retire slot)
```

---

## 2. Ports (the interface to reason about)

### Inputs — candidates
| signal | meaning |
|---|---|
| `wr_match_pending_i[W]` / `rd_match_pending_i[R]` | slot has pending work |
| `wr_match_rowhit_i` / `rd_match_rowhit_i` | slot's row == the bank's open row (CAM-computed; currently **unused** by the picker) |
| `wr_snap_{rank,bank,row,col,len,qos,age}_i[W]` | per-slot metadata snapshot (write CAM) |
| `rd_snap_{rank,bank,row,col,len,qos,age}_i[R]` | per-slot metadata snapshot (read CAM) |

### Inputs — per-bank safe timers (from `xbank_timers`, all `[RANK][BANK]`)
| signal | asserted when |
|---|---|
| `bank_act_ready_i` | bank may accept an **ACT** |
| `bank_rdwr_ready_i` | bank may accept a **RD/WR** |
| `bank_pre_ready_i` | bank may accept a **PRE** |
| `bank_row_active_i` | bank has a row open |
| `bank_open_row_i[ROW]` | which row is open |
| `tfaw_window_ok_i[RANK]` | fewer than 4 ACTs in the rolling tFAW window (global per rank) |
| `predict_open_i` | HAPPY_HYBRID per-bank "keep open" hint |

### Inputs — injection / config
`init_busy_i`, `init_cmd_{valid,op,bank,row}_i`, `mr_req_i`, `refresh_req_i`,
`pdn_req_i`, `wr_data_ready_i` (pre-pull), **`cfg_page_policy_i[1:0]`** (runtime
page policy: 0=param default, 1=OPEN, 2=CLOSE, 3=HYBRID).

### Outputs (all command/evt outputs are **registered** — +1 cycle)
| signal | meaning |
|---|---|
| `cmd_valid_o`, `cmd_op_o`, `cmd_{rank,bank,row,col,len}_o`, `cmd_{wr,rd}_slot_o` | the issued DRAM command |
| `evt_{act,rd,wr,pre,ap}_o`, `evt_{rank,bank}_o` | feedback to `xbank_timers` (what was issued) |
| `wr_issued_we_o`+`wr_issued_slot_o`, `rd_issued_we_o`+`rd_issued_slot_o` | retire the CAM slot |
| `wr_prepull_{valid,slot,len}_o` | stage write data ahead of the WR command |
| `refresh_grant_o`, `pdn_grant_o`, `mr_grant_o` | injection grants |

---

## 3. Current command-issue: single-op FSM (the thing to replace)

**Picker** — a 2-stage *pipelined* QoS/age tournament over all CAM slots →
`r_wr_cand` / `r_rd_cand` (best pending WR + best pending RD). Pipelined purely
for 100 MHz closure (the flat tournament was a 68-level path). **Cost: the pick
is ~2 cycles stale.** Winner: highest QoS → oldest age → lowest index.

**FSM** — one op in flight, walked through states:
```
S_IDLE ──(latch r_pending = picked slot)──► w_initial_state
   w_initial_state = row-hit ? S_NEED_RDWR : row-miss ? S_NEED_PRE : S_NEED_ACT
S_NEED_PRE ─(bank_pre_ready & cmd_ready)─► S_NEED_ACT
S_NEED_ACT ─(bank_act_ready & tfaw & cmd_ready)─► S_NEED_RDWR
S_NEED_RDWR ─(bank_rdwr_ready & cmd_ready [& wr_data_ready if prepull WR])─► S_DONE
S_DONE ─────────────────────────────────────────────► S_IDLE  (toggle fairness, reset age)
```
- CLOSE ⇒ RD/WR carries auto-precharge (`RDA/WRA`); OPEN ⇒ plain `RD/WR`;
  HYBRID ⇒ `predict_open` decides per op.
- **~3–5 cycles per op, exactly one op in flight, zero bank parallelism.**

**Cycle timing (the FUB test contract, `smoke_wr`):**
```
cyc0 set pending        cyc3 IDLE→NEED_ACT
cyc1 stage-A survivors  cyc4 cmd=ACT (evt_act)
cyc2 r_*_cand valid     cyc5 cmd=WRA (evt_wr, wr_issued)
```

---

## 4. The per-bank safe timers (`xbank_timers.sv`) — the safe-to-issue oracle

Per `(rank,bank)`: a **state machine + JEDEC countdown counters**. This is the
"bunch of safe timers" to build the new scheduler on.

### Bank state
`BANK_IDLE → BANK_ACTIVATING → BANK_ACTIVE → BANK_RD_BUSY / BANK_WR_BUSY → BANK_PRECHARGING → BANK_IDLE`

### Counters loaded on each issued command (via `evt_*`)
| event | new state | counters loaded |
|---|---|---|
| `evt_act` | ACTIVATING | `act_cnt=tRCD` (ACT→RD/WR), `rc_cnt=tRC` (ACT→ACT same bank), `ras_cnt=tRAS` (ACT→PRE), `open_row=row` |
| `evt_rd` | RD_BUSY | `rdwr_cnt=tRTP` (RD→PRE), `ap_pending=ap` |
| `evt_wr` | WR_BUSY | `rdwr_cnt=tWR` (WR→PRE), `ap_pending=ap` |
| `evt_pre` | PRECHARGING | `pre_cnt=tRP` (PRE→ACT) |

### Ready outputs (the "safe" signals) — combinational, then **registered**
| output | condition | JEDEC enforced |
|---|---|---|
| `bank_act_ready` | `IDLE && pre_cnt==0 && rc_cnt==0` | tRP, tRC |
| `bank_rdwr_ready` | `ACTIVE && act_cnt==0 && rdwr_cnt==0` | tRCD (+ RD/WR spacing) |
| `bank_pre_ready` | `ACTIVE && rdwr_cnt==0 && ras_cnt==0` | tRAS, tRTP/tWR |
| `bank_row_active` | `ACTIVE || RD_BUSY || WR_BUSY` | — (open-row tracking) |

Reset: all `bank_act_ready=1` (banks idle), others 0.

### NOT per-bank (separate/global — handle alongside)
- **tFAW** — `tfaw_window_ok_i[rank]`: ≤3 ACTs in the rolling window (own FUB).
- **tWTR / tCCD / tRTW / bus turnaround** — currently coarse / not strictly
  per-bank; the RD↔WR turnaround is partly the W/R arbitration's job. Worth a
  column in your spreadsheet — these are rank/bus-global, not per-bank.
- **predict_open** — HAPPY_HYBRID hint (page_predictor FUB).

---

## 5. THE DISCONNECTS (why a naive per-cycle picker fails; what the fix needs)

1. **2-cycle feedback latency.** `evt_*` is registered in the scheduler (+1),
   and `xbank_timers`' ready/row-state outputs are registered (+1). So after you
   issue a command, the bank's state/timers do **not** reflect it for **2
   cycles**. The current FSM survives this because it tracks op progress
   *locally* in `r_state` (it knows "I just ACTed, next is RD/WR") — it does
   **not** re-derive the needed command from `bank_row_active`. A stateless
   per-cycle picker that re-derives from `bank_row_active` each cycle sees stale
   state and re-issues ACT / can't sequence one op. **(This is what failed 19/23.)**

2. **Pipelined pick is 2 cycles stale.** `r_wr_cand`/`r_rd_cand` reflect the CAM
   from ~2 cycles ago → a per-cycle issuer can pick a slot whose bank has since
   changed, and can re-pick a just-issued slot before its `issued_we`→CAM
   `match_pending` drops (~2 cycles) → **double-issue**.

3. **Right shape = per-bank op machines + arbiter (LiteDRAM bankmachine model).**
   Give each bank a tiny local FSM that sequences ACT→RD/WR→(PRE) for *its*
   pending op, immune to the 2-cycle feedback (it remembers what it issued). A
   per-cycle arbiter then picks, among the banks whose next command's safe-timer
   is ready, one to drive this cycle. Result: one command/cycle across banks,
   full bank-level parallelism + intra-page batching.

4. **Reuse (don't rebuild):** `xbank_timers` (the safe timers — already correct),
   the CAM, the QoS/age tournament (repurpose as the *arbiter* over ready banks),
   the `evt_*`/`issued_we` interfaces, the runtime `cfg_page_policy_i`, and the
   pre-pull handshake (`wr_prepull_*`/`wr_data_ready_i`).

5. **Timing gate.** Design sits at ~0 ns slack @100 MHz; the picker is pipelined
   for closure. Any new per-cycle readiness logic must stay shallow/pipelined,
   and a Vivado STA (WNS ≥ 0) is a required sign-off — not just sim.

### Latency cheat-sheet for the spreadsheet
| edge | cycles |
|---|---|
| scheduler decides issue → `cmd_*_o`/`evt_*_o` on the wire | +1 (registered) |
| `evt_*` → `xbank_timers` state update → `bank_*_ready_o` reflects it | +1 (registered) → **2 total** |
| `issued_we` → CAM `match_pending` drops | ~2 |
| CAM/age → pipelined pick (`r_*_cand`) valid | +2 (2-stage tree) |
