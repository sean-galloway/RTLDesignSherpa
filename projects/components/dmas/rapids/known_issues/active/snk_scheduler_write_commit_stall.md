# RAPIDS SINK scheduler never returns to idle — write-commit accounting stall

**Status:** RESOLVED (2026-07-16). Root cause was in the CHARACTERIZATION HARNESS
slave, NOT the RAPIDS/STREAM DUT. Fixed + validated in deterministic sim.
**Severity:** High (functional stall in characterization; DUT itself was correct).
**Fix:** `rtl/amba/shared/axi4_slave_wr_crc_check.sv` — added a B-response FIFO.

---

## 0. RESOLUTION (read this first)

The RAPIDS/STREAM sink write engine was **correct all along**. The wedge was
caused by the synthetic write slave in the characterization harness,
`axi4_slave_wr_crc_check.sv`, which tracked only **one** outstanding B response
(a single `r_b_pending` bit). With 8 channels issuing gapless back-to-back bursts
(and `WR_XFER_BEATS=8` interpreted as ARLEN → 9-beat bursts + a trailing 1-beat
burst), a WLAST coincides with a B consume and the new B is dropped — **~1 B lost
per channel**. The DUT then waits forever for a B the slave never sent, so
`r_write_beats_to_commit` sits one beat short and the channel never leaves
`CH_XFER_DATA`. The slave's own comment already predicted it: *"a higher-rate
multi-channel slave would need a B FIFO."*

**How it was found (the decisive step):** run the exact board config (8 active
channels, beats=64 — not the self-check default 4ch/8-beat) in the cocotb harness
→ **deterministic sim repro** of the board wedge. VCD analysis of one wedged run:
**64 AW handshakes, 64 WLASTs, 512 W beats (all correct)** but only **56 `bvalid`
pulses** with `bready` never gating → the slave produced 56 B's for 64 bursts.

**Fix:** replaced the single `r_b_pending` bit with a `gaxi_fifo_sync` B-response
FIFO (depth 16) holding `{user,id}`, pushed on WLAST, popped on the B handshake.
Lint-clean; the 8ch/64-beat sim that previously wedged (`timeout:
snk_system_idle=0`) now **passes**.

**Consequences:**
- The perf report numbers remain valid (the meter's deterministic close captured
  the real data-path utilization regardless of the trailing stall).
- The host `CHANNEL_RESET` workaround is now unnecessary (harmless to leave).
- Earlier hypotheses in §5–§7 below (B-phase pop/commit race; phantom AW) were
  BOTH prototyped and REJECTED on silicon, then reverted. Kept as the debug trail.

---

## 1. Summary

After a SINK (AXIS→memory) transfer completes with **correct data** (golden CRC
passes, every beat written), the sink scheduler **never returns to idle**:
`snk_system_idle` stays low. Because the characterization harness re-uses the
same channels for the next run, the *second* back-to-back run — and *any*
`active < build_width` configuration — wedges (writes 0 beats). The data path is
fine; this is purely a **completion-bookkeeping stall**.

The characterization host currently works around it by pulsing the existing
`CHANNEL_RESET.CH_RST[7:0]` CSR before every run (forces every channel FSM to
`CH_IDLE`, flushes the descriptor FIFOs). **That is a workaround, not a fix** —
the sink should self-return to idle at end-of-descriptor.

---

## 2. Symptom (board)

| Observation | Value |
|-------------|-------|
| Data correctness | golden CRC PASS, all beats written |
| Run 1 (fresh board) | passes, but `SNK_IDLE = 0` afterward |
| Run 2 (same channels) | wedges — `wr_beats = 0`, times out |
| `active < 8` on an 8-ch build | wedges immediately (writes 0) |
| Discriminator: +0.3 s settle delay | still wedges (rules out in-flight AXI B retirement) |
| Discriminator: +`CHANNEL_RESET` | 5/5 clean (confirms stale-state, not fabric) |

The 0.3 s settle (30 M cycles ≫ any outstanding B) not helping rules out a stuck
fabric/in-flight cycle; the scheduler-level `CHANNEL_RESET` clears it, so the
stuck state is in the **scheduler/descriptor completion path**.

---

## 3. ILA evidence

Two on-silicon ILA passes (Genesys 2; `tcl/build_ila.tcl` + `tcl/capture_ila.tcl`,
wedge reproduced by `host/run_sink_once.py` with `CHANNEL_RESET` disabled).

**The wedge is INTERMITTENT** — a single fresh run often completes; back-to-back
runs (no reset) trip it within 1-2 runs. Intermittency = a timing race, not a
deterministic logic error. (A size sweep also showed a non-monotonic pattern:
1 burst/ch and 8 bursts/ch wedged, 2-7 did not — noise from the race, not a
clean threshold.)

**Pass 1 — which FSM state (`reports/ila_sched_state.csv`).** All 8 sink channels:

| ch | `r_current_state` | `w_read_complete` | `w_write_complete` | `descriptor_valid` |
|----|-------------------|:-----------------:|:------------------:|:------------------:|
| 0–7 | **`CH_XFER_DATA`** | **1** | **0** | 0 |

Frozen in `CH_XFER_DATA`: reads finished, writes never report complete. Not
`CH_NEXT_DESC` (no chaining/descriptor wait), not `CH_ERROR`.

**Pass 2 — the commit accounting (`reports/ila_wedge.csv`, beats=64).** All 8
channels identical:

| signal | value | meaning |
|--------|-------|---------|
| `r_current_state` | `CH_XFER_DATA` | stuck |
| `r_write_beats_to_commit` | **1** | one beat short of length=64 |
| `r_write_beats_remaining` | 0 | all beats *issued* |
| `b_phase_txn_fifo_empty[7:0]` | `0x00` | FIFO **not empty** — a dangling entry |
| `b_phase_txn_fifo_dout.beats` | **1** | the stuck entry is a **1-beat** burst |
| `r_commit_beats` (last) | **9** | a burst committed **9** beats |

Burst size: the host sets `WR_XFER_BEATS=8`, but the RTL treats
`cfg_axi_wr_xfer_beats` as an **ARLEN** value (line ~420: "stores ARLEN
(0==1 beat)"), so bursts are **9 beats**. length-64 therefore splits as
**7×9 + 1** — matching `commit_beats=9` and the dangling `dout.beats=1`.

**Decisive:** the run **passes CRC** (all 64 beats written correctly), so the
1-beat burst's **B response DID arrive** — yet its FIFO entry is un-popped and its
beat un-committed, and the B-phase FIFO is depth 16 (8 bursts cannot overflow it).
So a B response **landed but was not accounted** — a race in the B-phase FIFO
pop + commit-strobe logic (empty-flag / read-latency staleness), leaving a dangling
entry and freezing `r_write_beats_to_commit` at 1 forever.

---

## 4. Root-cause chain (RTL)

```
snk_system_idle = &scheduler_idle                        (rapids_snk_beats.sv:637)
  scheduler_idle = (r_current_state == CH_IDLE)           (scheduler_beats.sv:921)
    stuck in CH_XFER_DATA — can't reach CH_COMPLETE/CH_IDLE
      exit gated by w_exec_complete = w_read_complete && w_write_complete
        w_write_complete = (r_write_beats_to_commit == 0)  (scheduler_beats.sv:601)
          r_write_beats_to_commit never drains to 0
            decrements on sched_wr_commit_strobe/beats     (scheduler_beats.sv:559)
              driven by axi_write_engine_beats.sv B-response accounting
```

`r_write_beats_to_commit` is loaded to the descriptor `length` and drained as the
write engine reports **committed** (B-response) beats via `sched_wr_commit_strobe`
/ `sched_wr_commit_beats`, sourced from a per-channel **`b_phase_txn_fifo`**
(pushed on AW-issue with `awlen+1`, popped on each B response). The committed sum
comes up **short of `length`**, so the counter never reaches 0.

There is a documented hazard right in the write engine
(`axi_write_engine_beats.sv:~377`): the drain-request staleness / **"phantom
burst"** race, where `drain_ctrl` drops a redundant drain-request's pointer
advance — the comment ends *"…post-fix it just stalls forever."* That "stalls
forever" is consistent with this wedge.

---

## 5. The FUB(s)

Two candidate locations, and which one it is decides the STREAM blast radius (§6):

- **(A) `axi_write_engine_beats.sv` — commit reporting.** If the write engine
  reports fewer committed beats than it issued (drain-staleness/phantom-burst
  race, or a `b_phase_txn_fifo` push/pop imbalance), the scheduler counter can
  never reach 0. **This file is shared verbatim with STREAM (§6) → a bug here is
  in BOTH.**
- **(B) `scheduler_beats.sv` — commit accumulator.** RAPIDS decrements
  `r_write_beats_to_commit` *inside* the `CH_XFER_DATA` FSM case
  (`scheduler_beats.sv:559`). STREAM instead uses a **dedicated, always-running
  accumulator** outside the FSM. **This logic diverged → a bug here is likely
  RAPIDS-specific.**

ILA pass 2 points at **(A)**: the counter stalls because a real B response is not
turned into a commit (dangling FIFO entry), i.e. the write engine's B-phase
pop/commit under-reports. The scheduler's saturating subtract cannot recover an
*under*-commit, so even STREAM's hardened accumulator would stall on this input —
which makes (A), the **shared** write engine, the more worrying location.

### 5a. Read engine — verified NOT affected

`axi_read_engine_beats.sv` has **zero** commit-style signals (no
`sched_rd_commit` / `to_commit` / `b_phase_txn_fifo` / `m_axi_bvalid` /
`commit_strobe`). Reads have **no B/write-response channel**; completion is a
**single counter** (`r_read_beats_remaining`) drained by `sched_rd_done_strobe`
on `m_axi_rvalid && rready && rlast` (actual R-data arrival) — there is no
two-counter issue-vs-commit split to desynchronize. Empirically the SOURCE path
passes characterization at 99.8% util, its scheduler returns to idle, and ILA
pass 1 showed `w_read_complete=1`. **The read path is clean; this defect is
write-side only.**

---

## 6. STREAM-inheritance analysis (the "is it in both?" question)

RAPIDS beats was resynced from STREAM, so the two were compared directly.

### 6a. Write engine — IDENTICAL (shared risk)

`projects/components/stream/rtl/fub/axi_write_engine.sv` and
`projects/components/rapids/rtl/fub_beats/axi_write_engine_beats.sv` are **both
1076 lines and byte-identical except the include** (`stream_imports.svh` vs
`rapids_imports.svh`) and the SPDX/module-name header — **12 diff lines, zero
logic differences.** The commit reporting, the `b_phase_txn_fifo`, the WLAST/drain
handling (`axi_wr_sram_drain = m_axi_wvalid && m_axi_wready`), and the entire
phantom-burst/drain-staleness block are a **verbatim copy**.

> **Conclusion:** if the under-count originates in the write engine (candidate A),
> **STREAM carries the identical latent bug.**

### 6b. Scheduler — DIVERGED (RAPIDS simplified STREAM's hardened design)

`stream/rtl/fub/scheduler.sv` vs `rapids/rtl/fub_beats/scheduler_beats.sv` differ
by ~992 lines. The commit accounting specifically:

- **STREAM** keeps `r_write_beats_to_commit` in a **dedicated accumulator** run
  every cycle regardless of FSM state:
  `w_ctc_next = r_write_beats_to_commit + r_ctc_pending_add`, then a **saturating**
  subtract on `sched_wr_commit_strobe`. Its comment explicitly warns that "the
  write engine can commit burst-granular B-responses exceeding a short
  descriptor's launched length … the accumulator legitimately underflows and must
  clamp rather than wrap (a wrap leaves `w_write_complete` stuck low → channel
  never idle)" and cites a **named regression `datapath_wr_test varying_lengths`.**
- **RAPIDS** moved the decrement back **inside** the `CH_XFER_DATA` FSM case and
  **dropped the `r_ctc_pending_add` pending-add**; it keeps only the saturating
  subtract.

> **Conclusion:** STREAM has *already been bitten by and hardened against* exactly
> this "commit accumulator leaves `w_write_complete` stuck low" failure, with a
> regression guarding it. RAPIDS' simplified port re-exposes that surface. So the
> manifest wedge is **most likely RAPIDS-specific (candidate B)** — but the shared
> write engine (6a) means the underlying hazard is present in both trees.

---

## 6b. Fix attempt REJECTED on silicon — it is the phantom AW, not a dropped B

A first fix hypothesis (the dangling entry = a B response dropped by the B-phase
pop/commit due to empty-flag/read-latency staleness) was prototyped: a per-channel
pending-B counter making the commit fire only on an actual dequeue. It lint-clean'd
and passed the harness self-checks, but a clean Genesys bitstream with it **STILL
WEDGED on run 1** (beats=64). So the dangling 1-beat FIFO entry does **not** have a
late/dropped B — it has **no B at all**: it is a **phantom AW** from the
drain-request staleness race (`axi_write_engine`'s own comment, ~line 377:
"the wr engine then commits a phantom burst ... post-fix it just stalls forever").
A phantom AW pushes a b_phase_txn_fifo entry but its W has no SRAM data, so the AXI
slave never returns a B, so no commit ever drains that beat -> the scheduler's
`r_write_beats_to_commit` sits one beat short forever. The B-phase-commit path is
NOT the bug; the fix was reverted.

**Refined root cause:** the drain-request staleness / effective-availability logic
(`w_drain_t` / `r_drain_tminus1` / `w_effective_avail` / `w_pending_drain`,
~lines 383-430) still lets an AW be arbitrated for a channel whose SRAM drain is
already exhausted -> a phantom AW -> a dangling FIFO entry with no B. This is
aggravated by `WR_XFER_BEATS=8` being used as ARLEN (9-beat bursts -> a trailing
1-beat remainder that sits right on the staleness boundary).

## 7. How to confirm and fix (recommended next steps)

Next ILA should probe the **AW-issue / drain side** (not the B side): per channel
`m_axi_awvalid`/`awready`/`awlen`, `r_aw_channel_id`, `axi_wr_drain_req`/`size`,
`axi_wr_drain_data_avail`, `w_effective_avail`, `w_pending_drain`, and the AW count
vs `sched_wr_beats`. Expect: an **extra AW** issued after the real data is drained
(AW count exceeds ceil(length/9)), i.e. the phantom. Fix in the effective-avail
math so a channel with no remaining drainable data cannot be granted an AW; then
this becomes a shared rapids+stream RTL fix. Separately correct the
`WR_XFER_BEATS`-as-ARLEN mismatch so bursts are a clean size.

1. **One more ILA pass** on the write engine: probe per-channel
   `b_phase_txn_fifo` push-count vs pop-count and the running sum of
   `sched_wr_commit_beats` vs the descriptor `length`. If committed-sum < length
   at the write-engine boundary → candidate A (shared with STREAM). If the write
   engine reports the full `length` but the scheduler counter still hangs →
   candidate B (RAPIDS scheduler).
2. **Run STREAM back-to-back on its own harness** (no reset between runs) and see
   whether it wedges the same way. STREAM's characterization ran large matrices —
   check whether it resets between configs (masking) or genuinely does not wedge
   (which would point at candidate B, i.e. STREAM's dedicated accumulator saving
   it).
3. If candidate B: port STREAM's dedicated commit accumulator (`w_ctc_next` +
   `r_ctc_pending_add`, saturating) into `scheduler_beats.sv` and add the
   equivalent `varying_lengths` regression to the RAPIDS beats macro test.

## 8. Reproduce / tooling

- ILA build:   `BOARD=genesys2 vivado -mode batch -source tcl/build_ila.tcl`
- ILA capture: `RAPIDS_CHAR_JTAG_SERIAL=200300B818A0 vivado -mode batch -source tcl/capture_ila.tcl`
- Wedge repro (no reset): `host/run_sink_once.py /dev/ttyUSB1`
- Capture evidence: `reports/ila_sched_state.csv`

## 9. Current workaround

`host/run_characterization.py` `reset_channels()` pulses `CHANNEL_RESET` on both
halves before every run. It makes the full 24-config char matrix run in one
programming and unblocks `active<8`, but it does **not** fix the RTL — the sink
must self-return to `CH_IDLE`.
