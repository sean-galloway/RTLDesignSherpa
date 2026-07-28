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

<!-- End Header -->

# Known Issue: cluster state-accumulation wedge (long-session DMA hang)

**Status:** ✅ ROOT-CAUSED AND FIXED — commits `cb29e226` (saturation-recovery
contract) and `95c9490a` (runtime-disable auto-retire)
**Severity:** MEDIUM — only manifested after a long session of many mixed
runs; a full FPGA reprogram fully cleared it. Hang, not data corruption.
**Date Reported:** 2026-06-16
**Date Fixed:** 2026-07-21
**Affects:** `axi_monitor_trans_mgr.sv` / `axi_monitor_base.sv` /
`axi_monitor_reporter.sv` (`block_ready` never re-asserting once the
transaction table saturated).

---

## Resolution (2026-07-21)

The "suspected mechanism" below was correct in outline: the wedge was the
monitor's `block_ready` latching low permanently once the transaction table
saturated. Two independent slot-leak mechanisms fed the saturation, both
fixed:

1. **Stray non-last data beat poison** (`cb29e226`): a stray beat matching
   only already-closed entries dragged a terminal entry back to
   `TRANS_DATA_PHASE` with `data_completed` set — a state nothing could
   close and no timeout term matched. Each occurrence leaked a slot until
   occupancy pinned at `MAX_TRANSACTIONS`, and the old flat `MAX-3`
   `block_ready` margin placed the reopen threshold exactly AT the
   saturation point, so `block_ready` could never re-assert. Fixed by the
   saturation-recovery contract (`monitor_common_pkg::cmd_entry_reserve`):
   command entries capped below the reopen threshold, stray non-last beats
   absorbed without lifecycle updates, formal properties added
   (`ap_no_reopened_complete`, `ap_cmd_entry_cap`, mutation-checked).
2. **Runtime-disabled packet-class leak** (`95c9490a`): with a class
   compiled in but cfg-disabled (e.g. `debug-compl`-style presets toggling
   completion reporting), terminal entries were never marked reported and
   leaked. The reporter now auto-retires terminal entries of any class
   that is compiled out or runtime-disabled.

This explains the observed signature: state accumulated across many mixed
runs (each leak is permanent until reprogram), the `debug-compl` preset was
implicated (enable toggling), and the per-run soft reset did not clear the
monitor's transaction CAM. Regression: `val/amba/test_axi_monitor_trans_mgr.py`
(`phase_saturation_recovers`), `val/amba/test_axi_monitor_runtime_disable.py`,
and the 100-seed deliberately-undersized `test_stream_core_mon_backpressure`
sweep.

Note: a separate 8-channel STREAM **engine-side** wedge (params 7/9/11 of
the multi-channel stress family) was later fixed and is NOT a monitor issue.
8-channel STREAM builds are supported; there is no channel-count boundary.

The original write-up is retained below for history.

---

## ⚠️ Correction (2026-06-16)

An earlier version of this issue claimed a **100% reproducible** DMA hang at
**4–7 active channels** under the `debug-compl` preset. **That was wrong.**
On a **freshly reprogrammed board the entire 1–8 channel sweep passes**
(all CRC=ok, clean monotonic record counts), and `8desc_4ch` passes 8/8
consecutive runs plus the `hb_measure` path. The mid-session failures were an
**accumulated-state wedge**, not a clean-state config bug.

## Summary

After a long session of many mixed characterization runs (wide resp-delay
sweeps + `hb_measure` compression sweeps interleaving compression on/off and
`debug-compl`), the cluster reaches a **wedged state** in which some configs
(observed: 4–7 active channels under `debug-compl`) **hang** — channels stall
mid-transfer, zero beats move, 120 s timeout. The per-run soft-reset /
cluster-reset does **not** clear this; only a full FPGA reprogram does.

From a **clean (reprogrammed) board the same configs pass reliably**, so this
is a **reset-completeness / state-accumulation** problem in the harness, not
an inherent 4–7-channel DMA logic bug. It is a hang, not data corruption.

---

## Symptoms (FPGA, `8desc_4ch_1MB`, `debug-compl`, compression on)

Run times out at 120 s. Hang snapshot:

```
GLOBAL_STATUS    = 0x00000000   (not done)
CHANNEL_ENABLE   = 0x0000000F   (4 channels enabled)
CHANNEL_IDLE     = 0x000000F1   (ch0 idle/done; ch1,2,3 stuck)
SCHEDULER_IDLE   = 0x000000F5
AXI_RD_COMPLETE  = 0x00000000   (zero completions)
AXI_WR_COMPLETE  = 0x00000000
SCHED_ERROR      = 0x00000000   (no error flagged)
trace wr_ptr=242, overflow=0    (monbus flowing, not backed up to overflow)
```

Channel 0 finishes; channels 1–3 deadlock. `hb_measure` previously reported
this as "CRC=MISMATCH" — that was a *consequence* of non-completion (stale
CRC read after timeout), not bad data.

**It is a hard deadlock (zero beats moved), not a throttle.** A
progress heartbeat (`run_characterization.py -v`) over the first 60 s of
the hang shows the harness timer *running* (`timer_cyc` advances
510M → 6009M) while `r_last_beat_cyc` and `w_last_beat_cyc` stay **frozen
at 0** — i.e. not a single read or write data beat ever completes. The
clock is alive and `done` is correctly false; the DMA genuinely moves no
data. So done-detection is *not* the problem — the transfer never starts.

```
[progress  5.0s] timer_cyc=510347896  r_last_beat_cyc=0 w_last_beat_cyc=0 running=True done=False
[progress 30.0s] timer_cyc=3011004215 r_last_beat_cyc=0 w_last_beat_cyc=0 running=True done=False
[progress 60.0s] timer_cyc=6009276700 r_last_beat_cyc=0 w_last_beat_cyc=0 running=True done=False
```

---

## Behaviour by board state

| board state | result |
|---|---|
| fresh reprogram | **all 1–8 channel configs pass** (CRC=ok; `8desc_4ch` 8/8 consecutive; `hb_measure` 1–8ch sweep all ok) |
| after a long mixed-run session (wedged) | some configs hang (observed 4–7 active ch under `debug-compl`); cleared only by reprogram |

- Monitor preset of the *observed* wedged failures: `debug-compl`. Default
  preset never showed it.
- The 4–7-fail / 1-2-3-8-pass pattern is a snapshot of the **wedged** state,
  not a clean-state property — it does not reproduce after reprogram.

---

## Reproduction

Clean-state (does NOT fail — confirms the config itself is fine):

```bash
cd projects/NexysA7/stream_characterization/flows-stream-bridge/host
source $REPO_ROOT/env_python
# (full reprogram first: cd .. && make program)
python3 run_characterization.py --port /dev/ttyUSB2 --channels 4 \
    --configs 8desc_4ch_1MB --mon-config debug-compl --compression on
# -> RESULTS: 1 passed (and 8/8 on repeat)
```

Wedged-state (the open bug): reached only after a long sequence of mixed
runs (wide resp-delay sweeps + `hb_measure` compression sweeps). Once wedged,
`8desc_4ch` debug-compl times out at 120 s with
`AXI_RD_COMPLETE = AXI_WR_COMPLETE = 0` and zero beats moved. The exact
wedging operation is not yet bisected (TODO).
```

---

## Suspected mechanism (not yet confirmed in sim)

The monitors are **not** passive in this harness. `block_ready` gates the
upstream handshake:

```
axi4_master_rd_mon.sv:434   fub_axi_arready = w_core_fub_axi_arready & w_block_ready;
axi4_master_wr_mon.sv:439   fub_axi_awready = w_core_fub_axi_awready & w_block_ready;
axi_monitor_base.sv:454     block_ready = active_count < (MAX_TRANSACTIONS - BLOCK_MARGIN);
```

`block_ready` de-asserts as the transaction table fills while completion
reporting can't free entries fast enough. `axi_monitor_base.sv:444`
documents a *prior* `block_ready` form that deadlocked
(`block_ready=0 → ready=0 → count never increments`); the current code adds
a MAX-2/MAX-3 margin to avoid it. The hypothesis is that heavy completion
traffic at *partial* channel population re-trips an equivalent corner so the
shared engine stalls the non-first channels. The 4–7-hang-but-8-complete
pattern points at a `block_ready` / `active_count` (margin) corner rather
than simple monotonic load (8 channels generate the most traffic yet
complete).

**Caveat:** the monbus trace did not overflow (`wr_ptr=242`), so the
backpressure is internal (transaction-table / event-reported feedback),
not the bulk-trace SRAM filling.

---

## Simulation status

- The compressor / half-beat RTL is bit-exact to the golden model on the
  real multi-channel capture (`val/amba/test_monbus_halfbeat.py`) — **not**
  implicated.
- `stream_char` cosim at 4 channels + compression **passes** with the small
  default workload (4096 beats) — it does not generate enough sustained
  completion pressure to fill the transaction table, so the hang does not
  trigger. Reproducing it in sim needs forced table saturation (heavier
  completion load and/or a parameterized smaller `MAX_TRANSACTIONS` / monbus
  FIFO for a sim-only build). **TODO.**

---

## Workaround

`make program` (full FPGA reprogram) fully clears the wedge and restores
clean behaviour. For long unattended characterization sessions, reprogram
periodically rather than relying on the per-run soft-reset.

## Next step (root-cause)

Bisect which operation in a long run sequence first wedges the cluster
(suspects: the `hb_measure` compression sweeps, compression on/off toggling,
or the response-delay queues), then find the state that survives the
soft-reset / `clear_stats` / per-channel reset and add it to the reset. The
fix is to make the per-run reset as complete as a reprogram.
