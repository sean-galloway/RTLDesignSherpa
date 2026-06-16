# Known Issue: DMA hang at 4–7 active channels under heavy monitoring

**Status:** 🔴 OPEN — under investigation
**Severity:** HIGH — DMA deadlocks (no data loss; hang, not corruption)
**Date Reported:** 2026-06-16
**Affects:** `axi_monitor_base.sv` (`block_ready` / completion-feedback path),
as integrated by `axi4_master_rd_mon.sv` / `axi4_master_wr_mon.sv` in the
STREAM characterization harness (`stream_char_harness.sv`).

---

## Summary

With a heavy monitor preset (`debug-compl`: completion packets enabled) and
**4, 5, 6, or 7** active DMA channels, the DMA **hangs** — the non-first
channels stall mid-transfer and never complete. **1, 2, 3, and 8** active
channels complete normally. The default ("allow basic") monitor preset
passes every channel count (the full 40-config perf matrix is clean), so the
trigger is the heavy completion-monitor traffic, not plain data movement.

This is a **hang, not data corruption.** No bad data is committed; the
transfer simply never finishes.

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

## Affected configurations

| active channels (8 desc each) | result |
|---|---|
| 1, 2, 3 | completes, CRC ok |
| **4, 5, 6, 7** | **hang (timeout)** |
| 8 | completes, CRC ok |

- Monitor preset: `debug-compl` (completions on). Default preset: not affected.
- 100 % reproducible (verified across repeated runs, runner-direct — not an
  `hb_measure` artifact).

---

## Reproduction

```bash
cd projects/NexysA7/stream_characterization/flows-stream-bridge/host
source $REPO_ROOT/env_python
python3 run_characterization.py --port /dev/ttyUSB2 --channels 4 \
    --configs 8desc_4ch_1MB --mon-config debug-compl --compression on
# -> TIMEOUT after 120s; AXI_RD_COMPLETE = AXI_WR_COMPLETE = 0
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

Use the default monitor preset (not `debug-compl`) for >3-channel
characterization runs, or keep `debug-compl` runs to ≤3 active channels (or
exactly 8). The default-preset perf matrix is unaffected.
