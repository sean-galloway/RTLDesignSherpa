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

# Known Issue: Write Data Before Its Address Was Dropped (FIXED)

**Module:** `axi_monitor_trans_mgr.sv` (every AXI write monitor: `axi4_*_wr_mon`, `axi5_*_wr_mon`, and their `_cg` twins)
**Tracker:** amba BUG-037 (closed 2026-09-28); the visible symptom was filed against the ID filter, TASK-073
**Status:** FIXED 2026-09-28

## Fix (2026-09-28)

`axi_monitor_trans_mgr` keeps a small FIFO (`EARLY_BURSTS = 4`) of write
bursts that arrived before any AW, one beat count per completed burst plus the
burst still open. A W beat with no entry awaiting data goes there instead of
being dropped. Each write allocation absorbs the oldest early burst as its
data phase: `data_started`, `data_beat_count`, and `data_completed` when the
burst's LAST was seen or the count meets `expected_beats`. AXI4 orders write
data in AW order, so the next AW is the owner by definition and no ID is
needed. Two guards keep the accounting straight while early data is pending:
the same-cycle AW+W bypass is off (that beat belongs to a later transaction
and is queued too), and the bypass never attaches a beat to a pending AW whose
data phase is already complete.

More than four completed bursts ahead of their addresses keeps the old
behaviour (the excess is dropped). One or two is what real masters do.
`axi_monitor_lite` has carried the one-burst form of this since it was built.

## Summary

AXI4 lets a master present W beats before the AW they belong to. On an AXI
write monitor, a W beat that found no entry awaiting data was silently
dropped: `data_wants_alloc` is gated with `!IS_AXI` (an AXI4 W beat has no ID
to key an orphan entry on), so nothing recorded it. When the AW then arrived,
its entry waited for beats that had already passed, and the B response closed
it as `EVT_PROTOCOL` ("response before data"). A legal write was reported as a
protocol violation and its completion packet was never emitted.

## Symptoms

- `Error/PROTOCOL` packets on legal traffic from a master that sends W ahead
  of AW (the framework's AXI4 master BFM does, with several outstanding).
- Missing completions: `val/amba/test_axi4_wr_mon_id_filter[8-32-32-16]` at
  `SEED=94641` reported `completions=6` for eight writes with the ID filter
  off, and lost owned write 4 with it on. The filter was blamed (TASK-073's
  symptom); it was not the cause.

## Reproduction

```
cd val/amba
SEED=94641 REG_LEVEL=GATE python3 -m pytest \
  "test_axi4_wr_mon_id_filter.py::test_axi4_wr_mon_id_filter[8-32-32-16]"
```

A scratch harness replaying the same stimulus and dumping every AW/W/B
handshake and every monbus packet showed two single-beat W bursts on the bus
before their AWs, then `0x1080` and `0x11C0` completing as `PROTOCOL` with
`data_completed = 0`.

## Root cause

Two mechanisms, found in order:

1. **Early W beats had nowhere to go.** The WID-less write select picks the
   oldest entry awaiting data; with none, the beat fell through to
   `data_wants_alloc`, which is `!IS_AXI`-gated for writes, so no orphan was
   allocated and the beat vanished.
2. **The same-cycle bypass could steal a beat.** Once early bursts were
   absorbed, a pending AW (allocated on `cmd_valid`, handshake not yet done)
   whose data phase was already complete still qualified for the bypass and
   took the next transaction's beat.

## What was ruled out

The ID filter itself. TASK-073 had already stopped filtering W beats against
the live `m_axi_awid`; with that fix in place the filter-OFF leg still lost
completions, which is what pointed at the data path rather than the filter.

## Verification

- The test's own cell at `SEED=94641` is the RED-to-GREEN gate: filter off
  `completions=8`, filter on `owned_completed=[0, 2, 4, 6]`.
- `val/amba` GATE from `make clean-all` and the `axi_monitor_trans_mgr` /
  `axi_monitor_base` formal harnesses re-run after the change; results are in
  the fixing commit. The harnesses instantiate `IS_READ=1`, so the write
  path is covered by simulation, not by proof.
