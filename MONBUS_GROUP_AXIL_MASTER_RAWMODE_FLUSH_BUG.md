# Bug (RESOLVED): monbus group master-write path never flushed for an AXIL master in raw mode

**Status:** RESOLVED — fixed in `rtl/amba/shared/monbus_group_core.sv` and
validated (the bridge capture test went from 0 → 9 master-write beats).
**Severity:** High — the bulk-trace (master-write) path was completely
non-functional for two of the four `monbus_<p1>_<p2>_group` members.
**Found:** 2026-06-11, while syncing the bridge generator to the new
`monbus_<p1>_<p2>_group` family (commit `3d91e4de`).
**Found by:** `projects/components/bridge/dv/tests/test_bridge_1x2_rd_monitor_capture.py`

This document is retained as a postmortem: it records the defect and, more
importantly, the **`val/amba` coverage gap** that let it ship. The test
additions in the last section are still worth doing so the gap stays closed.

---

## TL;DR

When the monbus group's master-write side was an **AXIL** master
(`MAX_BURST_BEATS = 1`) **and** raw (uncompressed) mode was selected
(`USE_COMPRESSION = 0` ⇒ `BEATS_PER_UNIT = 3`), the burst writer could never
emit a record. The per-burst beat plan was capped at `MAX_BURST_BEATS = 1`,
then rounded **down** to a whole 3-beat record, which yielded **0**. The
write FSM's `WR_IDLE → WR_AW` guard required `beats_planned_units >= 3`, so it
never left idle. Packets accumulated in the write FIFO forever and nothing was
ever written out the master port.

Affected family members:

| Module | Master leaf | `MAX_BURST_BEATS` | Raw-mode master-write |
|---|---|---|---|
| `monbus_axil_axil_group` | `axil4_master_wr` | **1** | was BROKEN |
| `monbus_axi4_axil_group`  | `axil4_master_wr` | **1** | was BROKEN |
| `monbus_axil_axi4_group`  | `axi4_master_wr`  | configurable (default 64) | OK |
| `monbus_axi4_axi4_group`  | `axi4_master_wr`  | configurable (default 64) | OK |

Compressed mode (`USE_COMPRESSION = 1` ⇒ `BEATS_PER_UNIT = 1`) was **not**
affected, because a 1-beat record fits a 1-beat burst.

---

## Root cause

### The geometry pipeline

`rtl/amba/shared/monbus_group_core.sv`

```
BEATS_PER_UNIT = (USE_COMPRESSION == 0) ? 3 : 1;

cap_fifo           = beats_in_fifo;                       // occupancy
cap_max            = MAX_BURST_BEATS;                      // 1 for an AXIL master
beats_cap_max      = min(cap_max, cap_fifo);              // = min(1, N) = 1
beats_cap_geometry = min(beats_to_limit, beats_to_4kb);  // large
beats_planned      = min(beats_cap_geometry, beats_cap_max);   // = 1
beats_planned_units = (beats_planned / 3) * 3;           // = (1/3)*3 = 0
```

### The FSM guard

```
// WR_IDLE
if (do_flush && (beats_planned_units >= BEATS_PER_UNIT)) begin
    ... // issue AW, move to WR_W
end
```

With `beats_planned_units == 0`, the `>= 3` guard never fired even though
`do_flush == 1`: the writer was built to emit one whole record per AXI burst,
but a 3-beat record cannot be expressed as a `MAX_BURST_BEATS = 1` burst, and
the round-down collapsed the plan to zero. The fix lets a single-beat master
emit a record as N separate single-beat writes.

### Secondary defect (also hardened)

A degenerate window of `base = 0 / limit = 0xFFFF_FFFF` overflowed the byte
budget: `bytes_to_limit = cfg_limit_addr - geom_addr + 1 = 0x1_0000_0000`,
truncated to 0 in 32 bits ⇒ `beats_to_limit = 0` ⇒ never flushes.

---

## Evidence (waveform, from the bridge capture test, pre-fix)

`monbus_axil_axil_group`, raw mode, AXIL master, window `0x1000..0x4FFF`,
`cfg_flush_watermark=3`:

```
beats_in_fifo            = 9        (3 completion records buffered)
beats_cap_max            = 1        <-- min(MAX_BURST_BEATS=1, 9)
beats_planned            = 1
beats_planned_units      = 0        <-- (1 / 3) * 3
do_flush                 = 1        <-- wants to flush...
r_wr_state               = WR_IDLE  <-- ...but guard needs units >= 3, stuck
m_mon_axil_wvalid        = (never asserted)
```

Post-fix: the same test captures 9 `m_mon_axil_w` beats (3 records × 3 beats).

---

## How the existing `val/amba` tests missed it

| Test | What it covers | Why it missed the bug |
|---|---|---|
| `val/amba/test_monbus_axil_axil_group.py` | AXIL/AXIL: monbus input, **slave-read** error-FIFO drain, packet flow into the FIFO | **Explicitly skips master-write assertions** (header lines 23–25: *"lets the master-write side flush into a synthetic sink inside the TB (no master-write assertions in this minimal test; see the dedicated AXIL/AXI4 burst test for master-write coverage)."*). Never checks beats leave `m_axil_w*`. |
| `val/amba/test_monbus_axil_axil_group_compressed.py` | AXIL/AXIL with `USE_COMPRESSION=1` | `BEATS_PER_UNIT = 1`, so the rounding-to-zero path is never exercised. |
| `val/amba/test_monbus_axil_axi4_group.py` | AXIL slave / **AXI4** master bursts | Master is AXI4 with `MAX_BURST_BEATS = 64 >= 3`; the single-beat-master case is never hit. |
| *(none)* | `monbus_axi4_axil_group` | **No test exists** for this member; its AXIL master shares the broken path. |

### The gap, precisely

There was **no test asserting non-zero master-write output for an AXIL master
in raw mode** (`MAX_BURST_BEATS = 1`, `USE_COMPRESSION = 0`,
`BEATS_PER_UNIT = 3`). The AXIL/AXIL test delegated master-write coverage to
"the dedicated AXIL/AXI4 burst test," but that test uses an **AXI4** master —
a different `MAX_BURST_BEATS`, the exact variable that triggers the bug. So the
master-write assertion existed only for the configuration that cannot reproduce
the defect, and the configuration that could had its master-write side wired to
an unchecked synthetic sink. The bridge `test_bridge_1x2_rd_monitor_capture.py`
is the first test to **assert** beats on an AXIL master's write port in raw
mode, which is why it caught it.

---

## Recommended test additions (to keep the gap closed)

- Add a **master-write assertion** to `val/amba/test_monbus_axil_axil_group.py`
  (raw mode): drive packets, then assert ≥ `3*N` beats on `m_axil_w*` with the
  3-beats-per-record cadence (mirror the bridge capture test's snoop-and-count).
- Add `val/amba/test_monbus_axi4_axil_group.py` covering the AXI4-slave /
  AXIL-master member, including its master-write path.
- Add a raw-mode (single-beat-master) case to the "dedicated burst test" the
  AXIL/AXIL header refers to, so `MAX_BURST_BEATS = 1` × `BEATS_PER_UNIT = 3`
  is exercised directly at the module level.

---

## Key file references

- `rtl/amba/shared/monbus_group_core.sv` — `BEATS_PER_UNIT`, byte→beat budget
  (`bytes_to_limit` overflow), `beats_cap_max` / `beats_planned`,
  round-down-to-unit, `WR_IDLE → WR_AW` guard.
- `rtl/amba/shared/monbus_axil_axil_group.sv` / `monbus_axi4_axil_group.sv` —
  `.MAX_BURST_BEATS(1)`.
- `val/amba/test_monbus_axil_axil_group.py:23-25` — "no master-write assertions".
- `projects/components/bridge/dv/tests/test_bridge_1x2_rd_monitor_capture.py` — repro.
