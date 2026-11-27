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

# onyx_top: the Wrapper

**RTL:** `rtl/top/onyx_top.sv`; filelist `rtl/filelists/onyx_top.f`.

`onyx_top` is `onyx_ccu` with its D9 observation attached:

| Instance | Module | Fed by |
|---|---|---|
| `u_ccu` | `onyx_ccu` | every port of `onyx_top` but the MonBus, observer configuration and counter ports |
| `u_mon` | `onyx_monlite` | the event taps, the grant's debug taps, `mem_arid` and `mem_awaddr`, `mon_cfg_*`, `i_mon_time` |
| `u_cnt` | `onyx_counters` | the event taps, the grant's debug taps, `dbg_slot_vld`, the caches' `c_awvalid` / `c_awready` / `c_awaddr`, `cnt_clear`, `cnt_freeze` |

: Table 2.11: `onyx_top` instances

All `onyx_ccu` parameters pass through. `onyx_top` adds `USE_MONITOR`
(default 1) and `MON_OUT_DEPTH` (default 16, the observer's output queue
depth, a power of two of at least 2).

## The wiring choices

- **The grant's port, slot and address** reach the observer from the debug
  taps (`dbg_grant_dir`, `dbg_grant_slot`, `dbg_grant_addr`), which are
  the same signals as the grant's (`onyx_ccu.sv:1583-1586`).
- **The memory read's slot** is `mem_arid[SLOT_W-1:0]`, sampled in the
  `evt_mem_ar` cycle.
- **The write-back's requester** is `N_PORTS` for an IO write and 0 for a
  cache write-back (`evt_wb_io ? N_PORTS : 0`, `onyx_top.sv:363`). A
  cache's port rides in its AW's ID bits only by the caches' convention,
  which the observer does not assume; v1 records a cache write-back with no
  port. Its address is `mem_awaddr` in the AW handshake cycle.
- **`evt_grant_cu`** for the counters is the grant class compared against
  `AMBER_ACE_CLEAN_UNIQUE`.
- **`USE_MONITOR = 0`** ties the observer's MonBus outputs to zero
  (`gen_no_monitor` in `onyx_monlite`): `mon_valid = 0`, `mon_dropped = 0`.
  The counters are not affected by it; they are present in every build.

## Who uses which top

| Consumer | Top |
|---|---|
| onyx pair rig (`dv/tb/onyx_pair_rig_tb.sv`) | `onyx_ccu` with `onyx_monlite` and `onyx_counters` beside it in the harness (the counters and a third MonBus output are exposed to the TB) |
| onyx core-alone rig (`dv/tb/onyx_core_rig_tb.sv`) | `onyx_ccu` alone |
| Genesys2 reference rig, `REF_CACHE_SEL` 4 and 5 | `onyx_top` (`projects/fpga-systems/Genesys2/cache-ip/ref/rtl/ref_harness.sv`); the counters and masks at its harness CSRs (HAS Chapter 4.4) |
| formal harnesses | `onyx_ccu` alone (flattened) |

: Table 2.12: Which top each consumer instantiates
