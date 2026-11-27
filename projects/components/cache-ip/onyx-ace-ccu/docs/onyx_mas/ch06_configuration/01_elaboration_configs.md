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

# Elaboration Parameters and Built Configurations

## `onyx_ccu` parameters

| Parameter | Default | Legal range (elaboration check) | Effect on the micro-architecture |
|---|---|---|---|
| `N_PORTS` | 2 | 2 to 4 (`onyx_ccu.sv:460`) | number of cache ports; `N_REQ = N_PORTS + 1` requesters; AC / in-flight queues per cache; buffers and replay engines per requester; write-port candidates `N_PORTS + 2` |
| `ADDR_WIDTH` | `AMBER_ADDR_WIDTH` (32) | - | every address; `LINE_W = ADDR_WIDTH - OFFSET_W` line comparators |
| `LINE_BYTES` | `AMBER_LINE_BYTES` (64) | power of two (`:462`) | the line; with `BUS_WIDTH`, `FILL_BEATS` |
| `BUS_WIDTH` | `AMBER_BUS_WIDTH` (64) | multiple of 8 (`:466`); `FILL_BEATS` a power of two of at least 2 (`:464`) | R, W and CD width; buffer word width |
| `AXI_ID_WIDTH` | 8 | `2**AXI_ID_WIDTH >= SLOTS` (`:470`) | the memory read ID is the slot index |
| `AXI_USER_WIDTH` | 1 | - | AR and R user carried; write-side user zeroed |
| `SLOTS` | 18 | at least 2 (`:468`) | table depth; AC queue depth per cache; buffer rows `SLOTS * FILL_BEATS`; the lock's comparator count |
| `SNOOP_INFLIGHT` | 1 | at least 1 (`:472`) | ACs a cache may hold unanswered; the in-flight queue depth |
| `DEFER_AR` | 0 | 0 / 1 | the memory-AR trigger: every AC accepted (0) or every CR in with no supplier (1) |
| `SERIAL_MODE` | 0 | 0 / 1 | 1 locks every candidate while any slot is valid (one transaction system-wide) |

: Table 6.1: `onyx_ccu` parameters (the `l1_pkg` defaults in parentheses)

Fixed localparams: `PEND_DEPTH = 4` (pending queue per cache).

## `onyx_top` adds

| Parameter | Default | Range | Effect |
|---|---|---|---|
| `USE_MONITOR` | 1 | 0 / 1 | 0 ties the MonBus outputs off; the counters stay |
| `MON_OUT_DEPTH` | 16 | power of two, at least 2 (`onyx_monlite.sv:187`) | the observer's output queue depth |

: Table 6.2: `onyx_top` parameters

`onyx_monlite` also takes `AGENT_ID`, `UNIT_ID` and `DROP_CODE`, which
`onyx_top` leaves at the `onyx_pkg` / `l1_pkg` defaults.

## Built configurations

| Consumer | `N_PORTS` | `SLOTS` | `SNOOP_INFLIGHT` | `DEFER_AR` |
|---|---|---|---|---|
| formal, `formal/onyx/onyx_ccu` | 2 | 4 | 2 | 0 |
| formal, `formal/onyx/onyx_ccu_n3` / `_n4` | 3 / 4 | 4 | 2 | 0 |
| pair rig, core-alone rig, reference rig | see HAS Table 5.3 and the test files | | | |

: Table 6.3: Built configurations

## Not parameters

- The IO port is always present; a rig that does not use it ties
  `io_arvalid` and `io_awvalid` low (the core-alone rig does).
- No directory or snoop filter (D3, future).
- No `ARSNOOP` front end.
