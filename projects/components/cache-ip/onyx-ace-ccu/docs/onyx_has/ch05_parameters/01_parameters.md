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

# Build-Time Geometry

**Status:** parameters fixed 2026-11-21 with onyx TASK-001 step 2 (D4, D5 and D11 decided 2026-11-20, PRD v0.7). `onyx_ccu` takes its geometry from `l1_pkg` the way the caches do; there is no `onyx_pkg` in v1.

## Parameters of `onyx_ccu`

| Parameter | Default | Range | What it fixes |
|---|---|---|---|
| `N_PORTS` | 2 | 2 to 4 | cache-side ports; every cache-side signal is an unpacked array over it (D11) |
| `ADDR_WIDTH` | `AMBER_ADDR_WIDTH` | per `l1_pkg` | address width of every channel |
| `LINE_BYTES` | `AMBER_LINE_BYTES` | power of two | the line, and with `BUS_WIDTH` the beats per line (`FILL_BEATS`) |
| `BUS_WIDTH` | `AMBER_BUS_WIDTH` | multiple of 8 | data width of R, W and CD |
| `AXI_ID_WIDTH` | 8 | 2**width >= `SLOTS` | the memory read ID is the slot index; the requester's own ARID rides in the slot |
| `AXI_USER_WIDTH` | 1 | | user fields passed through on AR and R, zeroed on the write side |
| `SLOTS` | 18 | >= 2 | transaction table depth, shared by all ports; `N_PORTS * (MSHR_COUNT + 1)` lets every cache entry and upgrade be in flight at once (D4, D5) |
| `SNOOP_INFLIGHT` | 1 | >= 1 | ACs accepted by one cache and not yet answered; the rigs build 2 |
| `DEFER_AR` | 0 | 0 / 1 | D6 mode: 0 issues the memory read when every peer has accepted its AC, 1 only once every CR is in with no supplier |
| `SERIAL_MODE` | 0 | 0 / 1 | D5 bring-up: 1 admits one transaction system-wide |

: Table 5.1: `onyx_ccu` parameters

## Derived sizes

| Derived | Value | Note |
|---|---|---|
| `FILL_BEATS` | `LINE_BYTES * 8 / BUS_WIDTH` | 8 at the rig geometry (64-byte lines, 64-bit bus); the formal geometry uses 4 |
| `SLOT_W` | `clog2(SLOTS)` | 5 at 18 slots |
| `PORT_W` | `clog2(N_PORTS)` | 1 at two ports; the peer counters per slot are this wide |
| pending queue depth | 4 per port | the launches a cache can hold with their AR untaken (its read transport skids up to three ahead of the held AR) |
| snoop-data buffers | `N_PORTS` buffers of `SLOTS * FILL_BEATS` words | distributed RAM, one write port each, two reads (replay, absorption) |

: Table 5.2: Derived sizes

## What the rigs build

| Rig | `N_PORTS` | `SLOTS` | `SNOOP_INFLIGHT` | `DEFER_AR` |
|---|---|---|---|---|
| onyx pair rig (`dv/tb/onyx_pair_rig_tb.sv`, jet-prime's pair-rig grid) | 2 | `2 * (MSHR_COUNT + 1)` | 2 | 0 (parameter of the harness) |
| Genesys2 reference rig, `REF_CACHE_SEL` 4 | 2 | 18 | 2 | 0 |
| Genesys2 reference rig, `REF_CACHE_SEL` 5 | 2 | 18 | 2 | 1 |
| formal harness (`formal/onyx/onyx_ccu`) | 2 | 4 | 2 | 0 |
| out-of-context area row (`make ooc CACHE=onyx2`) | 2 | 18 | 2 | 0 |

: Table 5.3: Built configurations

## Not parameters in v1

The ACE-Lite IO port (D1) and the monlite observation taps (D9) are later steps of onyx TASK-001 and have no parameter yet; a directory-lite snoop filter (D3) is a future elaboration parameter and is not present.
