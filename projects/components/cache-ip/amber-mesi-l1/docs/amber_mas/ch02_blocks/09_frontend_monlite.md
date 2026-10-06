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

# amber_cpu_frontend and amber_monlite

**Modules:** `amber_cpu_frontend.sv`, `amber_monlite.sv`
**Location:** `projects/components/cache-ip/amber-mesi-l1/rtl/fub/`
**Status:** Pre-RTL micro-architecture contract

---

## amber_cpu_frontend

### Purpose

`amber_cpu_frontend` is the GAXI slave that accepts CPU requests and returns responses. Because the cache is blocking, it latches one request at a time and does not accept a new request until `amber_control` returns `req_ready`.

### Request payload

```systemverilog
CPU_REQ_W = ADDR_WIDTH + 1 + BUS_WIDTH/8 + BUS_WIDTH
```

Packed as `{addr[ADDR_WIDTH-1:0], we, be[BUS_WIDTH/8-1:0], wdata[BUS_WIDTH-1:0]}`.

### Response payload

```systemverilog
CPU_RSP_W = BUS_WIDTH
```

Packed as `{rdata[BUS_WIDTH-1:0]}`.

### Handshake

| Signal | Direction | Meaning |
|--------|-----------|---------|
| `cpu_req_wr_valid` | input | CPU has a request. |
| `cpu_req_wr_ready` | output | Frontend accepts request this cycle. |
| `cpu_req_wr_data` | input | Request payload. |
| `cpu_rsp_rd_valid` | output | Response ready. |
| `cpu_rsp_rd_ready` | input | CPU accepts response. |
| `cpu_rsp_rd_data` | output | Response payload. |

`cpu_req_wr_ready` is asserted only when `amber_control` is in `CTRL_IDLE` and no snoop priority stall is active. Once a request is accepted, the front end latches it and holds it until `amber_control` returns the response.

### Replay path

On a miss, `amber_control` re-drives the original latched request into its own hit logic in `CTRL_REPLAY`. The front end does not see a new GAXI transaction; the response is generated from the same latched request.

---

## amber_monlite

### Purpose

`amber_monlite` is the drop-and-count MonBus observer. It taps the internal signals of `amber_core` and emits 128-bit MonBus event packets. It never stalls the observed path; under sustained backpressure it drops packets and counts the loss.

### Observation points

| Event | Emit point | Payload highlights |
|-------|------------|--------------------|
| hit | `CTRL_HIT_RD` / `CTRL_HIT_WR` | set, way, old/new state |
| miss | `CTRL_MISS_VICTIM` | set, way, miss class |
| snoop | snoop accepted | snoop type, hit/miss, response class |
| eviction | `CTRL_MISS_VICTIM` dirty victim | clean/dirty, set, way |
| MESI transition | state update | old state, new state, cause |
| fill start | `CTRL_MISS_FILL` | address, direction |
| fill end | `CTRL_FILL_WRITE` | address |
| drain start | `CTRL_MISS_DRAIN` | address |
| drain end | drain done | address |

### Packet format

Standard MonBus 128-bit packet with house UNIT/AGENT ids. The exact field layout follows the shared `monitor_common_pkg` spec; the MAS does not invent a new layout.

### Drop-and-count

If `mon_ready` is low when a packet is ready, the packet is dropped and a saturating drop counter increments. The drop count is reported as an `EVENT_DROPPED` packet when the bus next has room, exactly like the STREAM monitor-lite behavior.

---

**Last Updated:** 2026-10-06
