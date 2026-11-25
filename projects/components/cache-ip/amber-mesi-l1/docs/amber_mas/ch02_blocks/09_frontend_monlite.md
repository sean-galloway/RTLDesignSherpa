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

# l1_cpu_frontend and l1_monlite

**Modules:** `l1_cpu_frontend.sv`, `l1_monlite.sv`
**Location:** `projects/components/cache-ip/common-ip/rtl/fub/`
**Status:** RTL landed; this chapter is the micro-architecture contract the RTL implements.

---

## l1_cpu_frontend

### Purpose

`l1_cpu_frontend` is the GAXI slave that accepts CPU requests and returns responses. It passes the request to `l1_control` in the handshake cycle (control latches it) and does not accept a new request until `l1_control` returns `req_ready`.

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

`cpu_req_wr_ready` is `ctrl_req_ready` (`CTRL_IDLE`, or `CTRL_HIT_RD` within the back-to-back run) AND room in the depth-2 response FIFO: while `l1_control`'s response is up the FIFO must be empty (that response and the new request's may both need an entry), otherwise one free entry.

`RSP_BYPASS` (amber sets 1 in `l1_cpu_plane`; jet and jet-prime keep the default 0): the response is presented in the cycle `l1_control` makes it -- `cpu_rsp_rd_valid` is the FIFO's not-empty OR `ctrl_rsp_valid`, the payload the FIFO head when it holds anything, else `ctrl_rsp_data` -- and goes into the FIFO only if not taken that cycle. With 0 every response passes through the FIFO, a cycle later, as before.

`MAINT_EN` (amber TASK-004; default 0 everywhere, set by `amber_top` / `amber_ace_top`'s `MAINT_EN` parameter): the request word carries the clean-all bit above `addr`, `{maint, addr, we, be, wdata}`, and the frontend passes it to `l1_control` as `req_maint`. With 0 the packing is the classic one and `req_maint` is 0 (ch03/01 Table 3.1.2).

The observer reports a clean-all write-back as DRAIN_START / DRAIN_END and its M-to-E commit as a TRANSITION (cause 7, other); it is not an EVICT (`l1_coh_core` gates the victim-load tap with `ctrl_drain_clean`).

### Replay path

On a miss, `l1_control` re-drives the original latched request into its own hit logic in `CTRL_REPLAY`. The front end does not see a new GAXI transaction; the response is generated from the same latched request.

---

## l1_monlite

### Purpose

`l1_monlite` is the drop-and-count MonBus observer. It taps the internal signals of `l1_core` and emits 128-bit MonBus event packets. It never stalls the observed path; under sustained backpressure it drops packets and counts the loss.

### Observation points

| Event | Emit point | Payload highlights |
|-------|------------|--------------------|
| hit | `CTRL_HIT_RD` / `CTRL_HIT_WR` entry, or a `CTRL_HIT_RD` entered from `CTRL_HIT_RD` (`tap_hit_again`, a back-to-back hit) | set (the latched request's), way, old/new state |
| miss | `CTRL_MISS_VICTIM` | set, way, miss class |
| snoop | snoop accepted | snoop type, hit/miss, response class |
| eviction | `CTRL_MISS_VICTIM` dirty victim | clean/dirty, set, way |
| MESI transition | state update | old state, new state, cause |
| fill start | `CTRL_MISS_FILL` | address, direction |
| fill end | `CTRL_FILL_WRITE` | address |
| drain start | `CTRL_MISS_DRAIN` | address |
| drain end | drain done | address |

### Packet format

Standard MonBus 128-bit packet with house UNIT/AGENT ids. The exact field layout follows the shared `ocelus_common_pkg` spec; the MAS does not invent a new layout.

### Drop-and-count

If `mon_ready` is low when a packet is ready, the packet is dropped and a saturating drop counter increments. The drop count is reported as an `EVENT_DROPPED` packet when the bus next has room, exactly like the STREAM monitor-lite behavior.

---

**Last Updated:** 2026-10-06
