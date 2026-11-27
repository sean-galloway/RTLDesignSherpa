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

# Top-Level Port List

**Status:** as built. `onyx_top` passes every `onyx_ccu` port through
unchanged except the event taps, which stay inside and feed the observer and
the counters; it adds the MonBus output, the observer's configuration and
the counters. Widths: `IW = AXI_ID_WIDTH`, `UW = AXI_USER_WIDTH`,
`STRB_W = BUS_WIDTH/8`, `SLOT_W = clog2(SLOTS)`, `N_REQ = N_PORTS + 1`,
`RQ_W = clog2(N_REQ)`.

Cache-side signals are **unpacked arrays over `N_PORTS`** for multi-bit
fields (`c_araddr [N_PORTS]`) and packed vectors for single-bit ones
(`c_arvalid [N_PORTS-1:0]`); a rig flattens them to per-port names
(`onyx_ccu.sv:181-184`).

## `onyx_ccu` (and `onyx_top`)

| Group | Signals | Dir | Notes |
|---|---|---|---|
| Clock / reset | `clk`, `rst_n` | in | single clock, active-low asynchronous reset (ch01/03) |
| Cache AR (per port) | `c_arid`, `c_araddr`, `c_arlen`, `c_arsize`, `c_arburst`, `c_arlock`, `c_arcache`, `c_arprot`, `c_arqos`, `c_arregion`, `c_aruser`, `c_arvalid` / `c_arready` | in / out | `c_arready` is the registered `r_arw_vld`; of the payload only `c_arid`, `c_arcache`, `c_arprot`, `c_aruser` are kept (the memory AR is regenerated from the slot) |
| Cache R (per port) | `c_rid`, `c_rdata`, `c_rresp`, `c_rlast`, `c_ruser`, `c_rvalid` / `c_rready` | out / in | memory beat or replay beat (ch02/05); `c_rid` is the requester's own `ARID` |
| Cache AW / W / B (per port) | `c_aw*`, `c_w*`, `c_b*` | in / out / out | write-back pass-through on the write port (ch02/06); `c_wuser` is not forwarded (`mem_wuser = 0`) |
| Snoop (per port) | `s_acaddr`, `s_acsnoop[3:0]`, `s_acprot[2:0]`, `s_acvalid` / `s_acready`; `s_crresp[AMBER_CRRESP_WIDTH-1:0]`, `s_crvalid` / `s_crready`; `s_cddata`, `s_cdlast`, `s_cdvalid` / `s_cdready` | out / in | the ACE-shaped port the caches carry (jet-prime's `m_axi_ac/cr/cd`); `s_acprot` is `3'b000` |
| D-8 sideband (per port) | `c_coh_req_valid`, `c_coh_req_addr`, `c_coh_req_type[2:0]`; `c_coh_done_valid`, `c_coh_done_id[IW-1:0]` | in | pulses, no ready; the class in `l1_pkg`'s `AMBER_ACE_*` code |
| IO AR / R | `io_ar*` incl. `io_arsnoop[3:0]`, `io_ardomain[1:0]`, `io_arbar[1:0]`; `io_r*` | in / out | ACE-Lite read (ch02/07); `io_arsnoop` and `io_arbar` are not decoded |
| IO AW / W / B | `io_aw*` incl. `io_awsnoop[2:0]`, `io_awdomain[1:0]`, `io_awbar[1:0]`; `io_w*`; `io_b*` | in / out | ACE-Lite write; `io_awsnoop` and `io_awbar` are not decoded |
| Memory AR / R | `mem_ar*`, `mem_r*` | out / in | `mem_arid` = slot (ch02/04) |
| Memory AW / W / B | `mem_aw*`, `mem_w*`, `mem_b*` | out / in | one burst at a time (ch02/06) |
| Debug taps | `dbg_busy`, `dbg_slot_vld[SLOTS-1:0]`, `dbg_pend_vld[N_PORTS-1:0]`, `dbg_abs_pend`, `dbg_grant`, `dbg_grant_dir[RQ_W-1:0]`, `dbg_grant_addr`, `dbg_grant_slot` | out | the pair fabric's names, read by the pair-rig testbench (ch03/04) |
| Event taps (`onyx_ccu` only) | `evt_*` | out | one-cycle pulses for the observer and the counters (ch03/04) |

: Table 1.1: `onyx_ccu` ports

## Added by `onyx_top`

| Group | Signals | Dir | Notes |
|---|---|---|---|
| MonBus | `i_mon_time` (`monbus_timestamp_t`), `mon_valid` / `mon_ready`, `mon_packet` (`monitor_packet_t`), `mon_timestamp`, `mon_dropped[7:0]` | in / out | the observer's output queue head; `mon_dropped` the saturating drop count |
| Observer configuration | `mon_cfg_enable`, `mon_cfg_perf_enable`, `mon_cfg_error_enable`, `mon_cfg_pkt_mask[15:0]`, `mon_cfg_perf_mask[15:0]`, `mon_cfg_error_mask[15:0]`, `mon_cfg_port_mask[N_REQ-1:0]`, `mon_cfg_addr_win_enable`, `mon_cfg_addr_win_low`, `mon_cfg_addr_win_high` | in | enables 1 = on, masks bit set = drop (ch04/02) |
| Counters | `cnt_clear` (pulse), `cnt_freeze` (level); `cnt_txn`, `cnt_supplied`, `cnt_mem_read`, `cnt_read_wasted`, `cnt_absorb`, `cnt_wb`, `cnt_cu_dt`, `cnt_old_wb` (32 bits each) | in / out | ch04/03 |

: Table 1.2: Ports `onyx_top` adds

## What is deliberately not here

- **No RACK / WACK** (N1): the cache side's retire is the `c_coh_done`
  sideband instead.
- **No `ARSNOOP` on the cache AR.** The caches carry the request class on
  the sideband; an `ARSNOOP`-decoding front end is the D7 adapter's second
  half, not built.
- **No snoop channels on the IO port** (ACE-Lite).
- **No register interface.** The observer's configuration and the
  counters are plain ports; the reference rig maps them to its harness CSRs
  (HAS Chapter 4.4).
