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

# Holders, Drop-and-Count and the Mask Layers

**RTL:** `onyx_monlite.sv:191-219` (grant time, window), `303-347`
(layers), `349-411` (holders and drain), `413-488` (output queue, drop
report, `USE_MONITOR`).

`onyx_monlite` is a drop-and-count observer: it drives nothing in the
measured path, a packet the MonBus will not take is dropped and counted,
and nothing backpressures `onyx_ccu` (handbook
`design/observers-do-not-drive.md`).

## Datapath

```
evt_* taps -> admission (layers, window) -> per-instance holder, 2 deep
           -> round-robin drain, one a cycle -> gaxi_fifo_sync u_out_q (OUT_DEPTH)
           -> monbus_valid / monbus_packet / monbus_timestamp
```

**Holders.** Each of the `N_CL` class instances has a two-entry holder
(`h_cnt`, `h_d0`, `h_d1`). An admitted event is pushed into its holder if
the holder has room after this cycle's pop; an event arriving at a full
holder that is not popped in the same cycle is **lost** and counted
(`w_lost`, up to 4 bits a cycle).

**Drain.** One holder a cycle, the first non-empty instance in rotating
order from the instance after the last one taken (`r_pick_rr`). The
picked head is written into the output queue only when the queue's own
`wr_ready` is high (`w_take`); otherwise it stays in its holder. The take
is gated on the FIFO's `wr_ready`, not a shadow count: an earlier cut
lost a packet when a refused write vanished uncounted.

**Why holders.** onyx's events cluster: a grant, a gather and a memory AR
routinely land in one cycle. The caches' two-intake engine lost 9 of 66
`TXN_START` packets in the first pair-rig run with a four-deep queue and
exactly the same with a sixteen-deep one, so the intake was the limit, not
the depth (`onyx_monlite.sv:45-53`).

**Output queue.** `gaxi_fifo_sync`, `DATA_WIDTH` = packet + timestamp,
`DEPTH = OUT_DEPTH` (`MON_OUT_DEPTH` in `onyx_top`, default 16, a power of
two of at least 2). `r_eff_q` tracks its occupancy for the drop report.

## Drop-and-count

`r_dropped` is an 8-bit count of lost events, saturating at `0xFF`. It is
reported as a `PktTypeError` / `AMBER_EV_DROPPED` packet carrying the
count when it is non-zero, no event was lost this cycle, no holder is
waiting, the output queue is empty and can take a write, and the error
layer is open; the report clears the count. `dropped_count`
(`mon_dropped`) is the live count. A masked drop report leaves the count
accumulating.

## The mask layers

The house MonBus is a low-bandwidth channel
(`vault/handbook/design/monbus-is-a-low-bandwidth-channel.md`), and every
per-transaction class floods it under sustained traffic, so the
integrator picks what is transmitted. Enables are 1 = on; masks drop the
bits that are set.

```
w_perf_on = cfg_mon_enable & cfg_perf_enable & ~cfg_pkt_mask[PktTypePerf]
w_err_on  = cfg_mon_enable & cfg_error_enable & ~cfg_pkt_mask[PktTypeError]
          & ~cfg_error_mask[DROP_CODE[3:0]]
fire[c]   = event[c] & w_perf_on & ~cfg_perf_mask[code[c][3:0]]
          & ~port_masked[c] & in_window[c]
```

| Layer | Input | Notes |
|---|---|---|
| observer | `cfg_mon_enable` | 0 is silent; nothing counts as lost |
| packet type | `cfg_perf_enable`, `cfg_error_enable`, `cfg_pkt_mask[type]` | Perf for the classes, Error for the drop report |
| class | `cfg_perf_mask[code[3:0]]` | bit 0 `TXN_START`, 2 `GATHER_DONE`, 3 `MEM_READ`, 4 `READ_WASTED`, 5 `ABSORB`, 6 `WRITEBACK`, 7 `LOCK_WAIT` |
| error code | `cfg_error_mask[code[3:0]]` | bit 9 the drop report |
| requester | `cfg_port_mask[N_REQ-1:0]` | `TXN_START` by the requester, `GATHER_DONE` / `READ_WASTED` by the answering port, `LOCK_WAIT` by the waiter, `WRITEBACK` only for the IO's (a cache write-back carries no port); `MEM_READ` and `ABSORB` are never port-masked |
| content | `cfg_addr_win_enable`, `cfg_addr_win_low`, `cfg_addr_win_high` | inclusive address window; disabled = everything |

: Table 4.2: Admission layers (`onyx_monlite.sv:303-347`)

A masked or out-of-window event is dropped **at the source**: it enters
no holder and is not counted as lost. The drop report says only what the
channel lost.

## The address window

onyx attributes its events by slot, so the window is evaluated once per
transaction:

- **At the grant** the grant address is compared with the window and the
  result stored in the slot's watch bit `r_slot_watch[slot]`. In the grant
  cycle itself the live compare is used (a memory AR may be taken in the
  grant's cycle).
- `GATHER_DONE`, `READ_WASTED`, `MEM_READ` and `ABSORB` read their slot's
  watch bit; `TXN_START` uses the live compare.
- `WRITEBACK` compares its own AW address; `LOCK_WAIT` the waiting
  candidate's address, latched when the episode starts.
- The drop report is never windowed.

## USE_MONITOR

`USE_MONITOR = 0` (`gen_no_monitor`) drives `monbus_valid`,
`monbus_packet`, `monbus_timestamp` and `dropped_count` to zero and never
reads the queue.
