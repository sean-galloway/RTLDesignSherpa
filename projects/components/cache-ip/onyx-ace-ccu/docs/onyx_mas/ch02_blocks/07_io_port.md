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

# ACE-Lite IO Port

**RTL:** `onyx_ccu.sv:129-160` (header), `534-539` (domain decode),
`576-588` (IO state), `627-632` and `652-655` (candidate), `705-711`
(grant kind and peers), `1104-1118` (the write gates), `1336-1377`,
`1390-1404`, `1498-1525` (sequential), `1642-1660` (simulation contract).

The IO port is requester `IO = N_PORTS`: one non-caching master with
AXI4 plus `AxSNOOP`, `AxDOMAIN`, `AxBAR` and no snoop channels. It uses the
caches' machinery (the lock, the slots, the AC queues, its own snoop-data
buffer and replay engine, the write port) and adds only a decode, a
candidate, two busy bits and one capture register set. The kinds and their
ACE semantics are HAS Chapter 4.5; this chapter is how the RTL carries them.

## Decode

```
w_io_ar_sh = io_ardomain[0] ^ io_ardomain[1]    -- inner (01) or outer (10) shareable
w_io_aw_sh = io_awdomain[0] ^ io_awdomain[1]
```

Non-shareable (`00`) and system (`11`) are not snooped. `io_arsnoop`,
`io_awsnoop`, `io_arbar` and `io_awbar` are not decoded: the domain alone
picks the kind (`onyx_ccu.sv:1600-1602`), and the simulation checks name a
shareable read whose `ARSNOOP` is not ReadOnce or a shareable write whose
`AWSNOOP` is not WriteUnique / WriteLineUnique (`onyx_ccu.sv:1645-1660`).

## State

| Register | Meaning |
|---|---|
| `r_ior_busy`, `r_ior_slot` | an IO read holds a slot, from its grant until the slot frees |
| `r_io_araddr`, `r_io_arlen`, `r_io_arsize`, `r_io_arburst`, `r_io_arlock`, `r_io_arqos`, `r_io_arregion` | the IO read's AR, captured at its take (the memory AR and the replay read them) |
| `r_iow_busy` | an IO write is in flight: from its grant (WriteUnique) or its write-port selection (WriteNoSnoop) to its BRESP |
| `r_iow_slot_vld`, `r_iow_slot` | that write is a WriteUnique holding a slot |

: Table 2.9: IO port state

One read and one write may be in flight at once, never two of either; the
same-ID ordering AXI requires of the port then holds by construction.

## The candidate and the grant

```
w_io_rd_cand = io_arvalid & ~r_ior_busy
w_io_wr_cand = io_awvalid & w_io_aw_sh & ~r_iow_busy
w_cand_vld[IO]  = rd | wr;   address and class from the read when both
```

A read has priority over a shareable write as the IO's candidate. A
non-shareable write is never a table candidate; it goes to the write port
directly (below). The IO's candidate takes the per-line lock and the
rotating grant like a cache's (ch02/02). At the grant:

| Kind | `r_type` | Peers | `r_nodata` | `r_ar_taken` | `r_rack` | Arms |
|---|---|---|---|---|---|---|
| shareable read (ReadOnce) | 7 | `N_PORTS` | 0 | 0 | 1 | `io_arready`; `r_ior_busy` |
| non-shareable read (ReadNoSnoop) | 7 | 0 | 0 | 0 | 1 | `io_arready`; `r_ior_busy` |
| shareable write (WriteUnique / WriteLineUnique) | 5 | `N_PORTS` | 1 | 1 | 1 | `r_iow_busy`, `r_iow_slot` |

: Table 2.10: What the grant writes for the IO

## The reads

**ReadOnce.** Every cache receives `ACSNOOP` ReadOnce. The memory read
follows the D6 mode exactly as for a cache, but its AR carries the IO's own
captured address, length, size, burst, lock, QoS and region (ch02/04). If a
cache supplies the line, its CD beats land in the IO's buffer and the IO's
replay engine delivers `io_arlen + 1` beats starting at the IO address's
beat within the line (ch02/05); the memory beats are dropped. A PassDirty
supply is absorbed like a cache fill's. The v1 contract is a full-width
INCR read within one line, checked in simulation (`onyx_ccu.sv:1645-1653`);
the replay comes from a line buffer.

**ReadNoSnoop.** No peers: the slot is gathered and all-accepted at once,
nothing is pushed on any AC queue, and the memory read is a candidate as
soon as the AR is taken. Any legal AXI burst passes; the beats are
forwarded as they come.

The IO read's slot frees on its last beat (`r_rack` was set at the grant);
`r_ior_busy` clears in that cycle and the port may read again.

## The writes

**WriteUnique / WriteLineUnique.** The slot has no read and no AR to take.
Every cache receives `ACSNOOP` CleanInvalid; the IO's AW stays unaccepted
while the slot gathers and any PassDirty line is absorbed. The IO write
becomes a write-port candidate when (`onyx_ccu.sv:1109-1117`):

```
io_awvalid & w_io_aw_sh & r_iow_slot_vld
  & gathered(slot) & (~r_pd | r_abs_done)(slot)
  & no cache presents an AW to the slot's line (w_io_line_wb)
```

The last term lets a victim whose drain had started when the snoop passed
its line dirty land first: a presented AW cannot be withdrawn, and the IO's
bytes must land last. Once selected, the IO's AW, W and B pass through the
write port with its own fields and strobes; the BRESP sets `r_iow_done`,
which delivers the slot, and clears `r_iow_busy`.

**WriteNoSnoop.** `io_awvalid & ~w_io_aw_sh & ~r_iow_busy &
~w_wb_blocked_io`: the write port, held exactly as a cache write-back is
against a slot on its line that still gathers or owes an absorption. It
holds no slot; `r_iow_busy` covers it from selection to BRESP.

## On the write port and the observer

The IO write is write-port candidate `N_PORTS + 1`. An absorption of a line
the IO's snoop produced carries `AWID = IW'(8'hA0 | N_PORTS)`. The
WRITEBACK event fires for an IO write as for a cache's write-back
(`evt_wb` with `evt_wb_io`), and `cnt_wb` counts both.

`ap_io_port` in both formal harnesses states the IO's contract on the
manager side; the harness constrains the IO to the v1 contract above.
