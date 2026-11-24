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

**Status:** as built 2026-11-23 (onyx TASK-001 step 7; D1 decided 2026-11-20, PRD v0.7). The RTL is `onyx_ccu`'s `io_*` port, requester `N_PORTS` of the transaction table.

## What D1 asked for

One ACE-Lite IO port beside the N cache ports and the memory master: a non-caching master (a DMA, an IO bridge, a host) that wants coherent *access* without being snooped. ACE-Lite is AXI4 plus the ACE address fields (`AxSNOOP`, `AxDOMAIN`, `AxBAR`) and nothing on the snoop side (IHI 0022 D11): the IO never receives AC and never drives CR or CD. The in-repo [ACE interface definition](../../../../References/AMBA_ACE_Interface_Definition.md) section 5 is the contract.

## The port, as built

`io_ar*` / `io_r*` / `io_aw*` / `io_w*` / `io_b*` with the three ACE fields on AR and AW. The IO is the table's third kind of requester (index `N_PORTS`; the observer's TXN_START and LOCK_WAIT carry it as such), takes the per-line lock like a cache, and is served by the same slots, snoop queues, replay engines and write port. What differs per kind:

| Kind | Decode | Slot | Snoop | Data path | Done |
|---|---|---|---|---|---|
| ReadOnce | `ARDOMAIN` inner or outer shareable, `ARSNOOP` 0 | yes | AC to **every** cache, `ACSNOOP` ReadOnce (`4'h0`) | a peer's DataTransfer: the requested beats replayed from the IO's own line buffer (from the AR's offset, `ARLEN+1` beats); none: the memory read per the D6 mode, the IO's own AR fields on the memory AR, the beats forwarded | the IO's RLAST |
| ReadNoSnoop | `ARDOMAIN` non-shareable or system | yes, no peers | none | the memory read, the IO's AR as issued (any legal AXI burst) | RLAST |
| WriteUnique / WriteLineUnique | `AWDOMAIN` shareable, `AWSNOOP` 0 / 1 | yes, no read | AC to every cache, `ACSNOOP` CleanInvalid (`4'h9`) | the IO's AW is held unaccepted while the slot gathers and any PassDirty line is absorbed; then AW / W / B pass the write port with the IO's own fields and strobes | the IO's BRESP |
| WriteNoSnoop | `AWDOMAIN` non-shareable or system | no | none | the write port, as a cache write-back (the same hold against an incomplete gather or pending absorption on its line) | BRESP |

: Table 4.5: The IO port's transaction kinds

**Why ReadOnce passes dirty.** The house snoop table (l1_pkg Table 3.0) answers ReadOnce from a Modified line with DataTransfer and PassDirty and invalidates the holder: the dirty line's responsibility moves to the manager, which absorbs it to memory exactly as it does for a cache's fill. From Exclusive the holder supplies clean and downgrades to Shared; from Shared the memory supplies. The IO master keeps no copy, so nothing further is owed.

**Why WriteUnique snoops CleanInvalid, not MakeInvalid.** A MakeInvalid snoop may not carry data (IHI 0022), so a Modified holder's bytes would be lost under a partial write. CleanInvalid makes the holder pass the line dirty and invalidate; onyx absorbs the line, then the IO's bytes land on top. WriteLineUnique (a whole line) takes the same path; the absorption it does not need costs one memory burst.

**The write-back race.** A victim in a cache's write-back buffer that answers the IO's snoop still drains (jet-prime's buffer contract: "an invalidated snarfed victim still drains"). Its AW to the line is held while the slot gathers and absorbs; when both clear, the IO's AW and the victim's are both candidates, and the IO's must not win: the IO's AW is forwarded only when no cache presents an AW to the slot's line, so the stale victim lands first and the IO's bytes last. A victim whose AW is presented only after the IO's write has landed is the cache's hazard, not the manager's, and is recorded as such (onyx ISSUE-002).

## What the IO may issue (v1)

- One read and one write in flight at a time. The port's `ARREADY` and the write port's selection enforce it; AXI's same-ID ordering follows by construction.
- A shareable read is a full-width INCR burst within one line (the replay comes from a line buffer); a shareable write stays within one line (one line is snooped). The sim contract check in `onyx_ccu` names a violation.
- `ARSNOOP` other than ReadOnce (the cache-maintenance operations) and `AWSNOOP` other than WriteUnique / WriteLineUnique are not decoded; the sim check names them. `AxBAR` is ignored (D8).
- No retire sideband: the IO's slot retires on its last beat or its BRESP.

## Memory-side consequences

- A ReadNoSnoop's memory AR carries the IO's own address, length, size, burst, lock, QoS and region; a cache's carries the slot's line. The memory read ID is the slot either way.
- An IO write on the write port carries the IO's `AWID`; an absorption of a line the IO's snoop produced carries `8'hA0 | N_PORTS` (`A2` at two ports).
- The observer's WRITEBACK class fires for an IO write as for a cache's write-back, with the requester field `N_PORTS`; `cnt_wb` counts both ("writes taken on the write port other than absorptions").

## The gather with two peers

Every cache is a peer of the IO's transaction, so two peers can accept their ACs, or answer their CRs, for the same slot in one cycle. The slot's peer counters step by the cycle's count and the verdict ORs over the cycle's CRs; the first IO read against two sharers hung on the per-peer decrement written twice to one register. The GATHER_DONE tap is attributed to the last of the cycle's CRs for the slot. A ReadNoSnoop has no peers and hence no GATHER_DONE.

## On the reference rig

The host's hand on the port is a doorbell (`ref_io_master`): one single-beat read or write per `IO_CTRL.go`, programmed through the harness CSR (`IO_ADDR` 0x040, `IO_WDATA_LO/HI` 0x044 / 0x048, `IO_CTRL` 0x04C with `go`, `write`, `shareable`, `wstrb`, `IO_STATUS` 0x050 with `busy`, `done`, `resp`, `absent`, `IO_RDATA_LO/HI` 0x054 / 0x058). `absent` reads 1 on the selections without onyx. The `io` sequence (`jet/bin/seq_io.py`) runs after smoke: a line of its own written and read back no-snoop and ReadOnce; a line the caches hold read ReadOnce, written WriteUnique (whole and partial), read back ReadOnce and ReadNoSnoop.

## What is fixed

- The IO is requester `N_PORTS`; four kinds by `AxDOMAIN` and `AxSNOOP`; one read and one write in flight.
- ReadOnce snoops every cache with ReadOnce and absorbs a PassDirty line; WriteUnique snoops every cache with CleanInvalid, absorbs, then writes.
- The IO's WriteUnique waits for any cache's presented write-back to its line.

## What is open

- Several IO masters, or several outstanding accesses per master (the port is one master, one access per direction).
- The cache-maintenance snoops an ACE-Lite master may issue (CleanShared, CleanInvalid, MakeInvalid on AR).
- Narrow shareable reads (lane steering out of the line buffer).
