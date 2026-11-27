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

# Transaction Table, Grant and the Per-Line Lock

**RTL:** `onyx_ccu.sv:550-617` (table, gather flags, release term),
`658-711` (lock, free slot, grant), `1233-1246` (retire), `1336-1374` and
`1531-1535` (allocation and release).

## The table

`SLOTS` entries shared by all `N_REQ` requesters; the table is the point of
serialization (D5). Per slot:

| Field | Width | Set | Cleared / changed |
|---|---|---|---|
| `r_vld` | 1 | grant | release (`w_free_now`) |
| `r_dir` | `RQ_W` | grant: the requester | - |
| `r_line` | `LINE_W` | grant: the candidate's line | - |
| `r_type` | 3 | grant: the candidate's class (`ONYX_CLS_IO_READ` = 7, `ONYX_CLS_IO_WRITE` = 5 for the IO) | - |
| `r_nodata` | 1 | grant: CleanUnique / MakeUnique, or the IO's WriteUnique | - |
| `r_ar_taken` | 1 | AR take (at the grant for the IO's WriteUnique) | grant |
| `r_arid`, `r_arcache`, `r_arprot`, `r_aruser` | `IW`, 4, 3, `UW` | AR take | - |
| `r_ac_left` | `PC_W` | grant: the peer count | steps down by the cycle's AC handshakes for the slot |
| `r_cr_left` | `PC_W` | grant: the peer count | steps down by the cycle's CRs for the slot |
| `r_dt` | 1 | a CR with DataTransfer | grant |
| `r_pd` | 1 | that CR's PassDirty | grant |
| `r_mem_issued` | 1 | memory AR handshake | grant |
| `r_mem_done` | 1 | the read's RLAST consumed, or a DataTransfer before any AR was presented | grant |
| `r_rpl_done` | 1 | the replay's last beat | grant |
| `r_abs_issued` / `r_abs_done` | 1 / 1 | absorption selected / its BRESP | grant |
| `r_rack` | 1 | the requester's retire pulse names `r_arid` (set at the grant for the IO) | grant |
| `r_iow` / `r_iow_done` | 1 / 1 | grant (IO WriteUnique) / the IO write's BRESP | grant |

: Table 2.2: Transaction table fields (`onyx_ccu.sv:553-574`)

`PC_W = clog2(N_PORTS + 1)`: a peer count reaches `N_PORTS` for the IO's
shareable transactions, so the counters are one value wider than a port
index. The peer count loaded at the grant (`w_grant_npeer`,
`onyx_ccu.sv:710-711`) is `N_PORTS - 1` for a cache, `N_PORTS` for the IO's
WriteUnique or shareable read, and 0 for the IO's non-shareable read.

## The per-line lock

```
w_cand_locked[d] = SERIAL_MODE & |r_vld
                 | OR over s ( r_vld[s] & r_line[s] == line_of(w_cand_addr[d]) )
```

(`onyx_ccu.sv:660-669`). A candidate whose line any valid slot holds, from
any requester, is not granted; it stays in its pending queue (a cache) or
its AR / AW stays unaccepted (the IO), and different lines interleave.
`SERIAL_MODE = 1` locks against any valid slot: one transaction
system-wide, the D5 bring-up shape. A locked candidate drives
`evt_lock_wait[d]` every cycle it waits.

The lock is held until the slot releases, and release waits for the
requester's retire (below), so a line is locked from grant to retire, not
to the last data beat (jet-prime delta 02's argument, unchanged at N).

## Free slot and the grant

- **Free slot:** the lowest-indexed invalid slot (`w_slot_free`,
  `w_slot_idx`, `onyx_ccu.sv:672-683`).
- **Eligible:** `w_cand_ok[d] = w_cand_vld[d] & ~w_cand_locked[d] &
  w_slot_free & ~r_arw_vld[d]`.
- **Pick:** rotating priority over the `N_REQ` requesters, starting at
  `r_rr`; after a grant `r_rr` moves to one past the winner
  (`onyx_ccu.sv:695-704`, `1373`). The IO port is requester `N_PORTS` in
  the same rotation, so it neither starves the caches nor is starved.
- **One grant per cycle.** A grant writes every field of the free slot,
  arms the requester's AR (ch02/01), pushes the slot onto every peer's AC
  queue (ch02/03) and, for the IO, sets its busy state (ch02/07).

Two candidates on the same line in one cycle cannot both be granted (one
grant a cycle), and the winner's slot locks the other from the next cycle:
`ap_line_unique` (one valid slot per line) and `ap_grant_unlocked` (no
grant to a held line) are the formal statements.

## Retire and release

A cache's slot needs the cache's own retire:

```
w_rack_hit[s] = r_vld[s] & r_ar_taken[s] & ~r_rack[s] & (r_dir[s] != IO)
              & c_coh_done_valid[r_dir[s]] & (c_coh_done_id[r_dir[s]] == r_arid[s])
```

(`onyx_ccu.sv:1237-1246`). The cache's retire id is its MSHR entry (the
upgrade's is `MSHR_COUNT`), which is the `ARID` it issued, so the slot is
matched by the ID it recorded at the AR take. The IO has no retire
sideband; its `r_rack` is set at the grant and its slot retires on its
last beat or its BRESP.

The slot frees in the cycle `w_free_now[s]` holds (`onyx_ccu.sv:605-617`):

```
r_vld & gathered & delivered
      & (read not issued | read drained)
      & ~(this slot's memory AR is presented this cycle)
      & (~r_pd | absorption BRESP'd)
      & r_rack
```

with `delivered` = `r_iow_done` for the IO's WriteUnique, `r_rpl_done` for
a supplied or no-data slot, `r_mem_done` otherwise. The "AR presented this
cycle" term keeps a slot alive whose read is about to be handed over; it
was the pair fabric formal's `ap_free_complete` and is the same property
here. Any number of slots may free in one cycle, and a freed slot is
allocatable in the next.

`ap_release_after_retire` and `ap_rack_source` state the retire rules;
`ap_table_flags` states the order of the flags in a slot's life (each
implies the ones before it).

## Sizing

`SLOTS` default 18. At `N_PORTS * (MSHR_COUNT + 1)` (jet-prime's
`MSHR_COUNT` default is 8, so 18 at two ports) every cache entry and
upgrade can be in flight at once and no grant waits for a slot; the IO
port's one read and one write are not in that sum, so at 18 slots and two
ports with every cache entry live the IO waits for a slot. The table's
compare logic is `SLOTS` line comparators per requester (the lock) plus
`SLOTS` per cache write port (the write-back holds, ch02/06).
