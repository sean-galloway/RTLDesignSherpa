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

# Snoop Fanout and Response Gather

**RTL:** `onyx_ccu.sv:476-505` (snoop map), `721-788` (queues, per-slot
steps, AC drive), `790-818` (CD write pick), `1406-1449` (sequential).

## Snoop map

`s_acsnoop[p] = map_snoop(r_type[slot])` (`onyx_ccu.sv:490-500`):

| Slot class (`r_type`) | `ACSNOOP` |
|---|---|
| `READ_SHARED`, `READ_NOT_SHARED_DIRTY` | `4'h1` ReadShared |
| `READ_UNIQUE` | `4'h7` ReadUnique |
| `CLEAN_UNIQUE` | `4'h9` CleanInvalid (onyx BUG-001: a killed upgrade's peer may hold the line dirty) |
| IO read (`ONYX_CLS_IO_READ`) | `4'h0` ReadOnce |
| IO write (`ONYX_CLS_IO_WRITE`) | `4'h9` CleanInvalid (dirty data first) |
| anything else (`MAKE_UNIQUE`) | `4'hC` MakeInvalid |

: Table 2.3: Slot class to ACSNOOP

`s_acaddr[p]` is the slot's line, line-aligned; `s_acprot[p]` is `3'b000`.

## Per-peer state

| State | Shape | Content |
|---|---|---|
| `r_snq[p]` / `r_snq_cnt[p]` | shift queue, `SLOTS` deep, count `SLOT_W+1` bits | slots owed an AC by peer `p`, in grant order |
| `r_sni[p]` / `r_sni_cnt[p]` | shift queue, `SNOOP_INFLIGHT` deep | slots whose AC `p` accepted and has not answered, in AC order |
| `r_cd_beat[p]` | `BEAT_INDEX_WIDTH` | the beat index of `p`'s next CD beat |

: Table 2.4: Fanout and gather state per peer

`r_snq` is `SLOTS` deep because at most `SLOTS` slots are valid; it cannot
overflow (`ap_snq_count`).

## Fanout

A grant with a non-zero peer count pushes the new slot onto the AC queue of
**every** cache except the requester (`push_q`, `onyx_ccu.sv:1411`; for the
IO the requester index is `N_PORTS`, so every cache is pushed). The push and
an AC handshake in the same cycle: the queue shifts first and the push lands
on the freed tail.

Peer `p` presents its queue head while it has room in flight:

```
s_acvalid[p] = (r_snq_cnt[p] != 0) & (r_sni_cnt[p] < SNOOP_INFLIGHT)
```

The head and its slot's line and class are registers, so the AC payload is
stable from presentation to handshake (`ap_ac_stable`). On the handshake
the head moves from `r_snq[p]` to the tail of `r_sni[p]`, and the slot's
`r_ac_left` steps down.

## Gather

`s_crready[p] = (r_sni_cnt[p] != 0)`: a CR is accepted whenever a snoop is
outstanding at that peer, and it belongs to the in-flight head
`w_sni_head[p]`. On the handshake:

- the head pops from `r_sni[p]`;
- the slot's `r_cr_left` steps down;
- with `CRRESP[DataTransfer]`, the slot's `r_dt` sets and `r_pd` takes
  `CRRESP[PassDirty]`; and if the slot's memory read is neither issued nor
  presented in this cycle, `r_mem_done` sets, so the read is never issued
  (a presented AR is held and issues; its beats are then dropped, ch02/04);
- `r_cd_beat[p]` resets to 0 (CD before CR: the slot's CD beats are in).

**Same-slot steps.** `w_ac_dec[s]` and `w_cr_dec[s]` count the cycle's
handshakes for slot `s` over all peers, and the counters subtract the count;
`w_cr_dt_now` / `w_cr_pd_now` OR the cycle's CRs for the event taps
(`onyx_ccu.sv:745-777`). `w_cr_last[p]` marks the highest-indexed peer
answering a given slot in the cycle, so a gather completed by two peers at
once reports once.

**Single supplier.** Under MESI at most one peer holds a line Exclusive or
Modified, so at most one CR per slot carries DataTransfer. A second is a
simulation error (`onyx_ccu.sv:1635-1638`); in the RTL the
highest-indexed answering peer's PassDirty would win.

`w_gathered[s] = (r_cr_left[s] == 0)` and `w_ac_all[s] = (r_ac_left[s] ==
0)` sit in their own `always_comb` (`onyx_ccu.sv:599-604`): the release
term reads the presented memory AR, whose candidate reads these flags, and
one block for both looked like a combinational cycle to the scheduler.

## CD write pick (one per snoop-data buffer)

Peer `p`'s CD beat targets the buffer of the requester of its in-flight
head: `w_cd_tgt[p] = r_dir[w_sni_head[p]]`. Each buffer has one write port,
so for each buffer `a` the pick takes one peer per cycle among those with
`s_cdvalid` and an outstanding snoop targeting `a`, by rotating priority
from `r_cd_rr[a]`; the pointer moves one past the writer
(`onyx_ccu.sv:795-818`, `1446-1449`).

```
s_cdready[p] = cdvalid & outstanding & (p is buffer w_cd_tgt[p]'s pick)
```

`CDREADY` therefore depends on `CDVALID`, which AXI permits (READY may wait
for VALID). Two peers contend for one buffer only when they supply two
different slots of the same requester in the same cycle, which needs at
least three caches, or the IO with two suppliers; at `N_PORTS = 2` each
cache is the only writer of the other's buffer and the pick never refuses.

The beat lands at `{w_sni_head[p], r_cd_beat[p]}` (ch02/05); `r_cd_beat[p]`
increments per beat and returns to 0 after `CDLAST`.

## What the harnesses state here

`ap_ac_legal` (an AC names a valid slot of another requester that owes that
peer an AC not yet accepted, with the slot's line and its class's snoop),
`ap_ac_stable`, `ap_sn_count` (each peer's outstanding count exact and
bounded, CR taken whenever one is outstanding), `ap_cd_slot` (a CD beat
lands in a live slot of another requester awaiting its verdict), and at
N = 3 and 4 the per-peer shadow properties `ap_peer_shadow`, `ap_cr_slot`
and `ap_snq_count`.
