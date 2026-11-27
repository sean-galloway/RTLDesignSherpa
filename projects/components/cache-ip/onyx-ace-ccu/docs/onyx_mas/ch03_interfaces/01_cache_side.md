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

# Cache-Side Port Timing

The cache side of `onyx_ccu` is three groups per port: the D-8 sideband,
the cache's AXI4 memory side (AR/R, AW/W/B), and the snoop port
(Chapter 3.2). The IO port's AR/R and AW/W/B behave as a cache's on the
same paths (differences in ch02/07). The handshake rules are AXI's
(`vault/handbook/design/valid-ready-contracts.md`): VALID never waits for
READY; READY may wait for VALID.

## Timing class per signal

| Signal | Class | Source |
|---|---|---|
| `c_arready[d]`, `io_arready` | flopped | `r_arw_vld` |
| `c_rvalid`, `c_rdata`, `c_rlast`, `c_rresp`, `c_ruser`, `c_rid` (and `io_r*`) | comb | the R select over the memory R inputs (same cycle) and the buffer's asynchronous read (ch02/05) |
| `c_awready`, `c_wready` (and `io_awready`, `io_wready`) | comb | `mem_awready` / `mem_wready`, gated by `r_wstate` and the selection |
| `c_bvalid`, `c_bid`, `c_bresp`, `c_buser` (and `io_b*`) | comb | `mem_b*`, gated likewise; `c_bid` etc. are broadcast, `c_bvalid` qualifies |
| `c_coh_req_*` | sampled | combinational into the candidate, the lock compare and the grant in the pulse's cycle |
| `c_coh_done_*` | sampled | combinational into the retire compare, registered as `r_rack` |

: Table 3.1: Cache-side timing classes

Two combinational paths cross onyx end to end, by design, and a rig that
closes timing at its clock has to carry them:

- **memory R to cache R:** `mem_rvalid` / `mem_rid` / `mem_rdata` through
  the router and the R select to `c_rvalid` / `c_rdata`, and `c_rready`
  back to `mem_rready`;
- **cache AW / W / B to memory:** the selected writer's channels to
  `mem_aw*` / `mem_w*`, and `mem_awready` / `mem_wready` / `mem_bvalid`
  back to the writer.

Neither has a register stage in v1. The Genesys2 reference rig builds them
at 100 MHz; where TASK-001 names the worst path of a build, it is
jet-prime's fill staging, not onyx.

## The sideband against the AR

The pulse precedes the AR. A pulse granted in cycle *t* arms `ARREADY` in
*t+1*; an AR presented earlier simply waits. A cache that presents its AR
before its pulse is still correct: the AR waits until a grant arms it.
What a cache must not do is present the ARs of two launches out of their
pulse order; the pairing is positional (ch02/01).

## R channel behavior

- RID is always the requester's own `ARID` (from the slot).
- Beats of two of a cache's slots may interleave (one forwarded from memory,
  one replayed, at most one per cycle); each slot's beats are in order.
  AXI4 permits interleaving across IDs; jet-prime's fill engine demuxes by
  ID.
- An upgrade's (`ARLEN = 0`) response is one beat, data 0, RRESP OKAY,
  RLAST 1, delivered after the gather.
- A replayed line carries RRESP OKAY and RUSER 0; a forwarded memory beat
  carries the memory's RRESP and RUSER.

## Write channel behavior

- A cache write-back passes through with its own ID, address, length, size,
  burst, lock, cache, prot, QoS, region and user; its W user is dropped
  (`mem_wuser = 0`).
- Its AW is accepted only while the write port has selected it (`W_AW`);
  until then `c_awready` is low, possibly for a long time under the holds
  (ch02/06). Its W is accepted only in `W_W`, so a cache that presents W
  before AW sees `c_wready` low until its AW is taken.
- `c_bvalid[d]` rises only for the selected writer in `W_B`.
