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

> **Status (2026-10-10): this block lives in common-ip now.** The RTL is `mc_axi4_plane`; its microarchitecture is owned by [common_mas mc_axi4_plane — AXI4 host interface and read-return ring](../../../../../common-ip/docs/common_mas/ch02_axi4_plane/01_mc_axi4_plane.md). This chapter keeps the pumice provenance and measured history; for current interfaces and parameters, read the common chapter.

# Read Return Ring (`mc_rd_return_ring`)

**Module:** `mc_rd_return_ring.sv`
**Location:** `common-ip/rtl/fub/`
**Category:** FUB
**Parent:** `mc_axi4_plane`
**Status:** Implemented

> **New block (2026-09-08).** Before it, `mc_rd_cmd_cam` held a read from
> insert all the way to R-drain and buffered the returned data per entry. That
> made the CAM's entry count the in-flight read limit, and Little's law then
> bounds read bandwidth: eight entries over a ~27-cycle DRAM round trip is
> 8 x 8 B / 27 cyc, about 180 MB/s on the board (pre-ring-fix state, 2026-09; the return-ring fix took board reads to ~572 MB/s), no matter how good the
> scheduler is.
>
> The ring splits the two jobs. The CAM entry now lives **insert -> issue
> only** and is purely a scheduling window; the ring holds the read for its
> whole DRAM round trip. In-flight capacity is `DEPTH` (32), decoupled from the
> CAM depth, which only has to be as deep as the scheduling window.

---

## Purpose

A read is given a **ticket** — a ring slot — when it is admitted, in AR order.
The CAM entry that schedules it is freed the cycle its column **issues**, and
the ticket alone follows the read through DRAM. Returns arrive in **issue**
order, because the DFI path is in order; each lands in its ticket's slot. The
ring drains from its **head in AR order** once the head's data is complete.

That gives the ordering guarantee AXI needs (per-ID reads return in request
order) without an age matrix and without an oldest-entry pick: **AR order is
the ring order**, structurally.

## Structure

FSM-free. The state is:

| Element | Role |
|---|---|
| head / tail pointers | tail allocates a ticket, head drains in AR order |
| per-slot `ready` + `resp` | is this slot's burst complete, and its RRESP |
| issue-order ticket FIFO | maps the next DFI return to the slot that issued |
| BRAM | the burst data, one slot per in-flight read |
| fetch pointer + 2-deep skid | runs ahead of head across the synchronous-read BRAM |
| per-slot `shadow` + `src` | read combining: a shadow slot drains its source slot's beats |

The prefetch skid is the same one `mc_rd_cmd_cam` uses, under the same
1-cycle BRAM read-latency contract.

## Interfaces

| Group | Direction | Purpose |
|---|---|---|
| `alloc_*` | in / out | with the CAM insert, in AR order; returns `alloc_ticket_o` (= ring tail). `alloc_ready_o` is the ring-not-full backpressure that gates AR acceptance. `alloc_merge_i` / `alloc_src_i`: this ticket is a shadow of `alloc_src_i` (read combining) |
| `issue_*` | in | from the CAM when the column issues: pushes the ticket into the issue-order FIFO |
| `dfi_ret_*` | in | the in-order DFI return stream: data, last, resp |
| `drain_*` | out | AR-order drain to `mc_rd_intake` |
| `occ_o` / `busy_o` | out | occupancy and any-in-flight, for observation |

## Read combining (pumice TASK-060)

A ticket allocated with `alloc_merge_i` is a **shadow** of an older ticket
whose read has not issued: the CAM found the same `{bank,row,col}` and took no
entry. A shadow is never pushed to the issue FIFO and never filled. It becomes
ready in the cycle its *source's* last return beat lands, and the fetch reads
its beats from the source's slot (`r_src`), so the drain hands the same burst
out twice -- source first, shadow later, both in AR order, since the shadow is
younger. The intake frames each read's own AxLEN from the beats it is given.

The source slot's data has to outlive the source's own drain, so the source is
**pinned**: the tail refuses to re-allocate a slot that an unfetched shadow
still points at (`alloc_ready_o` drops for that one slot). The pin releases
when the shadow's last beat is fetched. No deadlock: a shadow's fetch waits on
its source's return and on the R drain, neither of which waits on an
allocation. Any number of shadows may point at one source.

## Sizing

`RD_RET_DEPTH` (default 32) is the in-flight read count and therefore the read
bandwidth ceiling: sustaining 8 B/cycle across a 27-cycle round trip needs 32
in flight. It is plumbed from `pumice_core` and sizes the DFI plane's read
FIFO alongside it (`RD_FIFO_DEPTH = RD_RET_DEPTH * BURST_WORDS`). Raising the
CAM depth without raising this does nothing for read bandwidth; that is the
whole point of the split.

## Latency

Measured from the elaborated netlist (see ch01 "Pipeline Latency and Mux-Level
Schematics"):

| Path | Flops |
|---|---|
| `dfi_ret_data_i` -> `drain_data_o` | 3 |

Slot write, then the BRAM, then the skid. `alloc_ready_o`, `issue_ready_o` and
`dfi_ret_ready_o` are combinational from their respective valids — those are
timing paths, not latency.

## Verification

Directed unit test: `common-ip/dv/tests/fub/test_mc_rd_return_ring.py`
(depth 8, at 1 and 4 beats per burst). Its `pin` cell is the read-combining
hazard -- a shadow whose last beats are still unfetched in its source's slot
while the tail wants that slot; `alloc_ready_o` must stay low through the
drain stall -- and its `random` cell is a model-driven walk (shadows of
random unissued sources, issues out of order, returns in issue order, a
drain that stalls at random) checked beat by beat in AR order. Mutation
(2026-10-27): with the pin removed the walk returns the ninth read's beats
on a shadow and the directed cell sees the early allocation; both fail, so
the pin is load-bearing and the checks are live. The ring is also exercised
through `pumice_core` and `pumice_top`. The block asserts on a return with
no outstanding ticket, on an issue notify when the issue FIFO is empty, and
on a shadow whose source is not a live, unreturned, non-shadow slot — ticket
accounting breaks, caught structurally rather than by a data mismatch
downstream.
