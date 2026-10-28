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

# jet_control: Lookup/Commit Pipeline

**Status:** planned contract. `jet_control` replaces amber's blocking
`l1_control` FSM as the cache's control core. The arrays, replacement
engine, and snoop responder it drives are the unchanged `l1_*` FUBs.

## The split

Amber serializes everything through one FSM (LOOKUP → HIT_*/MISS_* → REPLAY
per transaction). jet splits control into two concurrent halves:

- **Lookup stage** — one request at a time: tag+state read on port A and
  the MSHR CAM match in the same window (the PoS, ch01). Outcome classes:
  `HIT`, `MISS_ALLOC`, `MERGE`, `STALL`.
- **Commit pipeline** — one fill completion at a time: merged store data
  written (amber D-4 write-merge at commit), tag install, MSHR retire,
  response handoff to `jet_rsp_seq`.

The two halves meet only through the arrays' write port (arbitrated, below)
and the MSHR file. Amber's global FSM states map onto per-entry progress:
each MSHR entry independently walks {allocated → fill launched → beats
landing → committing}; there is no global MISS_VICTIM/MISS_FILL state.

## Lookup classify (one request, one window)

Inputs: tag/state lookup (port A), MSHR CAM match, WB-buffer match, the
set's outstanding-victim-way claim count, and the oracle-equivalent state
decode from `l1_pkg`.

| Class | Condition | Action |
|---|---|---|
| HIT | line resident (S/E/M), no pending-fill hazard | serve from port A; write hits take the W port subject to fill-beat priority (J2); responses release in order |
| MERGE | line not resident, MSHR match, same class | append the request's sequence tag to the entry's merge list; no new traffic |
| MISS_ALLOC | line not resident, no MSHR match, resources free | allocate MSHR entry; claim victim way from `l1_repl`; if victim dirty, capture to WB buffer (J5); launch fill |
| STALL | MSHR full; or WB full AND dirty victim; or set oversubscribed (WAYS outstanding in this set); or cross-class wait (write miss behind a read fill, J3) | hold the request at the front end; retried next cycle |

The STALL classes are the whole congestion story (J6): they never drop a
request, and each has a bounded release condition (an entry retires, a
drain completes, a fill commits).

## Commit pipeline

On `fill_done` for entry E (fill engine order = alloc order, single AXI4
read ID):

1. **Merge store data.** If E's requester (or any merged requester) is a
   write, its byte-enable merge lands on the just-filled beats (D-4
   semantics, identical to amber's).
2. **Install the tag** with E's install state — S, or M when PassDirty was
   received (amber's #106 rule), or M for a write fill.
3. **Apply deferred snoop effects.** Any snoop that hit E's pending entry
   recorded its post-commit effect (downgrade to S / invalidate to I) in
   the entry; it applies now, ordered after the install (amber's
   `pending` semantics from the gem5-derived oracle).
4. **Retire E** and hand the response data to `jet_rsp_seq` for every
   sequence tag on E's merge list.

## The anti-livelock hold-off (J4/Chinnakonda §10.9)

When an upgrade (CLEAN_UNIQUE) for line L completes, `jet_control` holds
off snoop service to L until the granted write's commit lands — a fixed,
small number of cycles, guaranteed by construction (the commit needs only
the W port for one beat and the tag port for one write). The hold-off never
extends past that commit; §8.2's "temporary block" permission is the whole
license, and ch05/01 carries the bounded-window formal property.

## Illegal states

The sticky CTRL_ERROR contract is inherited: a reserved state encoding or
an unreachable transition drops the pipeline to ERROR, exactly as amber's
(the DV illegal-state scenario pins it).

## W-port arbitration

One write port feeds: fill beats (fill engine), hit/merged store data
(port A writes), WB capture reads are on port B. Priority: **fill beats >
write hits** (J2): a fill once in its beat stream finishes it (bounded:
FILL_BEATS cycles), then write hits proceed. This is the liveness-safe
order — fills retiring is what frees MSHR entries.

## Interface sketch (planned)

| Signal group | Dir | Content |
|---|---|---|
| `lkup_*` | in | request from the front end (addr, we, be, wdata, seq tag) |
| `lkup_rsp_*` | out | hit data / accept-stall to the front end |
| `tag_*` / `dat_*` | out/in | array port A drive/read |
| `repl_*` | out/in | victim request/way from `l1_repl` |
| `mshr_*` | out/in | alloc/match/retire to `jet_mshr` |
| `wb_*` | out/in | capture/drain-status to `jet_wb_buffer` |
| `fill_*` / `drain_*` | out/in | engine launch/done |
| `cpl_*` | out | completions to `jet_rsp_seq` (seq tag, data) |
| `sn_*` | in/out | snoop service interface from `l1_snoop_resp` |
| `mon_*` | out | MonBus event taps (ch04) |
