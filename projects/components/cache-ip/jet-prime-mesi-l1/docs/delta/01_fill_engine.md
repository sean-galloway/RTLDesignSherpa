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

# jet-prime delta 01: the fill engine (TASK-001 step 2)

**Status:** landed 2026-11-15. This is the first place jet-prime's
architecture differs from jet's. jet's books
([HAS](../../../jet-mesi-l1/docs/jet_has/jet_has_index.md),
[MAS](../../../jet-mesi-l1/docs/jet_mas/jet_mas_index.md)) still describe
everything else; this chapter records only what changed and why. It is not
a copy of a jet chapter and does not restate what jet's
[ch02/06 fill and drain](../../../jet-mesi-l1/docs/jet_mas/ch02_blocks/06_fill_drain.md)
and [ch02/01 control](../../../jet-mesi-l1/docs/jet_mas/ch02_blocks/01_jet_control.md)
already say.

## What changed, in one paragraph

jet filled one line at a time: the shared `l1_fill` engine issued one AR,
waited for its eight beats, and only then could the next launch be
accepted. The MSHR file kept several misses outstanding, but after the MSHR
every fill queued behind the one in the engine. jet-prime replaces that
engine with `jet_prime_fill`: every MSHR entry owns one AXI4 read ID, so
several line fetches are on the memory port at once and their bursts come
back in whatever order the memory side returns them. `jet_prime_control`'s
launch-order completion queue, which assumed a single read ID, became a
done queue fed by the engine's per-entry completion report, and its pre-AR
snoop rule became per entry.

Measured on the reference rig (step 1, same RTL as jet, no fabric): seven
misses in flight retiring at about 15 cycles each behind one fill engine
was the remaining gap to HPDcache on the read-lean thrash. Step 2 removes
the single engine; the rig numbers are in TASK-001's progress log and the
[reference comparison](../../../docs/reference_l1_comparison.md).

## `jet_prime_fill`

`rtl/fub/jet_prime_fill.sv`. Replaces `l1_fill` in `jet_prime_coh_core`;
nothing in common-ip changed.

### Slots and IDs

| Slot | Owner | ARID | ARLEN |
|---|---|---|---|
| 0 .. MSHR_COUNT-1 | MSHR entry of that index | the index | FILL_BEATS-1 |
| MSHR_COUNT | the single outstanding CLEAN_UNIQUE upgrade | MSHR_COUNT | 0 (no data) |

A slot holds `{valid, set, way, beat counter, PassDirty, RU}` for the fill
in flight. `2**AXI_ID_WIDTH` must cover `MSHR_COUNT + 1` (elaboration
check); at the house width of 8 that is never a constraint.

### Launch seam (from `jet_prime_control`)

Start held until accept, as before, but the launch now carries the entry
index and its claimed set/way:

| Signal | Dir | Meaning |
|---|---|---|
| `fill_start_i` / `fill_addr_i` / `fill_cls_i` | in | the launch (RNSD / RU / CU) |
| `fill_idx_i` | in | the MSHR entry (ignored for a CU) |
| `fill_set_i` / `fill_way_i` | in | where the beats land (the entry's claim) |
| `fill_accept_o` | out | `start & AR register free & in-flight room & slot free` |

The AR register is free when empty or draining this cycle, so launches
accept back to back at one per cycle while the transport takes ARs.
`FILL_INFLIGHT` caps accepted-not-done fills: at 1 the engine behaves as
`l1_fill` did (the pair rig keeps it there, see below); at `MSHR_COUNT + 1`
every entry and the upgrade can be in flight together.

### Beat and completion seams (to the plane and `jet_prime_control`)

| Signal | Meaning |
|---|---|
| `fill_beat_valid_o`, `fill_beat_idx_o`, `fill_beat_num_o`, `fill_beat_set_o`, `fill_beat_way_o`, `fill_beat_data_o` | one beat, with the entry it belongs to and where it lands; the consumer (data-array W port) is always-ready for fill beats, the MAS fill > commit > hit rule |
| `fill_done_o`, `fill_done_idx_o`, `fill_done_cls_o`, `fill_done_pd_o` | pulses in the cycle the slot's last beat is presented (the same alignment `l1_fill`'s F_DONE had); a CU completes on its single no-data response |
| `fill_busy_o` | any slot in flight or an AR awaiting the transport |

R beats enter a DEPTH-4 staging queue `{slot, data, PassDirty, last}`
(DECISION D-6 kept: `rready` is the queue's `wr_ready`). Beats of different
IDs may interleave on R (AXI4 permits it); each slot's own counter gives
the beat number, so the queue head always presents the right position.

### The capture contract, with several fills in flight

The MAS rule "an entry's beats must not land before its victim is
captured" is still enforced at the launch, in the plane: the engine sees a
launch only when no capture streams and the cycle is not a dirty-victim
alloc. What is new is the argument that this is enough with other fills in
flight: allocs hold while a launch pends, so the capture that refuses a
launch is always the launching entry's own, and an earlier entry's beats
landing during a later entry's capture go to a different claimed
`(set, way)` by the claim-aware victim check. The plane's one-deep
"adapter" record is gone; set/way ride the launch and return with each
beat.

## `jet_prime_control` changes

- **Done queue, not completion queue.** jet pushed at the launch accept and
  marked entries done in launch order (single read ID). jet-prime pushes at
  `fill_done_i` with the engine's `{idx, cls, pd}` and the commit pipeline
  consumes the head. Depth is unchanged (`MSHR_COUNT + 1`): each entry
  contributes at most one completion, the upgrade one. The commit
  pipeline itself (C_MERGE .. C_RETIRE, one completion at a time) is
  untouched; response order to the CPU is still `jet_prime_rsp_seq`'s
  (J4).
- **Per-entry pre-AR.** `r_ar_done` is a bit per entry, set by the
  memory-side AR handshake decoded by its read ID (the top taps
  `m_axi_arvalid & m_axi_arready` and `m_axi_arid`), cleared at the entry's
  retire. A snoop matching an entry whose bit is clear is answered at the
  Invalid row with no effect, exactly as before; the difference is that one
  entry can be post-AR while another, queued behind it in the transport,
  is still pre-AR.
- **Launch carries the claim.** `fill_idx_o`, `fill_set_o`, `fill_way_o`
  come from the claimed-way scoreboard (held launch) or the alloc pins
  (fast path).

## Where the plane and tops changed

- `jet_prime_coh_core`: `jet_prime_fill` instance, the launch gate, the
  W-port mux fed from the engine's set/way, `fill_ar_id` input, parameter
  `FILL_INFLIGHT`.
- `jet_prime_top` / `jet_prime_ace_top`: parameter `FILL_INFLIGHT`
  (default `MSHR_COUNT + 1`), `m_axi_arid` tapped to the plane; the
  integration asserts check the accept under the cap and every beat
  landing in its entry's claimed way.
- **Pair rig at `FILL_INFLIGHT = 1`.** `jet_prime_pair_fabric`'s kill rule
  and its 4-deep request queue are argued for a single-outstanding engine
  per direction ("every fill the peer can launch is pre-AR"). Until step 3
  rebuilds the fabric, `dv/tb/jet_prime_pair_rig_tb.sv` instantiates both
  caches at one fill in flight; the reference rig (`REF_CACHE_SEL=2`), the
  core and parity tests run the engine at full depth.

## Verification that carries this step

- `test_jet_prime_fill` (new): the engine against the AXI4 slave BFM,
  in-order at gate, out-of-order completions at func, interleaved R at
  full; cells at full depth and at `FILL_INFLIGHT = 1`.
- `test_jet_prime_control`: the fill stub models the new engine (several
  fills accepted, per-entry AR, bursts served in a chosen order); new
  scenarios `fill_concurrent_ooo` and `snoop_pre_ar_per_entry`; a third
  func/full pass runs every scenario under random completion order with
  the done riding the last beat.
- Core, parity and pair-rig TBs track fills by entry index and commit in
  done order.
- `formal/jet-prime/jet_prime_control`: the environment model is the new
  engine (three slots, per-slot fairness, completion in any order); the
  liveness age bound moved from 112 to 128 cycles to admit two fills'
  bursts sharing one beat stream.
