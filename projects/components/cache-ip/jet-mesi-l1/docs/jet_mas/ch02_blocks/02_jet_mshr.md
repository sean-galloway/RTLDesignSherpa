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

# jet_mshr: the MAB File

**Status:** planned contract. jet's MSHR file is a **MAB** (miss address
buffer) in Chinnakonda's terms: it holds no line data; fill beats write the
data array directly (the small-area scheme, §9.10.2).

## Organization (J1)

Fully associative CAM keyed by line address; `MSHR_COUNT` entries,
elaboration parameter 2–16, default 8 (sized by the §9.10.4 occupancy
formula against the pair rig's memory latency; the 2/4/8/16 sweep is the
J7 experiment).

## Entry format

| Field | Width | Content |
|---|---|---|
| `valid` | 1 | entry allocated |
| `line` | LINE bits | miss line address (the CAM key) |
| `cls` | 2 | fill class: RNSD (read miss) / RU (write miss); CLEAN_UNIQUE upgrades carry no fill and do not allocate |
| `install_state` | 1 | S vs M at commit (M when write fill or PassDirty expected) |
| `victim_way` | WAY bits | the way claimed at alloc (the set-oversubscription claim) |
| `wb_slot` | VICTIM_DEPTH bits + valid | WB-buffer slot holding the dirty victim, if any |
| `merge` | MSHR_COUNT-deep tag list | sequence tags of requesters waiting on this fill (the first is the allocator's) |
| `beats_rcvd` | FILL_BEATS bits | which fill beats have landed (the PF_GUARD "can deliver" test for the snoop bypass) |
| `pend_eff` | 2 | deferred post-commit snoop effect: none / downgrade-S / invalidate-I |
| `seq` | order bit | alloc age, for oldest-entry selection |

## Operations

- `match(line)` — CAM probe; used by lookup classify (merge?), by the snoop
  hazard compare (pending-fill?), and by the set-oversubscription counter
  (per-set valid-entry count).
- `alloc(...)` — first free entry; stalls when none (`mshr_full`).
- `merge(idx, seq_tag)` — append a requester to the merge list.
- `beat(idx, beat_no)` — mark a fill beat landed (drives PF_GUARD).
- `retire(idx)` — on commit; frees the entry, the victim-way claim, and
  (through `wb_slot`) marks the WB entry drainable-orphan if not already
  drained.

## Hazard rules carried by this block

- **Set oversubscription (§9.10.2):** a set with WAYS outstanding victim
  claims refuses further allocs to that set until one commits. The claim
  count is a per-set counter bank next to the CAM (SETS counters, 2 bits at
  4 ways).
- **Cross-class wait (J3):** a write miss matching an RNSD entry does not
  allocate; lookup reports STALL-until-commit. A read miss matching an RU
  entry merges (it will hit the committed M line).
- **Alloc/match same cycle:** an alloc and a snoop match against the same
  line in one cycle resolve alloc-first (the entry is visible to the snoop
  compare from the alloc cycle — the snoop must see the pending fill).

## Occupancy gauge

`occupancy_o` (valid-entry count) and `wb_occupancy` leave through the
MonBus event map (ch04) — the J7 occupancy histogram comes from these.
