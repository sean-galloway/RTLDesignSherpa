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
# jet-prime delta 05: a victim passed on by a snoop is not written back (BUG-002)

**Status:** landed 2026-11-24. The fifth place jet-prime differs from jet.
jet's [MAS ch02/03](../../../jet-mesi-l1/docs/jet_mas/ch02_blocks/03_jet_wb_buffer.md)
still describes the write-back buffer as jet has it; this chapter is the
part jet-prime changed, and the manager-side rule that goes with it
([delta 02](02_pair_fabric.md), and onyx's write port).

## What jet's rule was, and why it was wrong

A dirty victim waits in the WB buffer until its drain's BRESP. A snoop that
matches it is answered from the buffer at Modified (the snarf), and jet's
MAS said what happens next: "the entry's post-snoop state effect recorded
so the drain writes back the correct thing (an invalidated snarfed victim
still drains -- the fabric already took the data; the drain completes the
memory update)". The RTL recorded the effect and never read it; every
snarfed victim drained.

Every snoop that changes a Modified line passes the line on: ReadShared,
ReadOnce, ReadUnique, CleanShared and CleanInvalid answer DataTransfer +
PassDirty (the manager absorbs the line, or the requester takes it dirty),
and MakeInvalid hands the requester a line it will overwrite whole. ACE's
rule is the master's: a line passed on dirty is no longer the master's to
write back. The drain that follows writes the same bytes the absorption
wrote, which is harmless only while nobody writes the line in between. Two
caches can: the new owner writes the line, evicts it, and its write-back
lands; the old victim's drain, still queued or held at the manager, lands
after it and memory goes back to the old bytes.

The pair rig reproduced it once a soak phase drove both CPUs at a few lines
of two sets (2 of 20 FULL cells failed in two minutes; seed 83331,
`s016w2 m02v1`): cache 1's drain of line 0x1b9 started, the fabric held its
AW for cache 0's ReadUnique, the snoop passed the line on, cache 0 wrote it,
evicted it, and its write-back won the round-robin against cache 1's held
AW. Cache 1's stale line landed 13 cycles after cache 0's.

## The rule now

Three parts, one per place the old line could get back to memory:

1. **An entry passed on before its drain starts ends** (`jet_prime_wb_buffer`).
   The snoop's effect clears it from the snarf CAM at once and the head
   retires it without a drain when it gets there. The own-lookup drain-race
   stall ends with it: the cache may refetch the line.
2. **An entry whose drain has started drains, but answers no further snoop.**
   Its AW may already be presented, and an AXI AW cannot be withdrawn. It is
   marked passed (`sn_passed_o`): the CAM still matches it, so the cache's own
   refetch keeps waiting for the BRESP, but `jet_prime_control` no longer takes
   it as a snoop source -- a second snoop (the IO's, a third cache's) sees the
   Invalid row, never the stale bytes.
3. **The manager forwards write-backs to one line in presentation order**
   (`jet_prime_pair_fabric`, `onyx_ccu`). The drain in part 2 is held at the
   manager while the slot gathers and absorbs; once released it must not lose
   the round-robin to the new owner's later write-back of the same line. A
   write-back presented while another port already presents one to the same
   line yields until that one is taken, and the one burst in flight orders the
   two in memory. A stale/new pair can never be first presented in the same
   cycle: the new owner's write-back follows its own fill, which follows the
   verdict that the stale AW predates.

A drain must not start between a snoop's grant and its effect, or a passed
line would drain after all: `jet_prime_control` holds `drain_start` while a
WB-sourced snoop on the head entry (`sn_head_o`) is granted or in service,
bounded by the service (at most FILL_BEATS + 2 CD handshakes), after which
the head has ended. Only the head: the first version held every drain start
during any WB-sourced snoop, and the control liveness proof failed its
24-cycle drain bound (`ap_drain_progress`, step 62). A snoop granted in its
entry's BRESP cycle retires that entry at once, and the next head's drain
waited out the rest of a service that was not on its line. `sn_head_o` is
live through the service, so an entry that becomes the head mid-service is
held from that cycle.

## Cost

No cycle on any measured path: a drain start waits only while a snoop is
being served from the buffer, and the order hold delays a write-back only
behind another to the same line. Area: two bits per WB slot, one for the
head's drain in flight, and two bits per manager port.

## Verification

| Layer | What | Result |
|---|---|---|
| WB buffer unit | the entry ends (both effects), a passed-on entry behind the head is skipped without a drain, the draining head is passed and still drains, the random phase with drain starts and effects | gate / func / full PASS |
| Control unit | the BRESP-cycle snarf; a second snoop to a passed entry answers the Invalid row with no effect; a drain-progress watcher (an eligible drain waits at most 2 cycles unless a snoop is on its own line) and a snarf in the head's BRESP cycle with a second victim behind it | PASS; the first version's hold restored fails all three passes |
| Pair rig | the hot-set phase (both CPUs, 70 % writes, `WAYS + 3` tags in two sets) after the uniform soak; a write-back order check at the cache ports, independent of the fabric | full 155/155 from clean; every full cell ends 5-31 entries and drains 16-75 passed entries per cache |
| Mutations | M1, the fabric's order hold removed: seed 116 of 24 fails, the order check first; M2, entries never ended: 26 of 26 pair-rig cells fail | both caught |
| Formal | control: `ap_wb_no_drain_in_svc`, `ap_wb_ended_never_drains` (covers `cp_wb_ended` step 42, `cp_wb_passed_snoop` step 44); pair fabric and onyx: `ap_wb_order` (cover `cp_wb_order_wait` step 4) | covers reached; control liveness prove PASS (depth 112), pair fabric prove + prove_book PASS, onyx prove_book PASS; control safety and onyx prove running |

## Why the suites missed it

Recorded in the bug (jet-prime BUG-002) and in the handbook's escape
analysis: the unit test asserted the old rule, the core rig has no second
writer, the pair rig's model restated the RTL's rule, and the uniform soak
reached a WB snarf 0-6 times a cell.
