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

# Serializer and Point of Serialization

**Status:** architecture recorded 2026-11-21 (D5 decided 2026-11-20, PRD v0.7).

## The transaction table is the point of serialization

onyx holds every transaction in flight in one table of SLOTS entries shared by all ports; a slot is the manager's unit of serialization. A slot carries the requester port, the line, the request class, the taken AR's ID and attributes, the counts of peers yet to accept the AC and yet to answer, the verdict bits (`DataTransfer`, `PassDirty`), and the completion bits (memory read issued and drained, replay done, absorption issued and done, retire seen). The memory read ID is the slot index, so a memory beat names its slot directly and the requester sees its own AR ID back.

SLOTS defaults to N_PORTS times (MSHR_COUNT plus 1): every entry of every cache and every upgrade can be in flight at once and nothing ever waits for a slot.

## The per-line rule

Two transactions on the same line never proceed together. A grant candidate whose line is held by any valid slot, whichever port holds it, waits ungranted in its port's pending queue; different lines interleave freely (D5). Because the loser's AR stays at its cache, the loser's MSHR entry is pre-AR, and the cache's own pre-AR rule answers any snoop to that entry at the Invalid row: the loser's later grant then resolves against the winner's committed line. The lock is held from the grant to the winner's retire pulse, not to its last beat; the argument for the retire rather than the beat is jet-prime delta 02's, and it holds unchanged for N ports.

`SERIAL_MODE = 1` is the bring-up shape the PRD row named: a candidate waits while any slot is valid, so one transaction is in flight system-wide.

## Fairness

Three arbiters rotate:

- the grant, over the N ports: priority starts one past the last granted port, so a port that lost a cycle wins the next contested one;
- the write port, over the N write-back channels and the absorption, the same way;
- the CD write into each requester port's snoop-data buffer, over the peers wanting it (Chapter 3.4).

No fixed-priority path exists, so a single busy port cannot starve another of grants, of the write port, or of a buffer. A port is held back from a second grant only while its own AR from the previous grant is untaken, which is the cache's pace, not another port's.

## What the per-line rule guarantees

- One valid slot per line at any time (the formal harness's first property).
- A grant never goes to a held line.
- The lock drops only after the requester's retire, and the retire bit is set only by the requester's own pulse naming the slot's read ID.
- A write-back is selected for the memory write port only when no slot on its line has an incomplete gather or a pending absorption.
- Two write-backs to one line are forwarded in the order they were presented: one presented while another port already presents one to the same line yields until that one is taken (jet-prime BUG-002: a victim whose drain had started when a snoop passed its line on still drains, and must land before the new owner's write-back of the line).

The first four are stated and proven on the onyx formal harness at N_PORTS 2 (TASK-001 step 4), carried over from the pair fabric's 27-property argument; the fifth is `ap_wb_order` on the same harness (2026-11-24).
