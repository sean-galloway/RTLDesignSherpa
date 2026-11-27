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

# Memory-Side AXI4 Master

**Status:** as built 2026-11-21 (D1, D5 and D6 decided 2026-11-20, PRD v0.7).

## Port count and shape

One AXI4 master toward the house memory path (D1: CCU only). Plain AXI4 AR/R/AW/W/B; no snoop channels on this side. In the reference rig the far side is the house `sdpram_slave_axi4_axi4`; on the Genesys2 board the same slave behind the bridge.

## Reads

onyx issues one memory read per allocated data-class transaction at most: a full line (`ARLEN = FILL_BEATS - 1`, `ARSIZE` the bus width, INCR) at the slot's line address, with the requester's `ARCACHE`, `ARPROT` and `ARUSER` carried through. The read ID is the slot index, so a returning beat names its slot directly and several reads are outstanding at once, one per slot; the requester sees its own `ARID` back on R, not the memory's. A presented AR is held until taken.

When the read issues is the D6 mode (Chapter 3.2): `DEFER_AR = 0` at the last peer's AC accept, `DEFER_AR = 1` once every CR is in with no supplier. A read whose slot a peer then supplies is still drained to completion; its beats are consumed and dropped.

## Writes

The write port carries two kinds of burst, one at a time, round-robin over N + 1 candidates:

- **Write-backs,** passed through from a cache's AW/W/B with the cache's own `AWID`, address, length and attributes. A write-back to a line with a slot whose gather is incomplete, or whose absorption is pending, holds at its AW until that clears; one presented while another port already presents a write-back to the same line holds until that one is taken, so two write-backs to a line land in presentation order.
- **Absorptions,** the manager's own writes of a `PassDirty` line from the slot buffer: a full line at the slot's line address with `AWID = 8'hA0 | requester port` truncated to the ID width (at the rigs' 8-bit IDs, `A0` and `A1`), full strobes. One absorption per supplied-dirty transaction; the slot does not free until its `BRESP`.

`AWID` policy (the open D5 detail of the 0.2 book) is therefore fixed by construction: write-backs keep the cache's ID, absorptions use the manager's reserved IDs, and the port runs one burst at a time so no interconnect reordering question arises.

## What is fixed

- One AXI4 master; the memory read ID is the slot index; the requester's `ARID` is returned to it.
- The read is issued per the D6 mode and dropped when a peer supplies the line.
- Write-backs pass through with the cache's ID; absorptions carry the manager's reserved ID.
- One write burst in flight; the write-back hold against an incomplete gather or pending absorption, and a memory read to a line held while a write to that line is in flight (onyx BUG-002).

## What is open

- The ACE-Lite IO port of D1, a later TASK-001 step, will add a non-coherent requester on this side's traffic.
