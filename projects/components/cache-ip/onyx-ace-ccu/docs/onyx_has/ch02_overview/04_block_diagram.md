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


# Block Diagram

**Status:** as built. Figure 2.1 is drawn from the RTL (`rtl/top/onyx_ccu.sv`, `rtl/top/onyx_top.sv`), 2026-11-27: the cache ports, the ACE-Lite IO port (D1) and the MonBus observer (D9) are all in it. The microarchitecture of each block is the [onyx MAS](../../onyx_mas/onyx_mas_index.md).

### Figure 2.1: onyx whole unit as built

![onyx ACE CCU as built: the sideband pulses through the pending queues and the grant into the transaction table; the memory AR stage; the AC queues, CD pick, snoop-data buffers and replay engines; the memory R router and R select; the write port; onyx_monlite and onyx_counters on the event taps](../assets/graphviz/01_block_diagram.png)

**Source:** [01_block_diagram.dot](../assets/graphviz/01_block_diagram.dot)

## The shape as built

`onyx_ccu` is one module; `onyx_top` adds the observer beside it. The blocks in Figure 2.1:

1. **Per-port front end.** The D-8 sideband pulse enters a four-deep pending queue per cache; the port's AR is taken into the granted slot (`ARREADY` from a register); the port's R channel is driven by its replay engine or by a forwarded memory beat.
2. **The ACE-Lite IO port (D1).** One non-caching requester, index `N_PORTS` of the table. Its AR or shareable AW is its grant candidate; it shares the lock, the slots, the snoop queues, the replay engines and the write port with the caches (Chapter 4.5).
3. **Transaction table (the point of serialization, D5).** `SLOTS` entries shared by all requesters: requester, line, class, the taken AR, the peer counters, the verdict bits, the completion bits. The grant (rotating priority over the `N_PORTS` caches and the IO port) allocates into it under the per-line lock.
4. **Fanout and gather (D3, D4).** One AC queue per cache in grant order, one in-flight queue per cache for the ACs accepted and unanswered, per-slot counters for the gather, the CRRESP merge.
5. **Adjudication and the memory read (D6).** The memory AR stage (lowest slot with every AC accepted, or every CR in under `DEFER_AR`, no supplier, and no write to its line in flight), the AR hold, the memory R router (forward, hold, drop).
6. **Snoop-data buffers and replay.** One buffer per requester (`N_PORTS + 1`) written by the arbitrated CD beat, one replay engine per requester, the absorption read.
7. **Write port.** One burst at a time, round-robin over the `N_PORTS` write-back channels, the absorption and the IO write, with the write-back holds and the old-write-back-first order.
8. **Observation (D9).** `onyx_monlite` turns the event taps into MonBus packets behind its mask layers and address window; `onyx_counters` keeps eight exact counts (Chapter 4.4). The debug taps the pair-rig testbench reads are kept beside them.

## What is not in the shape yet

An `ARSNOOP`-decoding front end for a true ACE master (the caches carry the request class on the sideband), the cache-maintenance snoops an ACE-Lite master may issue on AR, and a directory-lite snoop filter (D3, a future parameter).
