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

# Observation: MonBus and counters

**Status:** built 2026-11-21 (onyx TASK-001 step 6b; D9 decided 2026-11-20). `onyx_monlite` and `onyx_counters` on `onyx_ccu`'s event taps, composed in `onyx_top`; the reference rig's pair block carries the MonBus chain that counts the packets and reads the counters through the harness CSR.

## Two instruments

The MonBus observer carries every event with its payload and timing, one packet a cycle through a bounded queue, and reports what it drops. The counters (`onyx_counters`, eight 32-bit saturating counters: transactions, lines supplied, memory reads, reads wasted, absorptions, write-backs, and two corner counts) are exact under any burst, cleared by a pulse and held by a level, the harness CSR's `tally_clear` and `tally_freeze`, so one host protocol snapshots the tally bins and the counters together. The D6 measurement (reads issued against reads wasted) is made from the counters; the MonBus gives it its shape in time.

The two corner counts say whether a run reached the cases the coherence rules exist for:

- `cu_dt`: CleanUnique slots whose gather ended with data. The upgrade was killed (its Shared copy was invalidated before the grant), and a peer that took the line Modified in between passed it dirty under the CleanInvalid snoop (onyx BUG-001). Each one is also a supplied line, and with the read alongside the snoop it is the one supplied line whose memory read was never issued, so `read_wasted = supplied - cu_dt` in that mode.
- `old_wb`: cache writes presented, and not accepted in that cycle, on a line a slot is still gathering. Such a write is older than that slot's verdict, typically a victim drain that the snoop passed on dirty (jet-prime BUG-002), and onyx lands it ahead of the newer owner's absorbed line (onyx BUG-003).

Neither needs an `onyx_ccu` port. The counter block keeps a per-slot mirror from the grant and gather taps (each slot's line, whether it is a CleanUnique, and whether it is still gathering) and recomputes `onyx_ccu`'s `r_aw_old` from it. The pair rig checks the mirrored flop against the real one every cycle, and checks both counts against its model.

## The observer

`onyx_ccu` exposes one-cycle event taps driven from its own handshakes (nothing on them feeds back); `onyx_monlite` turns them into 128-bit house MonBus packets (`PktTypePerf`, `PROTOCOL_CORE`, agent `0x00A3`, unit `0x01`) in the drop-and-count idiom of the caches' observers, with per-class holders in front of a sixteen-deep output queue because onyx's events cluster where the caches' do not. A lost event is counted and the count re-emitted as a `PktTypeError` / `AMBER_EV_DROPPED` packet when nothing is waiting. `USE_MONITOR = 0` ties the observer off, the same present-versus-absent pin the caches carry.

## Event classes

| code | class | when | payload |
|---|---|---|---|
| 0x20 | `TXN_START` | a grant: a transaction allocated | requester (a cache port; `N_PORTS` is the IO port), request class (the IO's: 7 a read, 5 a write), slot |
| 0x22 | `GATHER_DONE` | a slot's last CR landed (per answering port) | slot, DataTransfer, PassDirty, answering port, gather latency from the grant |
| 0x23 | `MEM_READ` | a memory AR taken | slot |
| 0x24 | `READ_WASTED` | a DataTransfer verdict for a slot whose read was issued or presented: its beats will be dropped (per answering port) | answering port |
| 0x25 | `ABSORB` | an absorption's BRESP | slot |
| 0x26 | `WRITEBACK` | a write other than an absorption taken on the write port: a cache's write-back, or the IO's write | requester for the IO's write (`N_PORTS`); a cache's write-back carries 0 in v1 (its port is not known to the observer) |
| 0x27 | `LOCK_WAIT` | a requester's candidate waited behind a held line, emitted on release | requester, episode duration |

: Table 4.1: onyx MonBus event classes (`onyx_pkg`)

The two per-port events are a class per port: two peers can each complete a different slot's gather in the same cycle, and the first cut's single `evt_gather` bit merged them, an event lost that nothing counted (the pair rig does it once a run). Each class has a two-deep holder; the drain takes one class a cycle, round-robin from the class after the last one taken. A class firing a third time while its two entries wait loses that event, and the loss is counted and reported: in the pair rig's gate cells the observer carries about 250 packets and reports 9 lost, all `TXN_START` and `GATHER_DONE` bursts. The AC handshake count was a class in the first cut and was retired as redundant: it is `TXN_START` times the peer count.

## What the counts mean

- **Transactions:** `TXN_START` is the grants; every allocated transaction gathers exactly once, so `GATHER_DONE` equals it.
- **The D6 trade:** `MEM_READ` is the memory reads issued; a `GATHER_DONE` with DataTransfer is a line a peer supplied. With the read alongside the snoop (`DEFER_AR = 0`) a supplied line whose read had already issued shows as `READ_WASTED`; with the read deferred, `READ_WASTED` is zero and `MEM_READ` is the reads that were necessary. The elision rate the deferred mode buys is `READ_WASTED` of the parallel mode as a fraction of its `MEM_READ`.
- **Serialization cost:** `LOCK_WAIT` episodes and their durations are the per-line rule at work.

## The mask layers

The house MonBus is a low-bandwidth event channel: it carries rare, meaningful events, and every per-transaction class the observer can emit floods it under sustained traffic (the handbook's `monbus-is-a-low-bandwidth-channel` note). The observer therefore carries the ocelus monitors' layers of masks, so the integrator picks what to transmit, and a masked event is dropped at the source: it enters no holder, counts as nothing lost, and the drop report says only what the channel itself lost. Enables are 1 for on; masks drop the bits that are set, the `cfg_*_pkt_mask` convention.

| layer | port | what it selects |
|---|---|---|
| the observer | `cfg_mon_enable` | everything; 0 is silent, nothing counted as lost |
| the packet type | `cfg_perf_enable`, `cfg_error_enable`, `cfg_pkt_mask[type]` | the event classes (all `PktTypePerf`) and the drop report (`PktTypeError`); the mask indexes the type (bit 4 Perf, bit 0 Error) |
| the event class | `cfg_perf_mask[code[3:0]]` | one bit per class: 0 `TXN_START`, 2 `GATHER_DONE`, 3 `MEM_READ`, 4 `READ_WASTED`, 5 `ABSORB`, 6 `WRITEBACK`, 7 `LOCK_WAIT`; the group core's `cfg_core_perf_mask` indexes the same codes, so the two can be set alike |
| the error code | `cfg_error_mask[code[3:0]]` | bit 9 the drop report (`AMBER_EV_DROPPED`); a masked report leaves the count accumulating in `dropped_count` |
| the port | `cfg_port_mask[p]` | the events attributed to requester p (`N_PORTS` is the IO port): `TXN_START` by the requesting port, `GATHER_DONE` and `READ_WASTED` by the answering port, `LOCK_WAIT` by the waiting requester, the IO's `WRITEBACK` by the IO (`MEM_READ`, `ABSORB` and `WRITEBACK` carry no port in v1) |
| the content | `cfg_addr_win_enable`, `cfg_addr_win_low`, `cfg_addr_win_high` | an inclusive address window on the transaction, the AXI monitors' address-range filter in onyx's terms: a per-slot watch bit is set at the grant (the grant address against the window) and read by the slot's later events (`GATHER_DONE`, `READ_WASTED`, `MEM_READ`, `ABSORB`); `TXN_START` is the grant itself; the write-back is matched on its own AW address; `LOCK_WAIT` on the waiting candidate's address, latched when the wait begins. Disabled is everything. The drop report is never windowed |

: Table 4.2: onyx observer mask layers (`onyx_monlite`)

The class layers turn a class on or off; the window is what makes a per-transaction class a low-bandwidth event. A class opened alone still fires on every transaction, which fits the channel at injector depth 1 and 2 and loses a fifth of its events at depth 8 in the thrash cells; the same class through a window on the lines of interest fires at the window's rate, which the channel is sized for.

`onyx_top` carries the layers as `mon_cfg_*`. On the Genesys2 reference rig they are four harness CSRs: `ONYX_MON_CTRL` (0x038: [0] enable, [1] error enable, [2] perf enable, [3] address window enable, [7:4] port mask, [31:16] class mask), `ONYX_MON_MASK` (0x03C: [15:0] packet-type mask, [31:16] error-code mask) and the window's bounds `ONYX_MON_WIN_LOW` / `ONYX_MON_WIN_HIGH` (0x014 / 0x018, inclusive; the sweep's `--onyx-mon-window LOW HIGH`). The reset is `0x007D0007`: everything enabled, no port masked, the six per-transaction classes masked and `LOCK_WAIT` open, so a bitstream out of reset transmits only the rare class and the host opens what it wants to see (`jet_perf_sweep.py --onyx-mon-classes`, with `all` the lower-bound reading of every bin and one class at a time what the channel carries exactly). The pair-rig testbench drives the layers from its cell's environment and holds a masked class to zero packets, a masked port to zero attributed packets, and the disabled observer to silence with nothing counted lost.

## Where the packets go

In the pair rig the harness exposes the observer as a third MonBus output (`mon2`) and the counters as ports. The onyx pair-rig testbench requires the counters to equal its own fabric model (transactions to grants, memory reads to memory ARs, absorptions, reads wasted to dropped reads, lines supplied to forwarded lines), every MonBus class count to be bounded by its counter, and the shortfall across classes to be covered by the observer's own drop reports: the observer loses nothing silently. On the Genesys2 reference rig the pair block merges the two caches' streams and onyx's through a `monbus_arbiter`, a `monbus_axil4_group_1wr` and a `monbus_tally_axil`, read by the host through the bridge's tally apertures with the harness CSR's clear and freeze bits, and the counters at CSR offsets 0x020 to 0x034 and 0x05C / 0x060 (`ONYX_CNT_*`, the last two `CU_DT` and `OLD_WB`; zero in the selections without onyx); the host profile `ref-onyx` (`jet_board.py`) bins the caches' core events as the jet rig does and onyx's classes in bins 11 to 17. The sweep with `--profile ref-onyx` reads the counters in the same frozen window as the tally and records them per cell. On the board the channel is the bound, not the observer, and by design: the house MonBus is a low-bandwidth event channel (the group writer takes several cycles a packet and serves three observers), and every per-transaction class the observer emits is one that floods it under sustained traffic, so at the thrash cells' event rates the tally bins fall to a fraction of the counters (bin 11 reads 12,613 against 20,240 transactions on `r64k_we64` at depth 1) while the resident and warm-up cells agree exactly. The bins are lower bounds on the board; the counters are the measurement. The observer's mask layers (Table 4.2) are the remedy the ocelus monitors carry for exactly this: the reset transmits only `LOCK_WAIT`, and a class opened alone is carried in full where the union is not (onyx ISSUE-001).

## What is open

The window is one address range; the AXI monitors carry several, and an ID (requester) match besides, which onyx has as the port mask. A cache's write-back carries no port in v1 (the IO's write carries `N_PORTS`); the tally keys on the event code only, so the DataTransfer flag of `GATHER_DONE` is read from the latch bank, not from a bin.
