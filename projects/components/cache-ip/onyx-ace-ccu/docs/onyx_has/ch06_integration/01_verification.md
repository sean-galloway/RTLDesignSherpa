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

# Verification Strategy

**Status:** as done through onyx TASK-001 steps 1, 2, 4, 6 and 7 (2026-11-23). D10 decided 2026-11-20: Pattern-B cocotb, the RDS-DV ACE BFM verified before the RTL, a fabric-style formal argument.

## What has been run

| Layer | Where | What it proves | Result |
|---|---|---|---|
| ACE BFM on the gather shapes | `dv/tests/test_onyx_snoop_gather_rig.py` on `dv/tb/onyx_snoop_gather_rig_tb.sv` | N snoop-master BFMs against N snoop-slave BFMs through the house ACE transport: the caches' CRRESP matrix cell by cell with full line data, broadcast gathers over the MESI-legal patterns, out-of-order completion, back-to-back per port, a compliance checker per port | gate 1/1, func 4/4, full 18/18 from clean at 2, 3 and 4 ports and both bus widths; 0 mismatches, 0 violations |
| The core with real caches | `dv/tests/test_onyx_pair_rig.py` on `dv/tb/onyx_pair_rig_tb.sv` | jet-prime's pair-rig testbench and grid unchanged, onyx in the fabric's place: both CPUs driven, the two-cache lockstep model with the fabric rules, ACE compliance scoring, the MSHR x VICTIM x policy knob sweep | gate 4/4, func 6/6, full 26/26 from clean; 0 mismatches; gate reports identical to the fabric's line for line |
| Formal, two ports | `formal/onyx/onyx_ccu` | the pair fabric's 27 safety properties restated for onyx at the fabric's geometry (16 lines, four beats, four slots, SNOOP_INFLIGHT 2): the per-line rule, the lock to the retire, AR and AC legality and stability, the gather bookkeeping, routing of every beat, the write-port hold, the table flag order, the engines' liveness of reference | `prove` (24 local properties, BMC depth 24) PASS 20:30; `prove_book` (3 end-to-end bookkeeping properties, depth 16) PASS 14:41; 19 of 19 covers reached by step 7; three mutations each fail the property written for them |
| Board | Genesys2 reference rig, `REF_CACHE_SEL` 4 and 5 | smoke (init + smoke CRC) and the 55-point single and dual sweeps in both D6 modes | PASS; every cycle count and CRC of SEL 4 equal to the pair fabric's bin 7 (Chapter 6.2) |
| The IO port with real caches (D1) | the pair rig, `AXI4ACEMasterRead` / `AXI4ACEMasterWrite` on `io_*` | the fabric model's third requester: the IO's slot transactions queued before the AR / AW and popped at the grant, the snoop resolution per peer with the OR as the verdict, the IO's data scored on the wire at RLAST against the supplier's line or the memory model as of the memory AR, its writes landing in the memory model at the W handshake; directed: ReadOnce against M (absorbed, holder invalidated), E (DT, holder to S), S (memory) and nothing, ReadNoSnoop; WriteUnique against M (absorb then merge, the holder's re-read sees both), WriteLineUnique against two sharers, WriteUnique against E, WriteNoSnoop; a read and a write together, a read behind a write of its own line; the soak adds an IO loop (ReadOnce anywhere, the other kinds in the IO's own region) | gate 12/12, func 17/17, full 51/51 from clean, 0 mismatches; one IO-port mask cell (`_pmio`) on the gate |
| The IO port, formal | `formal/onyx/onyx_ccu` | the IO as free AR / AW / W under A-io, every property restated over three requesters, the IO's own (`ap_io_port`: its R beats and RLAST, its one-at-a-time, its write handshakes only in its own selection, its WriteUnique forwarded only gathered, absorbed and behind any presented write-back), eight IO covers | `prove` PASS (BMC depth 24, 5 h 17 min), `prove_book` PASS (depth 16, 2 h 13 min), `cover` 27/27 reached, on the regenerated flat |
| The IO port on the board | the reference rig's doorbell (`ref_io_master`, harness CSR 0x040-0x058), the `io` sequence | WriteNoSnoop / ReadNoSnoop / ReadOnce of a line of its own; ReadOnce, WriteUnique, ReadOnce, ReadNoSnoop and a partial WriteUnique of a line the caches hold, after the smoke | D1-BOARD-PLACEHOLDER |

: Table 6.1: Verification as done

## The BFM family (D10)

`CocoTBFramework.components.ace` in RDS-DV (2026-10-05) is the family named in the PRD row: `AXI4ACEMasterRead/Write`, `AXI4ACESlaveRead`, `AXI4ACESnoopMaster`, `AXI4ACESnoopSlave`, `ACEComplianceChecker`, the `ARSnoop` / `AWSnoop` / `SnoopType` / `CRRESP` types. onyx was its first real application; the gather rig found one gap, recorded on the task page for RDS-DV: the snoop-slave BFM sends one CD beat every three cycles because its responder waits for each beat's handshake before queuing the next, so a latency measured through it carries two extra cycles per beat that are the BFM's. The snoop-master BFM allows one outstanding snoop per port, which is the family convention and onyx v1's.

## The formal argument

The harness (`formal_onyx_ccu.sv`) is the pair fabric's carried over: the environment is both caches, both snoop responders and the memory as free inputs under their documented contracts (the request pulses, the AR in launch order with a fresh ID, the retire after the last beat, the responders answering only accepted ACs in order with CD before CR, the memory answering only issued reads). What onyx changed is what the harness changed: the per-slot accept and answer bits became counters, so the harness reads the DUT's all-accepted and gathered flags; the memory AR waits on all-accepted and the absence of a DataTransfer; the flag order is DataTransfer implies all-accepted, PassDirty implies DataTransfer, gathered implies all-accepted; `CDREADY` depends on `CDVALID`. The first run found one real weakness and one harness gap together: the memory could present a beat nobody asked for in the one cycle after reset where its contract was not yet armed, and onyx's gather counters read "complete" for an invalid slot, so the stray beat was forwarded. The RTL now qualifies both memory-R routes with a read outstanding (a beat for no read is held, as a memory fault), and the harness holds reset for the two steps before the contracts arm. The mutations: the gather declared complete at once, the fanout including the requester, a second grant to a port with its AR untaken; each fails at step 3 on its property.

A three-port harness needs the per-peer accept and answer shadow the counters summarize; it is the next formal item. Liveness bounds (the control's style, derived from the environment's constants) are not yet stated for onyx.

## What the IO port found

The first IO read against two sharers hung: with every cache a peer of one slot, two peers accepted their ACs in the same cycle and the per-peer decrement of the slot's counter, written twice to one register in one cycle, landed once; the gather never completed. The counters now step by the cycle's count per slot and the GATHER_DONE tap goes to the last of the cycle's answers (`vault/handbook/design/credit-tokens-count-every-event.md`). The pair-rig run at two ports never reached the case, because a cache's transaction has one peer there; N_PORTS 3 and 4 would have. The formal run then found the IO write's busy flag set at its AW take rather than its selection, a window in which the write port held the IO's selection without the port counting itself busy (`ap_engines_live` at step 4); the flag is set at the selection now.

## Not yet run

- A core-alone rig with BFM caches on the AXI4 side, and a three-cache rig with real caches (N_PORTS 3 and 4 are lint-clean and BFM-exercised on the snoop side only).
- Golden-model parity at the three-block level beyond the pair-rig lockstep model (the gem5 `MESI_Two_Level` mapping remains the plan).
