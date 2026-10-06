# AMBA ACE — Working Interface Definition for cache-ip

Distilled 2026-10-05 for the `cache-ip` family, then **verified
clause-by-clause against IHI 0022H on 2026-10-05** (Arm's direct PDF, linked
in §7; fetched to `/tmp` for comparison, not stored in-tree). Verification
confirmed every transaction type, channel payload, CRRESP bit, and the
ACE-Lite channel exclusions; it caught and fixed two errors in the ordering
rules (the original draft claimed ACE serializes snoops one-at-a-time and
mandates CD-before-CR — ACE requires only per-channel ordering and permits
multiple outstanding snoops; the stricter behavior is recorded above as our
own adapter convention). This document is the
in-repo definition of the **ACE-shaped port contract** referenced by
[amber D4](../amber-mesi-l1/PRD.md) and [onyx D7](../onyx-ace-ccu/PRD.md)
(family decision 2026-10-05: cache-ip is ACE-shaped).

**Normative reference:** Arm, *AMBA AXI and ACE Protocol Specification*,
IHI 0022 (ACE chapters). Available from Arm without charge (direct PDF in
§7); Arm copyright, so deliberately not mirrored here. Where this document
and IHI 0022 disagree, IHI 0022 wins — file a docs bug. **Worked example:**
`pulp-platform/culsans` (`ace_ccu_top`, Solderpad license) — read its RTL
after this page, not before.

---

## 1. What ACE is

ACE (AXI Coherency Extensions) is AXI4 extended so that multiple caching
masters can share memory coherently. An ACE master is typically a CPU's
cache; an ACE-Lite master is a non-caching agent (DMA, IO) that wants
coherent *access* without being snooped. Between the masters and memory sits
a coherency manager — in this family, **onyx** — which receives coherent
transactions, broadcasts snoops to the peer caches, gathers their responses,
decides whether DRAM must be read, and serializes same-address traffic.

ACE adds three channels to AXI4. Everything else — AW/W/B/AR/R semantics,
burst rules, handshake rules — is unchanged AXI4 and is not restated here.

## 2. Channel inventory

### 2.1 Coherent master → manager (front side, per master)

The five AXI4 channels, with a transaction-type field added to each address
channel:

| Channel | New/changed payload | Notes |
|---|---|---|
| AR + R | `ARSNOOP[3:0]` | read-side coherent transaction type |
| AW + W + B | `AWSNOOP[2:0]` | write-side coherent transaction type |

Data and response channels are plain AXI4. A coherent read (e.g.
ReadShared) delivers its data on the ordinary R channel, sourced by the
manager from a peer cache or from memory as the adjudication decides.

Full ACE master interfaces also carry two acknowledge handshakes outside
the five channels: **RACK** (read acknowledge — master pulses after the last
read data beat of each transaction) and **WACK** (write acknowledge —
master pulses after the write response). ACE-Lite excludes both (IHI 0022H
§D11.1). Our D2 subset needs no ordering semantics from them; the family
convention is to auto-pulse them promptly at the adapter and record that
choice in the module docs.

### 2.2 Manager → cache, cache → manager (snoop side, per cache)

Three new channels. Direction below is from the point of view of the cache
(amber/jet); the manager (onyx) sees the mirror image.

| Channel | Dir | Payload | Meaning |
|---|---|---|---|
| **AC** — snoop address | in | `ACADDR`, `ACSNOOP[3:0]`, `ACPROT[2:0]` | "What state does this line have in you, and what should you do about it?" |
| **CR** — snoop response | out | `CRRESP[4:0]` | the answer: will you transfer data, is the line shared, is dirty responsibility passing |
| **CD** — snoop data | out | `CDDATA`, `CDLAST` | the line's data, when CRRESP said it would come |

Handshake rules mirror AXI4 (VALID/READY, no combinatorial dependency of
READY on VALID). Ordering rules that matter (IHI 0022H §D3.8–§D3.9, §D5.2,
§D6.2):

- **CR and CD only after AC.** The snoop response and any snoop data must
  only be asserted after the ACVALID/ACREADY handshake.
- **In-order responses, in-order data.** CR responses must be returned in
  the same order as the AC addresses; CD data likewise. The spec permits a
  cache to have **multiple outstanding snoop transactions** — serialization
  is not required by ACE, only per-channel ordering is.
- **Family convention (decided with onyx D4):** the amber/jet adapter
  completes a transaction's CD beats before asserting its CR, so onyx's
  gather sees one fully-closed response at a time. This is stricter than
  ACE requires and simpler to verify; it is our contract, not the spec's.
- **Snoop vs. local access arbitration.** A snoop reads the tag array and
  may evict/change a line's state, so it must arbitrate with the cache's own
  CPU-side tag port. This arbitration point is the classic cache-side cost
  of becoming a snoop responder (culsans' CVA6 cache shows one
  arrangement).

## 3. Transaction types (the onyx D2 research subset in **bold**)

Read side (`ARSNOOP`): ReadOnce, **ReadShared**, **ReadUnique**, ReadClean,
ReadNotSharedDirty, **CleanUnique**, **MakeUnique**, plus barrier/DVM forms
(out of scope, onyx D8).

Write side (`AWSNOOP`): **WriteUnique**, WriteLineUnique, **WriteBack**,
WriteClean, **Evict**, plus barrier/DVM forms (out of scope, onyx D8).

The six bolded transactions are the subset onyx D2 recommends; the
definition of the subset is: everything amber or jet needs to run MESI
write-back coherence against a manager, and nothing that requires DVM or
barrier semantics.

Intent of each subset member, one line each:

- **ReadShared** — fetch a line to read; other caches may keep Shared
  copies; the line arrives in S (or E if nobody shared it).
- **ReadUnique** — fetch a line to write; all other copies must be
  invalidated; if a peer held it dirty, its data (or DRAM's) is supplied.
- **CleanUnique** — "I already hold the line; make my copy Unique." No data
  transfer; peers with Shared copies drop them.
- **MakeUnique** — like CleanUnique but the requester does not need the data
  (it will overwrite the whole line); peers invalidate.
- **WriteBack** — retire a dirty line to memory; the manager must merge the
  data into DRAM (or hand it to a subsequent reader).
- **Evict** — retire a clean line; a hint: no data, no DRAM write needed.

## 4. The CRRESP decision bits

CRRESP is where a snooped cache answers. The four bits the manager's
adjudication logic consumes (bit 4, `WasUnique`, also exists per IHI 0022):

| Bit | Name | Meaning when set |
|---|---|---|
| [0] | DataTransfer | "I will drive the line's data on CD." Required of a Modified responder (or any responder told to transfer). |
| [1] | Error | "My lookup had an error." Propagated, not interpreted. |
| [2] | PassDirty | "The line is/was dirty and dirty responsibility moves to whoever receives the data" — set with DataTransfer when the responder passes dirty data, and on its own when the data is already moving elsewhere. The manager uses it to decide whether DRAM must be (re)written. |
| [3] | IsShared | "Another master (or I) may hold a copy." Tells the manager the requester must not be given Exclusive/Unique state, and that DRAM-read elision is safe when data was supplied. |

The adjudication onyx D6 specifies falls straight out of these bits:
a coherent read completes from cache-supplied data alone iff some CR
carried `DataTransfer`; DRAM must be read iff none did and no `PassDirty`
moved dirty responsibility; DRAM must be written iff `PassDirty` passed
dirty data that the requester did not absorb.

## 5. ACE-Lite

ACE-Lite is the non-snooped half: a master may issue coherent transaction
types but never receives AC, so it never drives CR/CD. onyx's IO port (onyx
D1) is ACE-Lite — this is why the earlier "ACE-lite-shaped snoop channel"
candidate in amber D4 was set aside: a snoop *responder* must drive CR/CD,
and ACE-Lite has no snoop channels at all.

## 6. What this family implements, and what it deliberately does not

In scope (amber D4 / onyx D2 subset, single shareability domain, onyx D8):
the six transaction types of §3, the AC/CR/CD contract of §2, the CRRESP
semantics of §4, broadcast snoop fanout (onyx D3 v1), same-address
serialization (onyx D5).

Transport for this contract exists in `rtl/amba/ace/` (added 2026-10-05):
`axi4ace_master_rd/wr` and `axi4ace_slave_rd/wr` (front-side movers with
`ARSNOOP`/`AWSNOOP`, auto-pulsed `RACK`/`WACK` on the masters), the
`axi4ace_snoop_slave` / `axi4ace_snoop_master` AC/CR/CD movers, and
`rtl/amba/monitor/axi4ace_snoop_monitor_lite` for snoop-side observation.

Out of scope, recorded as decisions and not accidents (onyx D8): DVM
(distributed virtual memory) messages, barrier ordering, multiple
shareability domains, stash/dealloc hints. The repo's port contract is
**ACE-shaped** — same channels, signals, payload fields, and ordering rules
on the pins — without claiming whole-spec conformance; see onyx D7 for why
"shaped" rather than "compliant."

## 7. Sources

1. Arm, *AMBA AXI and ACE Protocol Specification*, IHI 0022, ACE chapters —
   the definition. Current issue H (2020), direct PDF:
   <https://developer.arm.com/-/media/Arm%20Developer%20Community/PDF/IHI0022H_amba_axi_protocol_spec.pdf>
   (landing page: <https://developer.arm.com/documentation/ihi0022/>).
   Available from Arm without charge; Arm copyright — cited, not mirrored.
   Sections this document was verified against: D2.2 (channels), D3.8–D3.9
   (signaling, dependencies), D3.20–D3.22 (CRRESP), D5 (snoop transactions),
   D6.2 (sequencing), D11.1 (ACE-Lite).
2. `pulp-platform/culsans` — `rtl/src/ace_ccu_top.sv` and the CVA6
   coherent cache: a working ACE CCU and a working snoop-responder cache.
   Worked example, not a dependency. https://github.com/pulp-platform/culsans
3. *A Primer on Memory Consistency and Cache Coherence* (Sorin, Hill, Wood,
   2nd ed., stored alongside this file) — the coherence-theory background
   the transaction types above instantiate.
4. gem5 Ruby SLICC specs (`gem5-ruby-protocols/`, stored alongside) —
   executable transient-state tables for the same protocol family; the
   golden-model source material, phrased in messages rather than ACE
   signals.
