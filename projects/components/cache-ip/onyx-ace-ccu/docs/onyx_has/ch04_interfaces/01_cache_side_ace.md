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

# Cache-Side ACE Ports

## Decision status

**D7 is DECIDED (2026-10-05): onyx owns the ACE-shaped AC/CD/CR snoop port; `amber` and `jet` adapt to it behind a thin adapter.** This chapter therefore records the cache-side ACE contract as real content at 0.1.

## Port count

`N_PORTS` cache-side ports, 2 to 4 (D11, decided 2026-11-20). Each port is independent at the handshake level: its own pending queue, its own armed `ARREADY`, its own replay engine and snoop-data buffer. The ports meet in the shared transaction table (Chapter 3.3).

## What a port carries, as built

A cache-side port is three things the house caches already present:

- **The cache's memory side, plain AXI4.** AR/R for fills, AW/W/B for write-backs, exactly as jet-prime drives them toward the pair fabric. The request class does not ride `ARSNOOP`; the AR is plain AXI4 and onyx regenerates the memory-side AR fields it needs (length, size, burst) from the slot.
- **The D-8 coherence sideband.** `coh_req_valid/addr/type`: one pulse per fill launch or upgrade (`ReadNotSharedDirty`, `ReadUnique`, `CleanUnique`) and per dirty write-back launch (`WriteBack`), the class in `l1_pkg`'s `AMBER_ACE_*` encoding; and `coh_done_valid/id`: one pulse per retired MSHR entry or completed upgrade, carrying the entry's read ID (`MSHR_COUNT` for the upgrade). The pulse precedes the AR; the cache presents its ARs in launch order, so onyx pairs each granted pulse with the next AR of that port.
- **The ACE-shaped snoop port (D7).** AC in to the cache, CR and CD out of it, `ACSNOOP` in the IHI0022 encoding, CRRESP five bits, CD-before-CR (invariant 6). jet-prime's `m_axi_ac*`, `m_axi_cr*` and `m_axi_cd*` are this port; no adapter sits between them and onyx.

## Transaction subset

The D2 subset as decided 2026-11-20: `ReadNotSharedDirty`, `ReadUnique`, `CleanUnique`, `WriteBack`, `Evict` -- what the house caches issue. `WriteBack` and `Evict` allocate nothing in the manager; `MakeUnique` is decoded as a no-data class but no cache issues it yet. `ReadShared` is accepted and snooped as `ReadNotSharedDirty` would be; a MESI cache has no Owned state and does not issue it.

amber's `WriteClean` (amber TASK-004, the clean-all write-back: the dirty line is written and kept) is a sideband class like `WriteBack`: it allocates nothing, and its AW/W/B is a write-port pass-through under the same hold.

## What a cache owes the port on its own writes

onyx tracks no write-back or `WriteClean` in its table; the cache answers for the line while the write is in flight. The core-alone rig (`dv/tests/test_onyx_core_rig.py`) holds its BFM caches to these rules, which are jet-prime's (BUG-002) extended to `WriteClean`:

- **A write-back victim** answers the first snoop that takes the line with `DataTransfer` + `PassDirty` from its buffer, and Invalid after that; its drain, once presented, completes (the presentation-order rule on the write port keeps it ahead of the new owner's write-back).
- **A `WriteClean` line** is busy until its BRESP and answers snoops as Modified until then. Answered clean, a requester that then hits only Shared copies would be served from memory before the `WriteClean` lands: onyx holds that write while the requester's slot gathers.
- **A killed upgrade** (the Shared line invalidated by a snoop before its `CleanUnique` was granted) completes to Invalid and does not perform its store; onyx snoops the upgrade with `CleanInvalid`, so a peer that took the line Modified in between passes it dirty rather than dropping it (onyx BUG-001).

## The ACE-front-side flavor

An ACE master that carries the class on `ARSNOOP`/`AWSNOOP` rather than on the sideband is the D7 adapter's second half: a thin decode of `ARSNOOP` into the sideband pulse in front of the port. It is not built in v1 because no such master exists in the family yet; the RDS-DV `AXI4ACEMasterRead/Write` BFMs are the first candidates.

## Normative reference

The in-repo [AMBA ACE Interface Definition](../../../../References/AMBA_ACE_Interface_Definition.md) is the normative contract for the ACE-shaped port. It defines the channel inventory, payload fields, CRRESP semantics, ordering rules, and the family convention for RACK/WACK. This book does not restate that contract; it points to it.

## Open questions

### RACK/WACK (N1 decided 2026-10-11)

Ruling 2026-10-11 (Sean): RACK/WACK are omitted from the onyx↔cache
contract. Chinnakonda §7.20 and §14.39 say they are not required when
data-return and snoop paths are ordered to the coherency point, and the
D7 port contract guarantees that ordering. The house `axi4ace_master_rd/wr`
wrappers still auto-pulse RACK/WACK; that behavior is deprecated for family
contract use and its removal is tracked as amber RTL follow-up A5. See
[onyx PRD row N1](../../../PRD.md) and the
[AMBA ACE Interface Definition](../../../../References/AMBA_ACE_Interface_Definition.md).

### CD/CR ordering (decided 2026-10-11)

Ruling 2026-10-11 (Sean): the family convention is **CD before CR**
— a transaction's CD beats complete before its CR is asserted — and it
is the binding contract. The AMBA ACE spec requires only per-channel
ordering (CR in AC order, CD in AC order), so it permits either order;
the book yielded no guidance on CD-vs-CR ordering. The in-repo
[AMBA ACE Interface Definition](../../../../References/AMBA_ACE_Interface_Definition.md)
records the convention and the ruling. The PRD's invariant #6 is
DECIDED with the CD-before-CR wording.

## What is fixed

- onyx is the owner of the ACE-shaped snoop port.
- The cache-side ports are plain AXI4 AR/R/AW/W/B plus the D-8 sideband plus AC/CD/CR (as built, TASK-001 step 2).
- The D2 subset is the working transaction set.
- The in-repo AMBA ACE Interface Definition is the normative contract.
- RACK/WACK are omitted from the onyx↔cache contract (N1 decided).
- CD-before-CR is the binding snoop-response ordering (invariant 6 decided).

## What is open

- Whether the decoder grows with D2 to include barriers, DVM, or WLU/WU (N5, N6: not promoted).
- The ACE-front-side flavor of the port (`ARSNOOP` decode), when a true ACE master appears.
