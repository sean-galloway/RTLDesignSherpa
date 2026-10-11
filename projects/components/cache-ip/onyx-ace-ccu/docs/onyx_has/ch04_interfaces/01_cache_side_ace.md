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

N ACE-facing slave-side ports accept coherent transactions from attached caches. N is an elaboration parameter; D11 is open but the recommended direction is 2–4 masters. Each port is independent at the pin level: its own AR/R/AW/W/B channels and its own AC/CD/CR snoop channel.

## Transaction subset

Each port accepts the D2 subset on the AR and AW channels:

- `ReadShared`, `ReadUnique`, `CleanUnique`, `MakeUnique` on `ARSNOOP[3:0]`
- `WriteBack`, `Evict` on `AWSNOOP[2:0]`

The exact decoder width and BFM scope depend on D2 closing on this subset. Until D2 closes, the contract is "the D2 subset as defined by the PRD."

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
- The cache-side ports are ACE slave-side: AR/R/AW/W/B plus AC/CD/CR.
- The D2 subset is the working transaction set.
- The in-repo AMBA ACE Interface Definition is the normative contract.
- RACK/WACK are omitted from the onyx↔cache contract (N1 decided).
- CD-before-CR is the binding snoop-response ordering (invariant 6 decided).

## What is open

- Whether the decoder grows with D2 to include barriers, DVM, or WLU/WU.
