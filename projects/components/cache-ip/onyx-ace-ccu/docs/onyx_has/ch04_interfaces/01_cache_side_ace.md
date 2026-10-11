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

### RACK/WACK (N1)

The ACE definition doc records the family convention: RACK/WACK are auto-pulsed promptly at the adapter, even though the D2 subset needs no ordering semantics from them. The PRD N1 row cites Chinnakonda §7.20 and §14.39 to argue that RACK/WACK can be omitted if the data and snoop paths are ordered and not buffered past the coherency point. At 0.1 this is an open question: the definition doc's auto-pulse convention is the current contract, and the book's omission claim is recorded as the candidate rationale for changing it later. The contract decision is N1.

### CD/CR ordering tension

The AMBA ACE spec permits CR before CD and requires only per-channel ordering. The in-repo definition doc records a **family convention** decided with onyx D4: the cache-side adapter completes a transaction's CD beats before asserting its CR, so onyx's gather sees one fully-closed response at a time. This is stricter than ACE requires and is **our contract, not the spec's**.

The PRD's proposed invariant #6 states the opposite ordering: **CR before CD, CD-before-CDLAST, in-order CR/CD**. This is the natural ACE order (response indicates whether data will follow) and is simpler to verify against the spec.

At 0.1 the HAS records both conventions and does not pick one. The choice affects the gather state machine and the compliance checker, and must be resolved before RTL.

## What is fixed

- onyx is the owner of the ACE-shaped snoop port.
- The cache-side ports are ACE slave-side: AR/R/AW/W/B plus AC/CD/CR.
- The D2 subset is the working transaction set.
- The in-repo AMBA ACE Interface Definition is the normative contract.

## What is open

- RACK/WACK handling (N1).
- CD/CR ordering convention (family convention vs natural ACE order).
- Whether the decoder grows with D2 to include barriers, DVM, or WLU/WU.
