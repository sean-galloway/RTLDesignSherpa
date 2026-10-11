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

# Snoop Fanout Port

## Decision status

**D7 is DECIDED (2026-10-05): onyx owns the AC/CD/CR-shaped snoop port.** This chapter records the fanout contract as real content at 0.1. The exact fanout target selection (broadcast vs directory-lite) is D3 and is still open; the pin contract is fixed.

## Pin contract

For each attached cache, onyx drives AC and receives CR/CD:

| Channel | Direction from onyx | Payload | Meaning |
|---|---|---|---|
| AC | out | `ACADDR`, `ACSNOOP[3:0]`, `ACPROT[2:0]` | "What state does this line have in you, and what should you do about it?" |
| CR | in | `CRRESP[4:0]` | The cache's answer: data transfer, error, dirty responsibility, shared indication. |
| CD | in | `CDDATA`, `CDLAST` | The line's data when CRRESP indicated it would come. |

Handshake rules mirror AXI4: VALID/READY, no combinatorial dependency of READY on VALID.

## Core ordering rules

- **CR and CD only after AC.** The snoop response and any snoop data must only be asserted after the `ACVALID`/`ACREADY` handshake.
- **In-order responses, in-order data.** CR responses must be returned in the same order as the AC addresses; CD data likewise. ACE permits multiple outstanding snoops; only per-channel ordering is required by the spec.
- **No snoop to the requesting master.** onyx must not drive an AC to the cache that issued the coherent transaction. This is a D10 compliance-checker rule and proposed invariant #7.

## Proposed invariants as the binding-forward liveness contract

The PRD §"Design invariants (proposed)" lists seven bedrock liveness rules mined from Chinnakonda Ch. 7/8/10/14. At 0.1 they are **PROPOSED**, not DECIDED; once the owner rules, they become the binding liveness contract for this interface.

1. **Snoop forward progress.** A snoop may wait only on (a) a same-address outstanding WB/Ev/WC/WE, or (b) a guaranteed-to-complete temporary block (e.g. a retired store completing after it has received ownership). It must never wait on an unrelated transaction or an unpredictable buffer-drain event.
2. **Snoops ignore WLU/WU entirely.** A snoop to the same address as a `WriteLineUnique`/`WriteUnique` is always allowed to make progress; the WLU/WU does not block it.
3. **Snoop responses never depend on WU/WLU completion.** Otherwise SI buffers full of interdependent WU/WLU traffic can deadlock.
4. **CD never blocks on WDATA.** The snoop-data return path must have independent forward progress; if it shares resources with ordinary writes, those resources must be credit-reserved for the WB/Ev/WC/WE family.
5. **Multi-copy-atomic stores.** A store is considered complete only after all ownership invalidations have been performed everywhere.
6. **CR before CD, CD-before-CDLAST, in-order CR/CD.** A snoop response indicates whether data will follow; data beats are in order and `CDLAST` marks the final beat; CR and CD keep the issue order of the ACs. (Note: this conflicts with the cache-side family convention in the AMBA ACE definition doc; see [Chapter 4.1](01_cache_side_ace.md).)
7. **No snoop to the requesting master.** Already a D10 compliance-checker rule; restated as a design invariant.

## What is fixed

- The AC/CD/CR pin contract is owned by onyx (D7).
- Per-channel ordering and the no-snoop-to-requester rule are binding.

## What is open

- D3: whether targets are selected by broadcast or by directory-lite state.
- D4: how responses are gathered and completion detected.
- N1: whether RACK/WACK are part of the cache-side ordering contract.
- N3/N4: fill-sourcing and CD-path independence details.
- The CD/CR ordering convention (see [Chapter 4.1](01_cache_side_ace.md)).
