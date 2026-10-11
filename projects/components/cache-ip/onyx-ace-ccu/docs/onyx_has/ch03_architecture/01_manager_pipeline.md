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

# Manager Pipeline

**Stub: open until D1 and D2 close.** This chapter records the decision landscape for the front-end manager pipeline. No architecture is recorded here until D1 and D2 close.

## Candidates

| Decision | Candidates | What it drives |
|---|---|---|
| D1 Functional scope | CCU only — N ACE slave-side ports, one AXI4 master, one ACE-Lite IO port (recommended) vs CCU + address striping / multiple memory ports (interconnect territory; non-goal today) | block boundary, what "onyx done" means, whether the memory-side master is one port or many |
| D2 Transaction subset | `ReadShared` / `ReadUnique` / `CleanUnique` / `MakeUnique` / `WriteBack` / `Evict` (recommended) vs subset + barrier support vs full ACE incl. DVM | front-end decoder width, BFM scope, conformance matrix |

## What the decisions drive

D1 and D2 together fix the pipeline's inputs and outputs: how many ACE address channels enter the manager, what transaction types must be decoded, and whether the memory side is a single AXI4 master or a more complex interconnect. Until they close, the following are undecided:

- per-port buffering and skid/credit scheme;
- whether read and write paths share a single issue port into the serializer or remain separate;
- how `WriteBack`/`Evict` drains are merged with or separated from the response path;
- the ACE-Lite IO port shape, if D1 keeps it in scope.

## Background material

Chinnakonda, *Designing a Multiprocessor Cache Subsystem*, §7.2–7.4 give the `ARSNOOP`/`AWSNOOP` taxonomy: `ReadShared` for cacheable load misses, `ReadUnique` for store misses, `CleanUnique` for ownership requests when a store hits a Shared line, `MakeUnique` for whole-line ownership, `WriteBack` for dirty victims, and `Evict` for clean victims. §7.4 also introduces `WriteLineUnique` / `WriteUnique` for non-temporal / all-bytes-updated stores and coherent mem-copy; these are recorded as the scope-growth option N5, not part of the recommended D2 subset.

§10.2–10.3 discuss centralized vs. distributed manager organizations and the BIU as mapper. These sections confirm onyx as the BIU/manager block rather than an L2, and keep CCU-only the recommended v1 scope.

## Status

No architecture recorded. D1 and D2 must decide the functional scope and transaction subset before the manager pipeline can be drawn.
