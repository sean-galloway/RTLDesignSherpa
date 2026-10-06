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

# onyx — Snoop-Based ACE Coherency Unit

Third IP of the [`cache-ip/`](../) gemstone family: the coherence
**manager**. [amber](../amber-mesi-l1/) and [jet](../jet-mesi-l1/) are the
caches — each one keeps its own lines coherent. onyx is what turns a pile of
coherent caches into a *system*: it receives AMBA ACE transactions from
attached caches, broadcasts snoops to the other caches, gathers their
responses, decides whether memory must be read, and serialises same-address
traffic. Named for the banded stone — parallel bands, stern and orderly;
the serializer.

Where amber's research question is "what is a correct snoopy cache" and
jet's is "what does lockup-freedom buy", onyx's is "**what does the manager
side cost**": the fanout, the gather, the adjudication, and the
same-address ordering, measured on the house fabric.

## Status

**Scaffolded 2026-10-05** — README + PRD only. `rtl/`, `dv/`, `docs/` are
placeholders; no RTL, no testbench, no register model. Decisions are OPEN in
[PRD.md](PRD.md) until they record a name and a date; so far **D7 is decided
(2026-10-05): onyx owns the ACE-shaped AC/CD/CR snoop port, and amber/jet
adapt to it** — decided together with amber D4. The wait that remains is
amber's pair rig (amber D10), onyx's first consumer.

## What it teaches / why it exists

- **Coherence as a fabric problem.** The cache side of MESI fits in one
  FSM; the manager side is where the protocol meets arbitration,
  fanout/gather, and ordering. onyx is the other half of the story amber
  and jet only gesture at.
- **ACE on the house fabric.** ACE is AXI4 plus three snoop channels
  (AC, CR, CD) — and
  this repo already speaks AXI4 with skid buffers, FIFOs, and BFMs. onyx is
  the natural extension of that infrastructure, not a foreign protocol
  bolt-on.
- **A worked example exists.** [`pulp-platform/culsans`](https://github.com/pulp-platform/culsans)
  (ETH Zürich / PlanV, Solderpad) adds an ACE port to CVA6's write-back
  D-cache and implements `ace_ccu_top`, a snoop-based CCU on AXI4. Read it;
  do not depend on it (last push 2024). The definition remains Arm IHI 0022.

## Goals (summary — the binding list is [PRD.md](PRD.md) §"Success criteria")

1. An AXI4+ACE coherency unit carrying N coherent cache masters (2–4) plus
   an ACE-Lite IO path, against the IHI 0022 transaction subset the PRD
   pins down.
2. Golden-model parity on a coherence trace suite run against
   amber + onyx (the D10 pair rig, grown to three blocks).
3. MonBus-instrumented: fanout, response-gather, memory-read elision, and
   serialization stalls observable in sim and on FPGA.
4. FPGA-cost characterisation the way the rest of the repo measures.

## Explicit non-goals (for onyx)

Cache storage of its own (it is a manager, not an L2 — the L2 temptation
is explicitly out), directory-based coherence, DVM and full barrier
semantics, multi-CCU systems, stash/dealloc features. See
[PRD.md](PRD.md) §"Non-goals".

## Layout

`rtl/`, `dv/`, `docs/` exist as placeholders. When RTL lands, this
directory follows the per-component layout of
[`../../dma-ip/stream/`](../../dma-ip/stream/README.md) (fub/macro/top split,
filelists registry, Pattern-B cocotb tests) and the mandatory rules in
[`../../CLAUDE.md`](../../CLAUDE.md) (reset macros, shared `sdpram_core` /
FIFO primitives, array syntax).

## References

- Arm, *AMBA AXI and ACE Protocol Specification* (IHI 0022), ACE chapters —
  ReadShared / ReadUnique / CleanUnique / MakeUnique / WriteBack / Evict,
  the AC snoop request, CR response bits (DataTransfer, IsShared,
  PassDirty), ACE-Lite, domain and barrier rules. Available from Arm without
  charge (direct PDF linked in the definition doc); not mirrored in-tree
  (Arm copyright). The in-repo working definition
  of the subset this family implements is
  [`../References/AMBA_ACE_Interface_Definition.md`](../References/AMBA_ACE_Interface_Definition.md),
  which cites IHI 0022 as normative.
- `pulp-platform/culsans` — CVA6 coherent WB cache (how a cache becomes a
  snoop responder: AC/CD/CR, snoop-vs-core tag arbitration, MOESI-ish
  states) and `ace_ccu_top` (the manager: broadcast, gather, memory-read
  decision, same-address serialisation).
- [`../References/`](../References/README.md) — the family reference
  library: the ACE interface definition (the amber D4 / onyx D7 contract),
  the Primer (transient states), gem5 Ruby SLICC protocol specs
  (`MESI_Two_Level` L1/dir split is the closest executable model), and the
  supporting papers.
