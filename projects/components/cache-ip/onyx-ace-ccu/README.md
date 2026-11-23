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

**Built 2026-11-21 (onyx TASK-001, steps 1, 2, 4, 6).** The PRD's D rows
were decided on 2026-11-20 (v0.7) and `rtl/top/onyx_ccu.sv` is the v1
core: jet-prime's pipelined pair fabric generalized to `N_PORTS` (2 to 4)
under those rulings -- broadcast snoop, tagged gather, per-line
serialization, adjudicated data source with the memory read alongside the
snoop or deferred (`DEFER_AR`). Two jet-primes behind it pass jet-prime's
whole pair-rig grid unchanged (`dv/tests/test_onyx_pair_rig.py`); the ACE
snoop BFMs were verified on the gather shapes first
(`dv/tests/test_onyx_snoop_gather_rig.py`); the formal argument at two
ports is `formal/onyx/onyx_ccu`; the Genesys2 reference rig carries it as
`REF_CACHE_SEL` 4 and 5. Observation (D9) is built: `onyx_top` composes
the unit with `onyx_monlite` (house MonBus packets from the unit's event
taps, an observer that reports what it drops) and `onyx_counters` (six
exact counts: transactions, lines supplied, memory reads, reads wasted,
absorptions, write-backs), held to the pair-rig TB's model in sim and read
on the reference rig through the tally chain and the harness CSR. The
observer carries the ocelus layers of masks (observer, packet type, event
class, error code, port; `ONYX_MON_CTRL` / `ONYX_MON_MASK` on the rig,
reset to the rare class only) and the content filter, an address window
on the transaction (`ONYX_MON_WIN_LOW` / `HIGH`), because the house MonBus
is a low-bandwidth event channel and the integrator picks what to transmit
(onyx ISSUE-001).
Not yet built: the ACE-Lite IO port (D1), an `ARSNOOP` front end. Tracker:
[`vault/tracking/projects/components/cache-ip/onyx-ace-ccu/`](../../../../vault/tracking/projects/components/cache-ip/onyx-ace-ccu/INDEX.md);
architecture: [docs/onyx_has](docs/onyx_has/onyx_has_index.md).

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

- `rtl/top/onyx_ccu.sv` with `rtl/filelists/onyx_ccu.f` (area `onyx`,
  root `ONYX_ROOT` in `bin/filelists.toml`); the shared `l1_pkg` by
  `-f` include. `rtl/top/onyx_top.sv` (`onyx_top.f`) composes it with
  `rtl/fub/onyx_monlite.sv` and `rtl/fub/onyx_counters.sv` on the event
  taps; `rtl/includes/onyx_pkg.sv` holds the event codes.
- `dv/tb/` the harnesses (`onyx_pair_rig_tb.sv`: jet-prime's pair rig
  with onyx in the fabric's place; `onyx_snoop_gather_rig_tb.sv`: the
  BFM-against-BFM gather rig), `dv/tbclasses/`, `dv/tests/` (Pattern B;
  `make clean-all && make run-all-{gate,func,full}-parallel`).
- `formal/onyx/onyx_ccu/` (repo root): the safety harness and run file.
- `docs/onyx_has/`: the architecture book.

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
