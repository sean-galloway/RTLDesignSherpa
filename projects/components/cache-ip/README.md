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

# Caches

Research-oriented cache IP. Each IP carries a sedimentary-gemstone codename —
the thematic counterweight to the igneous-rock memory-controller family in
[`../mem-ctrl-ip/`](../mem-ctrl-ip/), whose volcanic names (pumice, scoria,
andesite) track JEDEC-era density the way gemstone names here track cache
behavior: **amber** preserves and stores (the blocking cache — correct,
quiescent, holding its line), **jet** is fossilized wood and jet-fast (the
lockup-free cache — everything still moving while a miss is in flight),
**onyx** is the banded stone — parallel bands, stern and orderly; the
serializer that holds same-address traffic in strict order.

The codename is the RTL identifier prefix and the module/package prefix
(`amber_*`, `jet_*`); the DIRECTORY is the compound `<codename>-<scope>` form,
mirroring the memory-controller convention — `amber-mesi-l1/`, not `amber`.
The bare codename is how an IP is referred to in prose; the compound form is
canonical anywhere a directory names one.

## Members

| Directory | Codename | Scope | RTL prefix | Status |
|---|---|---|---|---|
| [`amber-mesi-l1/`](amber-mesi-l1/) | **amber** | Blocking MESI snoopy L1 cache — the research baseline | `amber_*` | Scaffolded — README + PRD only, no RTL |
| [`jet-mesi-l1/`](jet-mesi-l1/) | **jet** | Lockup-free (MSHR) MESI snoopy L1 — the non-blocking follow-on to amber | `jet_*` | Scaffolded — README + PRD only, no RTL |
| [`onyx-ace-ccu/`](onyx-ace-ccu/) | **onyx** | Snoop-based ACE coherency unit — the coherence manager over the house AXI4 fabric | `onyx_*` | Scaffolded — README + PRD only, no RTL; waits behind amber's pair rig (amber D10); D7 decided 2026-10-05 — onyx owns the ACE-shaped snoop port |

The design intent: **amber** establishes the coherence protocol, snoop
transport, storage arrays, and observation fabric with the simplest possible
miss handling (a miss blocks); **jet** keeps all of that and adds miss-status
holding registers, hit-under-miss, and miss merging — so the performance
delta between the two is itself the research artifact. **onyx** is the
manager that makes the caches a system on real AMBA plumbing: an Arm-ACE
coherency unit on the house AXI4 fabric (the `pulp-platform/culsans` shape)
that broadcasts snoops, gathers CR responses, decides when memory must be
read, and serialises same-address traffic — the third side of the research
(caches both sides of a snoop, then the fabric between them). Opal stays
unclaimed until a concrete follow-on (victim cache) earns it.

Family interface decision, 2026-10-05: **cache-ip is ACE-shaped.** onyx owns
and defines the AC/CD/CR snoop-port contract; amber and jet stay
bus-agnostic internally and speak it through a thin adapter (amber D4, onyx
D7 — decided together). Any future cache-ip member adopts the same port
shape by inheritance, so a real ACE interconnect can replace onyx (or the
custom bus around it) without touching cache RTL.

Both IPs are built to be watched: MonBus checkers and perf counters observe
hits, misses, snoops, and evictions in simulation and on board, and the
trace-driven [cache simulator](../../../bin/apps/cache_sim/) app models the
same policy space for sim-vs-RTL hit-rate cross-checks.

Per-IP detail lives in each directory's `README.md` and `PRD.md`. The
per-component layout convention this directory will follow once RTL lands:
[`../dma-ip/stream/README.md`](../dma-ip/stream/README.md).
