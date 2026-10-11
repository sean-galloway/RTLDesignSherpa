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

# System Context

## Where onyx sits

onyx is the coherence manager on the house AXI4 fabric. It consumes ACE transactions from attached caches on one side, issues AXI4 transactions toward memory on another side, and drives/receives the AC/CD/CR snoop channels to/from the peer caches on a third side. A fourth MonBus tap carries observation events without stalling the measured paths.

## Onyx rig with amber

```
CPU/STREAM0 --GAXI--> amber_ace0 --ACE--> onyx --AXI4--> memory
CPU/STREAM1 --GAXI--> amber_ace1 --ACE-->
```

In this rig, each `amber_ace` is an ACE master toward onyx and a snoop responder toward onyx. Coherent read misses become `ReadShared` or `ReadUnique`; write promotions become `CleanUnique` or `MakeUnique`; dirty evictions become `WriteBack`; clean evictions become `Evict`. Memory is on the far side of onyx; the caches do not talk directly to memory.

## Onyx rig with jet

The same topology applies with `jet_ace` instances once jet exists:

```
CPU/STREAM0 --GAXI--> jet_ace0 --ACE--> onyx --AXI4--> memory
CPU/STREAM1 --GAXI--> jet_ace1 --ACE-->
```

jet's internal lockup-freedom is invisible to onyx except that jet may present more concurrent transactions to serialize.

## What exists today around it

- `amber` is the first onyx-rig consumer. amber D4 and onyx D7 were decided together on 2026-10-05: onyx owns the ACE-shaped AC/CD/CR snoop port, and `amber` stays bus-agnostic internally behind a thin adapter.
- `jet` will reuse the same adapter contract; its J-rows must not be pre-decided by onyx.
- The in-repo AMBA ACE Interface Definition captures the ACE-shaped port contract and the D2 subset.
- `rtl/amba/ace/` already contains `axi4ace_master_rd/wr`, `axi4ace_slave_rd/wr`, `axi4ace_snoop_slave/master`, and `axi4ace_snoop_monitor_lite` movers — the transport layer for the three port kinds.
- The RDS-DV `axi4` BFM family will be extended with the `axi4ace` classes; the direction is fixed in PRD D10 but the classes are not yet implemented (RTLDesignSherpa-DV issue #86).

## Boundary with the caches

onyx does not know what is inside `amber` or `jet`. It sees only the ACE-shaped ports: AR/R/AW/W/B for coherent transactions, and AC/CD/CR for snoops. The caches see onyx as their memory system. This decoupling is the point of D7.
