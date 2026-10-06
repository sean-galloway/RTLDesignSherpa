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

## Where amber sits

amber is a cache IP on the AMBA fabric. It consumes GAXI transactions from a CPU or DMA master on one side and issues AXI4 or ACE transactions toward memory or a coherency manager on the other. A third ACE-shaped port receives snoops from a peer cache or from `onyx`. Observation leaves through a fourth MonBus tap.

## Pair rig (`amber` top)

```
CPU/STREAM --GAXI--> amber --AXI4--> memory
                        ^--AC/CR/CD-- peer amber
```

The pair rig is the gated deliverable (D10). Each `amber` has its own tag/data arrays and its own replacement state. Coherence is snoopy and peer-to-peer: when one cache misses on a line the other holds, the response is delivered through the ACE-shaped snoop port, not through memory. Dirty victims write back to memory over the plain AXI4 master.

## Onyx rig (`amber_ace` top)

```
CPU/STREAM --GAXI--> amber_ace --ACE--> onyx --AXI4--> memory
                                      ^--AC/CR/CD--
```

In the onyx rig, `amber_ace` behaves as an ACE master toward `onyx` and a snoop responder toward `onyx`. Coherent read misses become `ReadShared` or `ReadUnique`; write promotions become `CleanUnique` or `MakeUnique`; dirty evictions become `WriteBack`; clean evictions become `Evict` (onyx D2 subset). Memory is on the far side of `onyx`, not directly reachable by `amber_ace`.

## Shared core, different tops

Both rigs instantiate the same `amber_core`. The CPU-side front end, the tag/data arrays, the control FSM, the replacement engine, and the snoop responder are identical. Only the fabric master stack and the coherent-transaction issuer differ, and that difference lives in the top wrapper, not in the core.
