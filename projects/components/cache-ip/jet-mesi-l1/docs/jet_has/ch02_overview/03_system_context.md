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

## Where jet sits

jet is a cache IP on the AMBA fabric, identical to amber at the boundary. It consumes GAXI transactions from a CPU or DMA master on one side and issues AXI4 or ACE transactions toward memory or a coherency manager on the other. A third ACE-shaped port receives snoops from a peer cache or from `onyx`. Observation leaves through a fourth MonBus tap. The difference from amber is internal: misses are no longer single-file.

## Pair rig (`jet` top)

```
CPU/STREAM --GAXI--> jet --AXI4--> memory
                        ^--AC/CR/CD-- peer jet
```

The pair rig is the measurement vehicle. Each `jet` has its own tag/data arrays and its own replacement state. Coherence is snoopy and peer-to-peer. With MSHRs, a cache can hold multiple outstanding misses to memory while still responding to snoops and hits to resident lines.

## Onyx rig (`jet_ace` top)

```
CPU/STREAM --GAXI--> jet_ace --ACE--> onyx --AXI4--> memory
                                      ^--AC/CR/CD--
```

In the onyx rig, `jet_ace` behaves as an ACE master toward `onyx` and a snoop responder toward `onyx`. Coherent read misses become `ReadShared` or `ReadUnique`; write promotions become `CleanUnique` or `MakeUnique`; dirty evictions become `WriteBack`; clean evictions become `Evict` (onyx D2 subset). The additional stress is that these transactions can now be concurrent inside the cache.

## Shared core, different tops

Both rigs instantiate the same `amber_core` plus the jet MSHR delta. The CPU-side front end, the tag/data arrays, the replacement engine, and the snoop responder are inherited. Only the fabric master stack and the coherent-transaction issuer differ, and that difference lives in the top wrapper, not in the core. The MSHR delta lives between the core and the fabric masters.
