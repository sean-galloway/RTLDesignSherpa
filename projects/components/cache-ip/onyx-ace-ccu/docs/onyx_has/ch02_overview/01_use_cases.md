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

# Use Cases

## Three-block coherence with amber

The primary use case is the onyx rig: two `amber` instances plus `onyx` form a coherent three-block system. Each `amber_ace` issues the D2 subset (`ReadShared`, `ReadUnique`, `CleanUnique`, `MakeUnique`, `WriteBack`, `Evict`) to onyx; onyx fans out snoops, gathers responses, and either completes the transaction from peer-cache data or reads memory. This is the pair rig grown by one block, and it is the first deliverable that exercises onyx end-to-end.

```
CPU/STREAM0 --GAXI--> amber_ace0 --ACE--> onyx --AXI4--> memory
CPU/STREAM1 --GAXI--> amber_ace1 --ACE-->
```

## Three-block coherence with jet

The same topology applies once `jet` exists: two `jet_ace` instances plus `onyx`. The onyx interface contract does not change; jet's lockup-freedom is an internal cache delta. This use case is the future consumer that verifies the interface was defined broadly enough.

## Standalone testing with BFM caches

onyx is standalone-testable long before `amber_ace` or `jet_ace` exist. Pattern-B cocotb tests drive the cache-side ACE ports and the snoop fanout with the RDS-DV `axi4ace` BFM family, exactly the way `culsans' ace_ccu_top` can be exercised in isolation. This decouples manager verification from cache verification.

## The onyx rig as jet's future consumer

The onyx-rig topology is also the integration target for `jet_ace`. Jet's research question (what does lockup-freedom buy) is measured against the same onyx manager and the same memory path, so the onyx interface must not pre-decide jet's internal concurrency choices.
