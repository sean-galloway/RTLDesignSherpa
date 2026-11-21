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

onyx is the coherence manager on the house AXI4 fabric: N cache-side ports toward the family's caches, one AXI4 master toward memory, and the AC/CR/CD snoop channels into every attached cache. It replaces jet-prime's pipelined pair fabric, which was the two-cache prototype of exactly this role.

## The rig as built

```
CPU/injector 0 --GAXI--> jet_prime_top 0 --AXI4 + sideband--> onyx_ccu --AXI4--> sdpram / bridge
CPU/injector 1 --GAXI--> jet_prime_top 1 --AXI4 + sideband-->   |
                                       <--AC / CR, CD --------- fanout and gather
```

Each jet-prime is an AXI4 master toward onyx (fills on AR/R, write-backs on AW/W/B) with its coherent request class on the D-8 sideband (`coh_req_*`) and its retire on `coh_done_*`; toward onyx it is also the ACE-shaped snoop responder (`m_axi_ac*`, `m_axi_cr*`, `m_axi_cd*`). Memory is reachable only through onyx.

## What exists around it

- `jet_prime_top` carries the sideband and the snoop port natively; no adapter sits between it and onyx (D7's snoop half is in the cache already; the ACE-front-side `ARSNOOP` flavor is the adapter's other half, not needed by any house cache).
- The in-repo AMBA ACE Interface Definition is the normative port contract; the RDS-DV `components.ace` BFMs implement it and were verified on onyx's gather shapes first.
- The Genesys2 reference rig measures onyx against the pair fabric it replaces (selections 3, 4, 5) and against HPDcache on the same injector, memory and bridge.
