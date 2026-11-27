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

## Two jet-primes behind onyx

The built use case (onyx TASK-001, 2026-11-21): two `jet_prime_top` caches plus `onyx_ccu` form a coherent three-block system with one shared memory behind the manager -- the jet-prime pair rig with onyx in the pair fabric's place.

```
CPU/injector 0 --GAXI--> jet_prime_top 0 --AXI4 + D-8 sideband--> onyx_ccu --AXI4--> memory
CPU/injector 1 --GAXI--> jet_prime_top 1 --AXI4 + D-8 sideband-->   |  AC/CR/CD to both caches
```

Each cache is an AXI4 master toward onyx with its request class on the D-8 sideband, and an ACE-shaped snoop responder toward onyx. Coherent read misses are `ReadNotSharedDirty` or `ReadUnique`, write promotions `CleanUnique`, dirty evictions `WriteBack`. This rig runs jet-prime's own pair-rig testbench unchanged (`dv/tests/test_onyx_pair_rig.py`) and sits in the Genesys2 reference rig as selections 4 and 5.

## Three and four caches

`N_PORTS` reaches 4 (D11). The core-alone rig (`dv/tests/test_onyx_core_rig.py`) runs `onyx_ccu` at N_PORTS 2, 3 and 4 with BFM caches; the snoop-gather rig exercises the BFM side of the fanout at three and four ports. Formal: `formal/onyx/onyx_ccu_n3` and `_n4` (one N-generic harness, commit c6273863b): cover 41/41 and `prove_fast` (17 properties, BMC depth 32) PASS at both N, 19 mutants fail at both N, the N = 3 `prove` (29 properties, depth 20) PASS; the N = 4 `prove` and both `prove_book` runs: running, see onyx TASK-001. A three-cache rig with real caches is not built.

## Standalone testing with BFM caches

The snoop fanout and gather were first met by BFMs alone: `dv/tests/test_onyx_snoop_gather_rig.py` puts N RDS-DV snoop-master BFMs (the fanout) against N snoop-slave BFMs (the caches) through the house ACE transport, before any onyx RTL existed (TASK-001 step 1). A core-alone rig with BFM caches on the AXI4 side is a later TASK-001 step.

## amber and jet

amber and jet carry the same snoop port and the same sideband contract and would attach the same way; both are frozen baselines, and jet-prime is the cache the family measures against HPDcache, so it is the one behind onyx.
