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

# DV Rigs

**Location:** `projects/components/cache-ip/onyx-ace-ccu/dv/` (Pattern B:
`tb/` harnesses, `tbclasses/`, `tests/`). Run through the area Makefile
from clean (`make clean-all && make run-all-{gate,func,full}-parallel`);
method in `vault/handbook/dv/running-regressions.md`. Results per run are
in onyx TASK-001.

| Rig | Harness | What drives onyx | What it is for |
|---|---|---|---|
| Snoop-gather rig | `tb/onyx_snoop_gather_rig_tb.sv`, `tests/test_onyx_snoop_gather_rig.py` | RDS-DV snoop master BFMs (the fanout) against snoop slave BFMs (the caches), through the house ACE transport; no onyx RTL | step 1: the BFMs and the CRRESP matrix verified on onyx's gather shapes at N 2 to 4 |
| Pair rig | `tb/onyx_pair_rig_tb.sv`, `tests/test_onyx_pair_rig.py` | two real `jet_prime_top` caches, one shared memory, the IO port driven by RDS-DV ACE master BFMs | jet-prime's pair-rig TB unchanged against onyx (N_PORTS 2): the lockstep model with the fabric rules, ACE compliance scoring, the IO scenarios, the counters held to the model and the observer to honesty |
| Core-alone rig | `tb/onyx_core_rig_tb.sv`, `tests/test_onyx_core_rig.py` | N MESI cache models on the framework BFMs (AXI4 masters, a snoop slave with a custom handler, the sidebands per cycle), a BFM memory; the IO port tied idle | every class onyx decodes, WriteClean included, at N 2 to 4 and both `DEFER_AR` modes |

: Table 5.3: onyx DV rigs

## What each rig reaches that the others do not

- **The pair rig** is the only one with real caches: jet-prime's own
  pre-AR rule, write-back buffer and killed upgrades, and the IO port. It
  runs at N_PORTS 2 only.
- **The core-alone rig** is the only one at N_PORTS 3 and 4 with traffic
  through `onyx_ccu`, the only one that drives WriteClean, and the one
  that found onyx BUG-001 and BUG-002 (and, at its full level, BUG-003).
  Its caches answer under the cache-side obligations HAS Chapter 4.1
  writes down.
- **The snoop-gather rig** has no onyx RTL; it is the BFM's qualification.

## Checks that live in the RTL

`onyx_ccu.sv:1606-1663` (simulation only, `translate_off`): the AR's line
and length against its slot, a memory read of a line while a write to it
is in flight (reads whose bytes are used), a memory beat for no read, two
slots on one line, a CD beat with no snoop outstanding, a second
DataTransfer for one slot, a pending-queue overflow, and the IO port's v1
contract (ReadOnce only, full-width INCR within one line; WriteUnique /
WriteLineUnique within one line). They are `$error` reports, not
assertions in the RTL proper (handbook `design/no-assertions-in-rtl.md`).

## The configurations simulated

The rigs' parameter grids are their test files' `generate_params()`; the
built configurations are listed in Chapter 6.
