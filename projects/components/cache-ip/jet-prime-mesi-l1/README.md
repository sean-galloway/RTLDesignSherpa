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

# jet-prime — jet, forked to beat HPDcache

[`../jet-mesi-l1/`](../jet-mesi-l1/) copied whole at commit `2be919254`
(2026-11-12) with the `jet_prime_` prefix on every module, filelist, harness,
test and formal wrapper. jet itself is frozen: it is the baseline the
reference comparison
([`../docs/reference_l1_comparison.md`](../docs/reference_l1_comparison.md))
measured, and nothing in it moves. jet-prime is where the miss path gets
rebuilt.

## Why a fork

On the 64 KB read-lean thrash at depth 16 jet runs 10.7 cycles per
transaction to OpenHW HPDcache's 7.6, with more misses in flight (7 vs 3)
and a slower retire (20 vs 14 cycles per miss): after the MSHR the miss path
is serial -- one fill engine, one coherence transaction and one memory read
at a time in the pair fabric. The work item is
[jet-prime TASK-001](../../../../vault/tracking/projects/components/cache-ip/jet-prime-mesi-l1/task/active/TASK-001.md):
measure jet-prime without the fabric, then multiple outstanding fills, then a
pipelined fabric, with the DV and formal to carry them.

## What is and is not here

- `rtl/`, `dv/`, `formal/jet-prime/` (repo root): jet's, renamed. Root
  variable `JET_PRIME_ROOT`; filelist area `jet-prime` in
  `bin/filelists.toml`; tests `make clean-all && make
  run-all-{gate,func,full}-parallel` in `dv/tests`.
- The shared MESI core stays at [`../common-ip/`](../common-ip/) and is
  reached by `-f` include, exactly as jet reaches it.
- **No HAS/MAS copy.** jet's books
  ([HAS](../jet-mesi-l1/docs/jet_has/jet_has_index.md),
  [MAS](../jet-mesi-l1/docs/jet_mas/jet_mas_index.md)) describe jet-prime
  until the architecture diverges (TASK-001 step 2); module headers keep
  their `Documentation:` pointers into them. A second identical copy is the
  one nobody edits.
- Board measurement: the reference rig's cache slot,
  `projects/fpga-systems/Genesys2/cache-ip/ref` with `REF_CACHE_SEL=2`
  (jet-prime straight onto memory, snoop port tied off).

Binding requirements: [PRD.md](PRD.md).
