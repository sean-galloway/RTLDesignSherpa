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

# RTL Landing Diff Procedure

## When RTL Lands

After the first RTL commit for a module, update the corresponding sheet in [`gen_amber_contracts_kmaps.py`](../../gen_amber_contracts_kmaps.py):

1. Add citations to the RTL file and line numbers in the `CITES` registry.
2. Replace `rtl_sop=None` with the actual RTL expression as a sum-of-products string.
3. Re-run the generator.
4. Review each sheet's verdict.

First landing (2026-10-06): the snoop CRRESP / next-state decode exists as `l1_pkg` functions + `l1_snoop_kmap`. See [01_kmap_verdicts.md](01_kmap_verdicts.md) for why its sheets record truth-table PASS but the SOP-literal diff is classified RTL-REDUNDANT; the procedure above applies to every sheet still at `rtl_sop=None`.

## Diff Checklist

For every sheet that reports **RTL-DIFFERS**:

- Is the difference a deliberate redundancy? Re-label as RTL-REDUNDANT and add a note.
- Is an unstated invariant doing work? Add it as a checked `relation` and re-derive.
- Is the RTL expression wrong? File a bug and fix it.

For every sheet that reports **RTL-REDUNDANT**:

- Does the redundancy serve timing closure? Keep it and document.
- Does the redundancy serve readability? Keep it if the cost is small.
- Is it accidental? Simplify the RTL.

## Regression Rule

The generator is part of the CI check for amber. Any RTL edit that moves or changes a cited expression must cause the generator to fail loudly, not silently publish a stale map. This is enforced by the `CITES` registry in `gen_amber_contracts_kmaps.py`.

## Task 14 RTL-vs-MAS Diff Notes (2026-10-11)

The following differences between the landed RTL and the MAS text were evaluated during the Task 14 kmap verdict sweep. All of them map onto the known errata pinned in the plan; **no NEW differences were found** in the kmap-relevant scope.

| # | MAS text / figure | Landed RTL | Verdict class | Known erratum |
|---|-------------------|------------|---------------|---------------|
| 1 | ch01 and ch03 describe tag/data arrays as "built from `sdpram_core`" | Arrays are per-way inferred RAMs in the `sdpram_core` internal idiom; the literal `sdpram_core` module is a FUB/AXI burst slave and is the wrong shape for a same-cycle multi-way tag compare. The Task 9 ruling keeps the landed arrays and satisfies D11's queue requirement with the two `gaxi_fifo_sync` instances. | RTL-DIFFERS (documentation wording) | MAS ch01↔ch03 `sdpram_core` wording contradiction |
| 2 | ch02 port list / handshake table uses `ctrl_snoop_crresp`, `ctrl_snoop_cddata`, `ctrl_snoop_cdlast` | `l1_control` and `l1_snoop_resp` use `ctrl_crresp`, `ctrl_cddata`, `ctrl_cdlast`, plus the streaming handshake `ctrl_cdvalid`/`ctrl_cdready`. | RTL-DIFFERS (naming) | ch02 `ctrl_snoop_*` → landed `ctrl_*` names (RTL wins) |
| 3 | ch02/05 shows a single-cycle `victim_load` that loads a full line | The data-array port is `BUS_WIDTH` wide (MAS ch03), so a full line cannot be loaded in one cycle. `l1_control` gathers the dirty victim line over `FILL_BEATS` port-A read cycles and uses `ctrl_victim_load` as the final-beat strobe. | RTL-DIFFERS (timing) | ch02 single-cycle `victim_load` → gather over `FILL_BEATS` with final-beat strobe (D-5) |
| 4 | ch02 FSM table lists `CTRL_IDLE`, `CTRL_LOOKUP`, `CTRL_HIT_RD`, `CTRL_HIT_WR`, `CTRL_MISS_VICTIM`, `CTRL_MISS_DRAIN`, `CTRL_MISS_FILL`, `CTRL_FILL_WRITE`, `CTRL_REPLAY`, `CTRL_SNOOP`, `CTRL_ERROR` | `l1_pkg` and `l1_control` implement an additional stable state `CTRL_INIT` for the post-reset init walk that writes `STATE_I` to every way before the first lookup. | RTL-DIFFERS (FSM states) | ch02 FSM table missing `CTRL_INIT` (D-3) |
| 5 | ch01/02 top-level port list omits the coherence sideband | `amber_top` and `amber_ace_top` expose the pair-rig coherence sideband `coh_req_{valid,addr,type}` (DECISION D-8). | RTL-DIFFERS (port list) | ch01/02 port list missing the coherence sideband |
| 6 | Plan / early testplans reference `dv/tests/fub/` | All amber unit and macro suites live in the flat `dv/tests/` directory, consistent with the repo convention and the plan's DECISION D-13. | RTL-DIFFERS (paths) | `dv/tests/fub/` → flat `dv/tests/` paths |

### Design evolutions that are not kmap diffs

The following landed design choices are recorded here for completeness but do not change the truth table of any K-map sheet:

- **DECISION D-2 (leaf modules):** `l1_pending_fill_bypass` and `l1_victim` are built as leaf modules (not inline control logic) so Task 13 can prove them standalone. The port-level contract matches the MAS fields; the leaf boundary is an RTL-REDUNDANT structural choice.
- **DECISION D-6 (fill/drain queues):** `l1_fill` uses a `gaxi_fifo_sync` (DEPTH=4) to stage R beats so snoop-imposed port-A stalls never drop `fub_axi_rready`; `l1_drain` forwards victim beats directly because the `axi4_master_wr` wrapper's W skid absorbs backpressure. This changes the pre-RTL fill/drain handshake sketch but does not affect the control-path K-map.
- **DECISION D-9 (RANDOM policy):** `l1_repl` RANDOM uses an LFSR; `cache_sim` uses mulberry32. Exact bit-for-bit parity is impossible; the parity suite records this caveat. This is outside the K-map sheets.

---

**Last Updated:** 2026-10-11 (Task 14 RTL-vs-MAS diff sweep)
