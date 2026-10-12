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

# Claude Code Guide: Delta (AXI-Stream Crossbar Generator)

**Version:** 1.0
**Last Updated:** 2026-10-12
**Purpose:** AI-specific guidance for the Delta component (fabric-gen-ip)

---

## Quick Context

**What:** Delta is a **Python-based AXI4-Stream (AXIS) crossbar generator**.
It emits a single self-contained SystemVerilog module per configuration — a
flat M×N stream crossbar routing `s_axis_*` masters to `m_axis_*` slaves.

**Status:** Active development. RTL generates and simulates; there is **no
`dv/` test suite yet** (the CocoTB suite is the known TODO). Re-homed from
`noc-ip/delta` on 2026-10-12 — the move did not change any behavior.

**Your Role:** Help users generate, parameterize, and validate AXIS crossbars;
keep generated RTL and this documentation in sync.

**Not this component:** the aspirational DELTA mesh NoC design draft
(routers, virtual channels, XY routing) lives separately at
`projects/components/noc-ip/delta_spec/` — **no NoC RTL exists**. When "delta"
comes up without qualification, this crossbar generator is what is meant.

---

## How It Actually Works (verified against `rtl/delta_axis_flat_4x16.sv`)

- **Route decode:** the target slave comes straight from `s_axis_tdest`
  (`DEST_WIDTH` bits) — there is **no address map**.
- **Arbitration:** per-slave round-robin; the grant is **packet-atomic** —
  once granted, a master holds the slave until `TLAST`.
- **Data path:** `TDATA/TVALID/TLAST/TDEST/TID/TUSER` crossbar mux is
  **combinational**; the **grant** is the registered stage.
- **Backpressure:** `TREADY` from the granted slave is steered back to the
  granted master only.
- **Optional flavors (2026-10-12, default off, default output byte-identical):**
  `TSTRB` (`--strb-width`) byte qualifiers, and AMBA 5 `TWAKEUP`/`TPARITY`
  (`--amba5`, `--parity-width` default DATA_WIDTH/8) so generated crossbars
  port-match `rtl/amba/axis4/*` and `rtl/amba/axis5/*`. TWAKEUP is TDEST-decoded
  (OR per slave) and may assert before TVALID, per the AMBA 5 hint semantics.
- **Optional:** packet counters.

Parameters on the generated module: `DATA_WIDTH`, `DEST_WIDTH`, `ID_WIDTH`,
`USER_WIDTH`, `NUM_MASTERS`, `NUM_SLAVES`.

---

## Repository Map

| Path | What |
|---|---|
| `bin/delta_generator.py` | The generator (`DeltaConfig`, `DeltaFlatCrossbar`, CLI) |
| `bin/delta_performance_model.py` | Analytical + simulation performance model |
| `bin/complete_tree_generator.py` | Retired tree-topology prototype (kept for history) |
| `rtl/delta_axis_flat_4x16.sv` | Reference generated crossbar (checked in) |
| `rtl_test/*.sv` | Generated variants (2×4, 3×8, 2×16, 4×16) |
| `rtl_test/delta_axis_flat_2x4_strb_amba5.sv` | Rich-flavor example (TSTRB + TWAKEUP/TPARITY) |
| `rtl/filelists/*.f` | Filelists (`$REPO_ROOT`-relative) |
| `README.md` / `PRD.md` / `QUICK_START.md` | Product docs (PRD REQ-GEN-002 is flat-only since 2026-10-12) |
| `delta_index.md` | Crossbar doc index |
| `TREE_TOPOLOGY_TEST_RESULTS.md` | Historical results for the retired tree path |

---

## Critical Rules

1. **Flat only.** `--topology tree` (and `both`) prints "not yet implemented
   in framework version". Do not promise tree generation; REQ-GEN-002 was
   amended 2026-10-12.
2. **Regenerate, don't hand-edit.** `rtl/delta_axis_flat_4x16.sv` and the
   `rtl_test/` variants are generator outputs. Fix `bin/delta_generator.py`
   and re-emit; note `--topology tree` was retired — regenerate with `flat`.
3. **AXIS only.** No AXI4/AXI4-Lite/APB conversion here (PRD non-goal). For
   memory-mapped fabrics see siblings `../bridge/` and `../apbx-xbar/`.
4. **Filelist paths** in `rtl/filelists/*.f` are `$REPO_ROOT`-relative — keep
   them working from any cwd.
5. **Do not resurrect the NoC** (`noc-ip/delta_spec/`) unless the owner
   explicitly asks for NoC work.

---

## Common Tasks

```bash
# Generate a fresh crossbar
python3 bin/delta_generator.py --topology flat --masters 4 --slaves 16 \
    --data-width 64 --output-dir rtl/

# Rich flavor: TSTRB + AMBA 5 sidebands (matches rtl/amba/axis4 + axis5)
python3 bin/delta_generator.py --topology flat --masters 2 --slaves 4 \
    --data-width 32 --strb-width 4 --amba5 --output-dir rtl_test/

# Performance comparison (historical flat/tree data retained)
python3 bin/delta_performance_model.py --topology compare
```

---

**Maintained By:** RTL Design Sherpa Project
