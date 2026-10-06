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

# amber_pkg and Build-Time Geometry

## Parameter philosophy

amber is a parameter-only IP. All geometry, policy, and bus-width choices are elaboration parameters; there is no runtime register block. This matches the decision to put all visibility on MonBus rather than on an APB CSR.

## Core parameters

| Parameter | Default | Range / set | Meaning |
|---|---|---|---|
| `SETS` | 128 | 16–512 | number of sets |
| `WAYS` | 4 | 2–8 | associativity |
| `LINE_BYTES` | 64 | 32–64 | cache line size in bytes |
| `BUS_WIDTH` | 64 | 32–128 | CPU/fabric data width in bits |
| `REPL_POLICY` | `"LRU"` | `lru`, `tree_plru`, `fifo`, `random` | replacement policy |
| `WRITE_POLICY` | `"wb_wa"` | `wb_wa`, `wt_na` | write-back/write-allocate or write-through/no-allocate bring-up mode |
| `VICTIM_DEPTH` | 1 | 1–2 | dirty victim buffer depth |

: Table 5.0: Core elaboration parameters

## Derived quantities

- `SET_INDEX_WIDTH = $clog2(SETS)`
- `LINE_OFFSET_WIDTH = $clog2(LINE_BYTES)`
- `TAG_WIDTH = ADDR_WIDTH - SET_INDEX_WIDTH - LINE_OFFSET_WIDTH`
- State field adds 3 bits to the tag store (MESI now, MOESI headroom reserved).
- `FILL_BEATS = LINE_BYTES / (BUS_WIDTH/8)`

## Package contents

`amber_pkg` holds the parameter defaults, derived localparams, MESI state encodings, the replacement-policy enum, the write-policy enum, and the transaction-type encodings used by `amber_ace_issue`. The FSM oracles and the Python reference model both derive from the same gem5 Ruby `MESI_Two_Level` SLICC tables, so the encoding in `amber_pkg` is the single source of truth for RTL and DV.

## Rig is not a parameter

There is no `RIG` parameter. The pair rig and the onyx rig are two separate top modules sharing `amber_core` (Pre-HAS Q1, resolved 2026-10-06). Elaboration selects the rig by selecting the top file to compile and instantiate.
