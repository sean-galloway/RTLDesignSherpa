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

# Pending-Fill Bypass Register

**Module:** `amber_control` sub-block
**Status:** Pre-RTL micro-architecture contract

---

## Purpose

While a fill is outstanding, a snoop may arrive for the same line. The pending-fill bypass register lets `amber_control` answer that snoop with the post-fill state and any fill beats already received, before the tag and data arrays have been updated. This is the only place in amber where a line can be observed in a state that has not yet been committed to the arrays, so its correctness is a SymbiYosys target.

---

## Register Fields

| Field | Width | Meaning |
|-------|-------|---------|
| `pf_addr` | `ADDR_WIDTH - OFFSET_WIDTH` | Line address (tag + set index) of the fill. |
| `pf_state` | 3 | State that will be installed when the fill completes. |
| `pf_data_valid` | `FILL_BEATS` | Per-beat mask: bit[i] is 1 when fill beat i has been received. |
| `pf_active` | 1 | Register is valid and the fill is still outstanding. |

The register is loaded in `CTRL_MISS_FILL` when `amber_fill` is launched. `pf_state` is determined by the request type:

- Read miss to shared → `STATE_S`
- Read miss to exclusive → `STATE_E`
- Write miss (whole-line allocate) → `STATE_M`

`pf_data_valid` is updated as each R beat is accepted by `amber_fill`. The snoop responder can forward fill beats whose `pf_data_valid` bit is set; beats not yet received stall the CD channel until they arrive.

---

## Match Logic

A snoop matches the pending-fill bypass when:

```systemverilog
pf_active &&
(snoop_line_addr == pf_addr)
```

The line address is `{tag, set_index}`; the line offset is ignored. The kmap workbook contains a small optional bypass-match sheet, but the match is a single equality compare; the sheet is included only if it earns its place as a teaching aid.

---

## Timing

| Cycle | Event |
|-------|-------|
| `CTRL_MISS_FILL` entry | `pf_active` set, `pf_addr` and `pf_state` loaded, `pf_data_valid` cleared. |
| Each accepted R beat | Corresponding `pf_data_valid` bit set by `amber_fill` done-strobe. |
| Snoop arrives during fill | If match, `CRRESP` and CD beats sourced from bypass register; otherwise normal tag lookup. |
| `CTRL_FILL_WRITE` | Bypass register contents written to arrays; `pf_active` cleared. |
| `CTRL_REPLAY` | Original request now hits the installed line. |

The critical correctness property is **state-accuracy**: the bypass register must answer with the post-fill state, never the pre-fill (Invalid) state. A snoop that would invalidate the line after the fill must see the post-fill state and then be allowed to perform its invalidation in the normal snoop path.

---

## Snoop vs Fill Ordering

If a snoop arrives for the pending line and requires data transfer, the CD beats are sourced from whichever copy is available:

- If the beat has already been received (`pf_data_valid[i] == 1`), it is forwarded directly from the fill-path register.
- If the beat has not yet arrived, the snoop responder stalls on `cd_ready` until the beat arrives, then forwards it.

The fill still completes normally into the arrays after `RLAST`. The snoop does not cancel the fill; any state change caused by the snoop is applied after the fill commits.

---

**Last Updated:** 2026-10-06
