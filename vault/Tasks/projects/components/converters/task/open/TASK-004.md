# TASK-004: converters/README.md: three instantiation examples name parameters and ports the modules do not have

**Priority:** P3
**Status:** open
**Owner:** TBD
**Filed:** 2026-09-29 (fanned out from tooling TASK-016)

`bin/check_doc_examples.py` (widened 2026-09-28 to beside-code README.md and
PRD.md) reports three instantiation examples in
`projects/components/converters/README.md` that name parameters or ports the
module does not have. Run `python3 bin/check_doc_examples.py` for the live
list; as filed:

| Example | Names the module lacks |
|---|---|
| `axi4_to_apb4_convert` | M_APB_ADDR_WIDTH, M_APB_DATA_WIDTH, S_AXI_ADDR_WIDTH, S_AXI_DATA_WIDTH, m_apb_paddr |
| `axi_data_dnsize` (appears 4x) | DUAL_BUFFER |
| `peakrdl_to_cmdrsp` | clk, cmd_addr, cmd_data, cmd_write, reg_addr |

The gate cannot tell a stale rename from a deliberate illustration, which is why
this is filed on the unit and not fixed from tooling: the owner decides per
example. A stale example is fixed against the module header; a deliberate one
(a planned design, a sketch) is marked so on the page, the way
`axi4_dwidth_converter.md` states "Status: Planned - no RTL in this repository".

The findings are held by `BASELINE` in `bin/check_doc_examples.py` (7 as of
2026-09-29). **Drop it by one for each example that stops being reported**, in
the same commit as the fix -- the script prints "baseline can be lowered to N"
when it can.

**Done when:**

- [ ] each of the three examples compiles against its module header, or is
      marked illustrative on the page
- [ ] `BASELINE` lowered by the number that stopped being reported
