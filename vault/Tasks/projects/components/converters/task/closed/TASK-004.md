# TASK-004: converters/README.md: three instantiation examples name parameters and ports the modules do not have

**Priority:** P3
**Status:** CLOSED 2026-09-29 (done)
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

---

## CLOSED 2026-09-29 -- three examples fixed against the headers; gate floor back to 0

- `axi_data_dnsize` (appeared 4x, all `.DUAL_BUFFER(...)`): the parameter no
  longer exists. One example kept, without it; the "dual-buffer" example, the
  "high-performance" configuration example, the throughput bullets, the
  hierarchy diagram annotation, the performance-table row, the design-decision
  paragraph and the "16 configs" test list (the test file holds 8) all said
  the mode still existed. Each now says it was removed and points at the MAS.
- `axi4_to_apb4_convert`: the example used `S_AXI_*`/`M_APB_*` parameters and
  flat `s_axi_awaddr`-style ports; the module's parameters are
  `AXI_*`/`APB_*` and its ports are PACKED channel beats (`r_s_axi_aw_pkt`,
  `w_s_axi_awready`, ...) with a packed APB command/response pair. The example
  now shows that shape and says `axi4_to_apb4_shim` is the flat-port wrapper.
- `peakrdl_to_cmdrsp`: `clk`/`rst_n`/`reg_*`/`cmd_addr`/`cmd_data`/`cmd_write`
  were never its ports; the example now lists `aclk`/`aresetn`, the
  `cmd_p*`/`rsp_p*` pair and the `regblk_*` passthrough cpuif from the header.

`bin/check_doc_examples.py`: 0 findings repo-wide; `BASELINE` 6 -> 0 with the
history in its comment. Any doc example naming a port its module lacks is NEW
again and blocks the commit.
