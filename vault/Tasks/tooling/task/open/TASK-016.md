# TASK-016: fan out the 8 doc-example findings the widened gate surfaced

**Priority:** P3
**Status:** open
**Owner:** TBD
**Filed:** 2026-09-28

`bin/check_doc_examples.py` now scans beside-code `PRD.md` and `README.md`
(RLB BUG-005). That widening brought 79 more pages into scope and surfaced 8
fabricated examples, none of them in the unit that made the change:

| File | Example | Names |
|---|---|---|
| `projects/components/converters/README.md` | `axi4_to_apb4_convert` | M_APB_ADDR_WIDTH, M_APB_DATA_WIDTH, S_AXI_ADDR_WIDTH, S_AXI_DATA_WIDTH, m_apb_paddr |
| `projects/components/converters/README.md` | `axi_data_dnsize` | DUAL_BUFFER |
| `projects/components/converters/README.md` | `peakrdl_to_cmdrsp` | clk, cmd_addr, cmd_data, cmd_write, reg_addr |
| `projects/components/dmas/stream/regs/README.md` | `stream_regs` | ch0_ctrl_desc_addr, ch0_rd_burst, global_ctrl_enable, paddr, pclk |
| `projects/fpga-systems/boards/README.md` | `debounce` | CLK_FREQ_MHZ, DEBOUNCE_TIME_MS, i_clk, i_rst_n, i_signal_raw |

They are held by `BASELINE = 8` in that script so the widening could land
green. **The floor is filed debt, not a verdict.** Each finding needs its
OWNER to triage, because this gate cannot tell a stale example from a
deliberate one: the script's own comments record `axi4_dwidth_converter.md`
as a PLANNED-DESIGN page whose example describes a module that does not exist
yet. Some of the 8 may be that; some are probably stale renames.

Per Sean (2026-09-28, tooling TASK-004): an item that needs edits inside many
separate units is filed on each unit, or it never completes. This is the
parent; fan it out to converters, stream and fpga-systems.

**Done when:**

- [ ] each of the 5 rows is triaged by its owner: fixed, or marked illustrative
- [ ] `BASELINE` drops by one for each that closes
- [ ] `BASELINE` reaches 2 (the pre-existing rapids TASK-008/009 debt) or lower
