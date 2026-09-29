# TASK-016: fan out the 8 doc-example findings the widened gate surfaced

**Priority:** P3
**Status:** CLOSED 2026-09-29 (done)
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

---

## CLOSED 2026-09-29 -- fanned out; BASELINE 8 -> 7

The five rows went to their owners, except one that had no owner lane:

| Row | Where it went |
|---|---|
| converters/README.md, 3 examples (`axi4_to_apb4_convert`, `axi_data_dnsize`, `peakrdl_to_cmdrsp`) | **converters TASK-004** |
| dmas/stream/regs/README.md, `stream_regs` | **stream TASK-015** |
| fpga-systems/boards/README.md, `debounce` | **fixed in place** -- `projects/fpga-systems` has no task lane. The example named a `CLK_FREQ_MHZ`/`DEBOUNCE_TIME_MS` pair and `i_clk`/`i_rst_n`/`i_signal_raw`/`o_signal_clean` that `rtl/common/debounce.sv` never had; it now shows the real header (N, DEBOUNCE_DELAY, PRESSED_STATE; clk, rst_n, long_tick, button_in, button_out), wired the way NexysA7/cdc_counter_display wires it. |

`BASELINE` is 7 and its comment says why. The two filed items each carry the
instruction to lower it in the same commit as their fix; the parent's third
criterion (BASELINE reaches 2) is therefore theirs to finish, and this item
closes as the fan-out it was filed to be (Sean, 2026-09-28: unit edits are
filed on the unit, or they never complete).
