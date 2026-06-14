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

# Module Hierarchy

The controller is decomposed into 17 RTL modules under a single top-level wrapper. Each is described in detail in Chapter 3.

## Hierarchy Tree

![Module Hierarchy](../assets/mermaid/02_module_hierarchy.png)

**Source:** [02_module_hierarchy.mmd](../assets/mermaid/02_module_hierarchy.mmd)

## Module Functional Groupings

For documentation and review purposes, the modules group naturally into seven functional layers:

| Layer                  | Modules                                            |
|------------------------|----------------------------------------------------|
| AXI Frontend           | `axi4_slave`, `addr_mapper`                        |
| Transaction Buffering  | `txn_queue`                                        |
| Scheduling             | `scheduler`, `page_predictor`                      |
| Bank State + Timing    | `bank_machine`, `xbank_timers`                     |
| Refresh + Power        | `refresh_mgr`, `power_state`                       |
| Initialization         | `init_engine` (with embedded step_table)           |
| Command Output         | `cmd_encoder`, `gear_out`                          |
| Data Paths             | `wdata_path`, `rdata_path`                         |
| PHY Interface          | `dfi_master`                                       |
| Configuration          | `csr_slave`                                        |

Chapter 3 follows this grouping (one section per functional layer).

## Memtype-Conditional Modules

Three modules contain memtype-conditional logic that is selected at elaboration:

- **`cmd_encoder`** — instantiates either `ddr2_encoder` or `lpddr2_encoder` based on `MEMTYPE`.
- **`init_engine`** — its step_table ROM is loaded from either `ddr2_init_steps_pkg` or `lpddr2_init_steps_pkg`.
- **`power_state`** — handles Self-Refresh (DDR2) or Deep Power Down (LPDDR2) entry sequences.

Synthesis dead-code-eliminates the unused paths. The same RTL source supports both targets.

## Optional Modules

One module is parameter-gated and may be entirely absent from the synthesized design:

- **`page_predictor`** — only instantiated when `PAGE_POLICY == HAPPY_HYBRID`. For `OPEN` or `CLOSE` policies, the predictor module is not synthesized.
