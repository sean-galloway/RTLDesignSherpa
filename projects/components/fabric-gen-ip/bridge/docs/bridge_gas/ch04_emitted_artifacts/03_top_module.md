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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Top Module

The top module (`<bridge_name>.sv`) is the integration shell. It instantiates the subtractive catch-all, every master adapter, the crossbar, and every slave adapter.

## Module signature

The top module takes **no parameters**. All widths are fixed at generation time and come from the package:

```systemverilog
module bridge_mix_e
    import bridge_mix_e_pkg::*;
(
    input  logic aclk,
    input  logic aresetn,

    // Master 0: cpu_axi3 (rw)
    input  logic [3:0] cpu_axi3_awid,
    input  logic [31:0] cpu_axi3_awaddr,
    // ... all AXI3/AXI4/APB/Wishbone channels per port protocol ...

    // Slave 0: ddr_axi3
    output logic [5:0] ddr_axi3_awid,
    // ...

    // Unmapped-address status (subtractive slave)
    output logic        unmapped_irq,
    output logic [31:0] unmapped_addr,
    output logic [7:0]  unmapped_count,
    input  logic        unmapped_clear
);
```

The exact port list is derived from the port protocol, channel subset, and widths.

## Internal structure

The top module contains:

1. **`axi4_subtractive_slave`** — always present, terminates unmapped addresses with DECERR and exposes the `unmapped_*` status pins.
2. **Master adapter instances** — one per master, named `<name>_adapter`.
3. **Crossbar instance** — `<bridge_name>_xbar`, wired to all adapter outputs.
4. **Slave adapter instances** — one per external slave plus one `subtractive_adapter` for the catch-all.

## Excerpt: subtractive catch-all instantiation

```systemverilog
axi4_subtractive_slave #(
    .AXI_ID_WIDTH   (6),
    .AXI_ADDR_WIDTH (32),
    .AXI_DATA_WIDTH (64),
    .AXI_USER_WIDTH (1),
    .UNIT_ID        (8'd3),
    .AGENT_ID       (16'h5B00)
) u_subtractive (
    .aclk          (aclk),
    .aresetn       (aresetn),
    // ... AXI channels ...
    .o_hit_irq     (unmapped_irq),
    .o_hit_addr    (subtractive_hit_addr),
    .o_hit_count   (unmapped_count),
    .i_hit_clear   (subtractive_hit_clear)
);
```

## Excerpt: adapter wiring pattern

```systemverilog
cpu_axi3_adapter u_cpu_axi3_adapter (
    .aclk(aclk),
    .aresetn(aresetn),
    .cpu_axi3_awid(cpu_axi3_awid),
    // ... external AXI3 pins ...
    .slave_select_aw(cpu_axi3_slave_select_aw),
    .bridge_id_aw(cpu_axi3_bridge_id_aw),
    .slave_select_ar(cpu_axi3_slave_select_ar),
    .bridge_id_ar(cpu_axi3_bridge_id_ar),
    // ... width-specific internal paths ...
);
```
