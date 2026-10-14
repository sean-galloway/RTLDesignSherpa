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

# Parameter Semantics

The generator resolves two classes of parameters: **generation-time** (fixed in the emitted module) and **elaboration-time** (left as `parameter` in the generated SystemVerilog).

## Generation-time parameters

These are baked into the module name, the instance names, and the address map comments.

| Parameter | Effect in emitted RTL |
|-----------|-----------------------|
| `num_masters` | Number of master APB interfaces, master-side `apb4_slave`/`apb5_slave` instances, and width of per-slave request/grant vectors. |
| `num_slaves` | Number of slave APB interfaces, slave-side `apb4_master`/`apb5_master` instances, and number of arbitration blocks. |
| `base_addr` | Stamped into `BASE_ADDR` default and the address-map comment. |
| `slave_size` | Stride between slaves; also sets the bit slice used for slave selection. Must be a power of two. |
| `master_versions` / `slave_versions` | Selects `apb4_*` vs `apb5_*` boundary modules and the presence of sideband/parity pins. |
| `enable_parity` | Adds APB5 parity ports when the corresponding port is APB5. |
| `name_suffix` | Appended to the module and file names (e.g., `_mixed`). |

: Generation-Time Parameters

## Elaboration-time parameters

The generated module exposes three parameters:

```systemverilog
module apbx_xbar_2to4 #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH / 8,
    parameter logic [ADDR_WIDTH-1:0] BASE_ADDR = 32'h10000000
) (
```

| Parameter | Typical use |
|-----------|-------------|
| `ADDR_WIDTH` | Widen or narrow PADDR to match a subsystem. |
| `DATA_WIDTH` | 32 for standard APB; 64 for wide APB variants. |
| `STRB_WIDTH` | Always `DATA_WIDTH / 8`; kept as a derived parameter for readability. |
| `BASE_ADDR` | Override the base address at instantiation time without regenerating the module. The address-map comment still reflects the generator's default. |

: Elaboration-Time Parameters

The number of masters and slaves is **not** parameterized: a 2×4 module cannot be instantiated as 2×8. Generate a new module instead.
