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

# Document Conventions

## Typographic Conventions

| Style          | Meaning                                                |
|----------------|--------------------------------------------------------|
| `monospace`    | Module names, parameter names, signal names, register names |
| **bold**       | Defined terms on first introduction; important warnings |
| *italic*       | Emphasis; placeholder values to be replaced            |
| `MEMTYPE`      | Top-level build-time parameter (all caps)              |
| `bank_machine` | RTL module name (lowercase with underscores)           |
| `tRC`, `tRCD`  | JEDEC timing parameters (as in JESD79-2 / JESD209-2)   |

## Numbering Conventions

- **Decimal** numbers have no prefix: `16`, `256`.
- **Hexadecimal** numbers are prefixed with `0x`: `0x800`, `0xFF`.
- **Binary** literals use Verilog notation when needed: `8'b1011_0010`.
- Bit ranges use the convention `[MSB:LSB]`, e.g., `dfi_address[19:0]`.

## Signal Direction Conventions

For DFI signals, direction is from the **memory controller's** perspective:

- **MC → PHY** — driven by the controller
- **PHY → MC** — driven by the PHY (sampled by controller)

For AXI signals, direction follows the standard AXI4 convention with the controller as the **slave**.

## Module Diagram Conventions

ASCII block diagrams in this document use the following conventions:

All diagrams in this document are rendered from Mermaid source files
in `assets/mermaid/`. The Mermaid source files (`.mmd`) are linked alongside
each rendered image so the diagrams can be edited and re-rendered.

- **Rectangular boxes with sharp corners** denote RTL modules.
- **Subgraph rectangles** group modules by functional layer.
- **Solid arrows** show primary data or control flow.
- **Dashed arrows** show configuration or observation paths (typically
  from the CSR slave to other modules).
- **Trapezoidal nodes** denote external interface ports (AXI, DFI, APB).

## Cross-Reference Conventions

- References to other chapters: "see Chapter 4"
- References to specific sections: "see §4.1" or "see Section 4.1"
- References to other documents: "see `pre-aspec.md`" (relative path)
- References to external standards: "per JESD79-2F §x.y"
