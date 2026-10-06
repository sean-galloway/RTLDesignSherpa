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

## Signal naming

- `fub_*` — the flat upstream-facing side of a house AXI/ACE wrapper or adapter (e.g., `fub_axi_araddr`, `fub_acaddr`).
- `m_*` — the master-facing side toward the fabric or peer (e.g., `m_axi_araddr`, `m_axi_acaddr`).
- `s_*` / `i_*` / `o_*` — used for local module ports where the house convention prefers it.
- Active-low resets are named `rst_n` inside project components and `aresetn` on AMBA-facing pins, per the repo's reset convention.

## Numbering and bases

- Addresses and data widths are decimal unless prefixed with `0x`.
- Bus bit ranges use Verilog-style `[MSB:LSB]`.
- Array dimensions use the house `[DEPTH]` unpacked syntax, not `[0:DEPTH-1]`.

## Citation discipline

- PRD rows are cited as `amber Dn` (e.g., `amber D1`).
- Pre-HAS feature sketches are cited as `Fn` (e.g., `F9`).
- `onyx` rows are cited as `onyx Dn`.
- `jet` rows are cited as `jet Jn`.
- `OPEN` decisions are stated as open, with the current direction and the consequence for the architecture. No `TBD` or placeholder language is used.

## Diagram conventions

- Block diagrams show data flow and module ownership; they are not cycle-accurate timing diagrams.
- Mermaid source is inlined in the chapter and also stored under `assets/mermaid/`; the trailing source line in each chapter gives the asset path.

## Voice

This specification uses first-person-plural engineering voice: "amber does X because Y." Every architectural claim is traceable to a PRD row, an F-item, a GLOBAL_REQUIREMENTS rule, or a real RTL port list.
