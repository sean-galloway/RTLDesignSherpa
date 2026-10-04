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

# AXI4 Slave and APB CSR (both inherited)

## The host side is unchanged in shape

Everything on the host side of the controller transfers from scoria without
structural change: the AXI4 slave, the width-gearing converters that let the
host bus width differ from the DRAM's (x8 DDR4, x16-per-channel LPDDR4 at
this design point), the APB slave into the register block, and the
in-order commit discipline. Nothing about DDR4 or LPDDR4 reaches this side
of the controller, and the front-end blocks that serve it are the green set
of Figure 2.1.

The AXI4 shape is inherited as a *shape*, not just a protocol: the same ID
handling, the same burst chopping against the DRAM's page, the same
read-reorder and write-data CAMs. scoria's book is the specification for
those blocks and andesite's MAS references it rather than rewriting it.

## The register block

The CSR block regenerates from an `andesite_csr.rdl` through the same
PeakRDL flow scoria uses. Two rules carry, both load-bearing:

1. **Registers are named, not offset-numbered, in books.** Offsets live in
   the generated documentation, not in prose; a register's name is its
   handle everywhere in this book, the MAS, and the kmap book. The house
   peakrdl wrapper generates the offset map when the RDL lands.
2. **The generation flow is inherited; the contents grow.** Every new timing
   (the long/short pairs, the ODT latencies, the FGR factor), every new
   policy select (placement, elastic refresh carried forward, DBI enables),
   and the training interfaces' telemetry join the register map. Chapter 5
   owns the inventory; the growth is content, not mechanism.

## The seam with the rest of the book

The host side's only contacts with this book's deltas are telemetry (the
training and ODT instruments are host-visible, per the four-state rule of
Chapter 3.3) and the width gearing's view of the LPDDR4 channel width. Both
are CSR-visible; neither is structural.
