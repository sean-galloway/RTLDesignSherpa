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

# AXI4 Slave and APB CSR

Both interfaces are **INHERITED** from pumice without functional change. This
chapter records what that inheritance includes, so that "inherited" is not
mistaken for "unspecified".

## AXI4 slave

The host-side interface is pumice's `axi4_ifc`: one read intake and one write
intake at 1:1, a write-data CAM, a read-reorder CAM, in-order commit, and
FSM-free split and aggregate where the aggregate and last flags ride with the
command in the CAM.

Nothing about DDR3 or LPDDR3 reaches the host side. The DRAM generation is
invisible across this boundary, which is the property that makes the family
worth having.

**Width gearing is inherited too.** The host bus width need not match the DRAM
burst width: formally-verified dwidth converters wrap the core, so the host side
is free. This is why `scoria_top_geared` exists as a separate top alongside
`scoria_top`.

## APB CSR

A PeakRDL-generated register block behind an APB slave. The register *set* grows
(Chapter 5), but the interface and the generation flow do not change.

**Important — the regeneration rule applies unchanged.** The register block is
generated through `bin/peakrdl_generate.py`, never raw `peakrdl`, and always with
an explicit `-o`. The wrapper emits the RTL, the documentation and the Python
regmap together; raw peakrdl skips the latter two and the default output path can
write an orphan copy the build never reads, which then drifts.

**Important — registers are accessed by NAME.** Host code reads and writes
through the generated regmap, never by hardcoded offset. Offsets churn whenever
the RDL changes, and a host that hardcodes them fails silently by hitting a
neighbouring register that happens to decode.

## The CDC on the CSR path, and why it is an async FIFO

If scoria is integrated the way pumice is on its board — an APB window on one
reset domain reaching a core on another — then the CDC between them must be a
gray-pointer async FIFO, not a toggle-parity handshake.

The reason is an asymmetric reset, and it is worth carrying forward because it
cost real debugging on pumice: the APB side runs on `presetn` and the core side
on `aresetn`, and a soft reset pulses **only the core side**. A toggle-parity
handshake desynchronises across that and leaves the response stream permanently
offset by one transaction — every readback returns the answer to the previous
question, which looks like a lagging register file rather than a CDC fault.

This is a note about integration rather than about scoria's own ports, but it
belongs here because the next person to simplify that CDC will be reading this
chapter.
