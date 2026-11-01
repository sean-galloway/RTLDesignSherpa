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

# Programmer-Visible Machine State

## General-Purpose Registers

This section will describe the x0-x31 register file, including the hard-wired zero behavior of x0.

## Program Counter

This section will describe the PC behavior: reset address, sequential increment, branch/jump targets, and freeze on halt.

## Memory Model

This section will summarize the byte-addressable, little-endian memory space, the Harvard instruction/data ports, and the naturally aligned access requirement.

## Halt State

This section will describe the `halt` output and `halt_cause` encoding visible to the system layer.

---

**Last Updated:** 2026-11-01
